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
/- Source: ProjectionCertificates/R_m14e10q0_0009.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q0_0009

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [295, 555, 331, 213, 677, 325, 713, 794, 802, 348, 436, 600, 752, 816, 11, 35, 259, 37, 69, 133, 261, 73, 521, 545, 193, 321, 641, 266, 522, 290, 546, 770, 84, 148, 276, 164, 292, 324, 88, 280, 536, 328, 584, 176, 304, 560, 208, 592, 784, 672, 800, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_295, vertices_555, vertices_331, vertices_213, vertices_677, vertices_325, vertices_713, vertices_794, vertices_802, vertices_348, vertices_436, vertices_600, vertices_752, vertices_816] (by decide +kernel)
  polygons := literalFinset [vertices_11, vertices_35, vertices_259, vertices_37, vertices_69, vertices_133, vertices_261, vertices_73, vertices_521, vertices_545, vertices_193, vertices_321, vertices_641, vertices_266, vertices_522, vertices_290, vertices_546, vertices_770, vertices_84, vertices_148, vertices_276, vertices_164, vertices_292, vertices_324, vertices_88, vertices_280, vertices_536, vertices_328, vertices_584, vertices_176, vertices_304, vertices_560, vertices_208, vertices_592, vertices_784, vertices_672, vertices_800, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_295), (false, vertices_555), (false, vertices_331), (false, vertices_213), (false, vertices_677), (false, vertices_325), (false, vertices_713), (true, vertices_770), (true, vertices_276), (true, vertices_88), (true, vertices_280), (true, vertices_536), (true, vertices_176), (true, vertices_304), (true, vertices_560), (true, vertices_592), (true, vertices_784), (true, vertices_800)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 12 16 19 21 22 23 24 25 26
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_295) then 13 else
  if p.val = (false, vertices_555) then 14 else
  if p.val = (false, vertices_331) then 15 else
  if p.val = (false, vertices_213) then 17 else
  if p.val = (false, vertices_677) then 18 else
  if p.val = (false, vertices_325) then 0 else
  if p.val = (false, vertices_713) then 20 else
  if p.val = (true, vertices_770) then 1 else
  if p.val = (true, vertices_276) then 2 else
  if p.val = (true, vertices_88) then 3 else
  if p.val = (true, vertices_280) then 4 else
  if p.val = (true, vertices_536) then 5 else
  if p.val = (true, vertices_176) then 6 else
  if p.val = (true, vertices_304) then 7 else
  if p.val = (true, vertices_560) then 8 else
  if p.val = (true, vertices_592) then 9 else
  if p.val = (true, vertices_784) then 10 else
  if p.val = (true, vertices_800) then 11 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_325), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_770), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_276), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_88), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_280), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_536), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_176), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_304), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_560), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_592), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_784), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_800), by decide +kernel⟩
  | 12 => Sum.inl 0
  | 13 => Sum.inr ⟨(false, vertices_295), by decide +kernel⟩
  | 14 => Sum.inr ⟨(false, vertices_555), by decide +kernel⟩
  | 15 => Sum.inr ⟨(false, vertices_331), by decide +kernel⟩
  | 16 => Sum.inl 1
  | 17 => Sum.inr ⟨(false, vertices_213), by decide +kernel⟩
  | 18 => Sum.inr ⟨(false, vertices_677), by decide +kernel⟩
  | 19 => Sum.inl 2
  | 20 => Sum.inr ⟨(false, vertices_713), by decide +kernel⟩
  | 21 => Sum.inl 3
  | 22 => Sum.inl 4
  | 23 => Sum.inl 5
  | 24 => Sum.inl 6
  | 25 => Sum.inl 7
  | 26 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 2 3 7 8 794 266 2
cert_row_4 1 1 2 3 5 7 348 84 1
cert_row_4 2 1 3 4 6 7 436 148 2
cert_row_4 3 3 4 5 6 8 752 176 2
cert_rows
cert_pivot_2 0 2 1 3
cert_heightProof 4
cert_coverFacet 0 794
cert_cover_5 0 0 0 2 3 7 266 794 2
cert_coverFacet 1 802
cert_cover_2 1 4 0 7 8 290 802 3
cert_coverFacet 2 348
cert_cover_5 2 1 1 2 3 5 84 348 1
cert_coverFacet 3 436
cert_cover_5 3 2 1 3 4 6 148 436 2
cert_coverFacet 4 600
cert_cover_2 4 3 2 5 8 88 600 3
cert_coverFacet 5 752
cert_cover_5 5 3 3 4 5 6 176 752 2
cert_coverFacet 6 816
cert_cover_2 6 4 3 7 8 304 816 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q0_0009

end
end BundlePart0

section BundlePart1
/- Source: ProjectionCertificates/R_m14e10q0_0011.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q0_0011

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [307, 659, 611, 709, 409, 481, 558, 282, 538, 298, 668, 300, 460, 868, 19, 35, 515, 145, 273, 97, 289, 193, 577, 385, 641, 26, 42, 266, 522, 274, 530, 290, 546, 44, 140, 268, 524, 292, 548, 196, 324, 580, 644, 152, 280, 536, 296, 392, 656, 352, 608, 448]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_307, vertices_659, vertices_611, vertices_709, vertices_409, vertices_481, vertices_558, vertices_282, vertices_538, vertices_298, vertices_668, vertices_300, vertices_460, vertices_868] (by decide +kernel)
  polygons := literalFinset [vertices_19, vertices_35, vertices_515, vertices_145, vertices_273, vertices_97, vertices_289, vertices_193, vertices_577, vertices_385, vertices_641, vertices_26, vertices_42, vertices_266, vertices_522, vertices_274, vertices_530, vertices_290, vertices_546, vertices_44, vertices_140, vertices_268, vertices_524, vertices_292, vertices_548, vertices_196, vertices_324, vertices_580, vertices_644, vertices_152, vertices_280, vertices_536, vertices_296, vertices_392, vertices_656, vertices_352, vertices_608, vertices_448] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_307), (false, vertices_659), (false, vertices_611), (false, vertices_709), (false, vertices_409), (false, vertices_481), (true, vertices_26), (true, vertices_42), (true, vertices_266), (true, vertices_522), (true, vertices_44), (true, vertices_140), (true, vertices_268), (true, vertices_524), (true, vertices_292), (true, vertices_548), (true, vertices_324), (true, vertices_536), (true, vertices_296)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 13 17 19 21 22 24 25 26 27
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_307) then 14 else
  if p.val = (false, vertices_659) then 15 else
  if p.val = (false, vertices_611) then 16 else
  if p.val = (false, vertices_709) then 18 else
  if p.val = (false, vertices_409) then 20 else
  if p.val = (false, vertices_481) then 23 else
  if p.val = (true, vertices_26) then 0 else
  if p.val = (true, vertices_42) then 1 else
  if p.val = (true, vertices_266) then 2 else
  if p.val = (true, vertices_522) then 3 else
  if p.val = (true, vertices_44) then 4 else
  if p.val = (true, vertices_140) then 5 else
  if p.val = (true, vertices_268) then 6 else
  if p.val = (true, vertices_524) then 7 else
  if p.val = (true, vertices_292) then 8 else
  if p.val = (true, vertices_548) then 9 else
  if p.val = (true, vertices_324) then 10 else
  if p.val = (true, vertices_536) then 11 else
  if p.val = (true, vertices_296) then 12 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_26), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_42), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_266), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_522), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_44), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_140), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_268), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_524), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_292), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_548), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_324), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_536), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_296), by decide +kernel⟩
  | 13 => Sum.inl 0
  | 14 => Sum.inr ⟨(false, vertices_307), by decide +kernel⟩
  | 15 => Sum.inr ⟨(false, vertices_659), by decide +kernel⟩
  | 16 => Sum.inr ⟨(false, vertices_611), by decide +kernel⟩
  | 17 => Sum.inl 1
  | 18 => Sum.inr ⟨(false, vertices_709), by decide +kernel⟩
  | 19 => Sum.inl 2
  | 20 => Sum.inr ⟨(false, vertices_409), by decide +kernel⟩
  | 21 => Sum.inl 3
  | 22 => Sum.inl 4
  | 23 => Sum.inr ⟨(false, vertices_481), by decide +kernel⟩
  | 24 => Sum.inl 5
  | 25 => Sum.inl 6
  | 26 => Sum.inl 7
  | 27 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 2 4 8 558 42 1
cert_row_4 1 1 2 3 6 8 668 140 2
cert_row_4 2 1 2 5 6 7 460 140 2
cert_row_4 3 1 4 5 7 8 868 292 2
cert_rows
cert_pivot_2 0 3 2 1
cert_heightProof 4
cert_coverFacet 0 558
cert_cover_5 0 0 0 1 2 4 42 558 1
cert_coverFacet 1 282
cert_cover_2 1 2 0 3 7 26 282 3
cert_coverFacet 2 538
cert_cover_2 2 2 0 3 8 26 538 3
cert_coverFacet 3 298
cert_cover_2 3 2 0 4 7 42 298 3
cert_coverFacet 4 668
cert_cover_5 4 1 1 2 3 6 140 668 2
cert_coverFacet 5 300
cert_cover_2 5 2 1 4 7 44 300 3
cert_coverFacet 6 460
cert_cover_5 6 2 1 2 5 6 140 460 2
cert_coverFacet 7 868
cert_cover_5 7 3 1 4 5 7 292 868 2
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q0_0011

end
end BundlePart1

section BundlePart2
/- Source: ProjectionCertificates/R_m14e10q0_0012.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q0_0012

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [675, 93, 653, 613, 185, 369, 782, 410, 650, 866, 418, 284, 852, 432, 13, 69, 517, 25, 137, 49, 81, 97, 161, 545, 641, 138, 266, 522, 162, 290, 546, 386, 642, 770, 28, 268, 524, 84, 276, 580, 772, 152, 280, 648, 176, 304, 336, 400, 352, 608, 416, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_675, vertices_93, vertices_653, vertices_613, vertices_185, vertices_369, vertices_782, vertices_410, vertices_650, vertices_866, vertices_418, vertices_284, vertices_852, vertices_432] (by decide +kernel)
  polygons := literalFinset [vertices_13, vertices_69, vertices_517, vertices_25, vertices_137, vertices_49, vertices_81, vertices_97, vertices_161, vertices_545, vertices_641, vertices_138, vertices_266, vertices_522, vertices_162, vertices_290, vertices_546, vertices_386, vertices_642, vertices_770, vertices_28, vertices_268, vertices_524, vertices_84, vertices_276, vertices_580, vertices_772, vertices_152, vertices_280, vertices_648, vertices_176, vertices_304, vertices_336, vertices_400, vertices_352, vertices_608, vertices_416, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_675), (false, vertices_93), (false, vertices_653), (false, vertices_613), (false, vertices_185), (false, vertices_369), (true, vertices_138), (true, vertices_266), (true, vertices_522), (true, vertices_290), (true, vertices_386), (true, vertices_770), (true, vertices_268), (true, vertices_276), (true, vertices_772), (true, vertices_280), (true, vertices_400), (true, vertices_416), (true, vertices_832)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 13 15 19 21 23 24 25 26 27
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_675) then 14 else
  if p.val = (false, vertices_93) then 16 else
  if p.val = (false, vertices_653) then 17 else
  if p.val = (false, vertices_613) then 18 else
  if p.val = (false, vertices_185) then 20 else
  if p.val = (false, vertices_369) then 22 else
  if p.val = (true, vertices_138) then 0 else
  if p.val = (true, vertices_266) then 1 else
  if p.val = (true, vertices_522) then 2 else
  if p.val = (true, vertices_290) then 3 else
  if p.val = (true, vertices_386) then 4 else
  if p.val = (true, vertices_770) then 5 else
  if p.val = (true, vertices_268) then 6 else
  if p.val = (true, vertices_276) then 7 else
  if p.val = (true, vertices_772) then 8 else
  if p.val = (true, vertices_280) then 9 else
  if p.val = (true, vertices_400) then 10 else
  if p.val = (true, vertices_416) then 11 else
  if p.val = (true, vertices_832) then 12 else
  0
cert_priority
cert_nodeAtPriority_11 138 266 522 290 386 770 268 276 772 280 400 416 832 675 93 653 613 185 369
cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 2 3 6 7 410 138 2
cert_row_4 1 0 1 2 7 8 782 266 1
cert_row_4 2 0 4 5 7 8 866 290 2
cert_row_4 3 1 3 5 7 8 852 84 3
cert_rows
cert_pivot_2 6 2 0 1
cert_heightProof 4
cert_coverFacet 0 782
cert_cover_5 0 1 0 1 2 7 266 782 1
cert_coverFacet 1 410
cert_cover_5 1 0 0 2 3 6 138 410 2
cert_coverFacet 2 650
cert_cover_2 2 2 0 6 8 138 650 3
cert_coverFacet 3 866
cert_cover_5 3 2 0 4 5 7 290 866 2
cert_coverFacet 4 418
cert_cover_2 4 4 0 6 7 162 418 3
cert_coverFacet 5 284
cert_cover_2 5 2 1 3 7 28 284 3
cert_coverFacet 6 852
cert_cover_5 6 3 1 3 5 7 84 852 3
cert_coverFacet 7 432
cert_cover_2 7 4 3 6 7 176 432 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q0_0012

end
end BundlePart2

section BundlePart3
/- Source: ProjectionCertificates/R_m14e10q0_0013.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q0_0013

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [563, 403, 355, 453, 665, 737, 558, 282, 538, 298, 412, 300, 716, 868, 19, 35, 259, 145, 529, 97, 545, 193, 321, 385, 641, 26, 42, 266, 522, 274, 530, 290, 546, 44, 140, 268, 524, 292, 548, 196, 324, 580, 388, 152, 280, 536, 296, 648, 400, 352, 608, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_563, vertices_403, vertices_355, vertices_453, vertices_665, vertices_737, vertices_558, vertices_282, vertices_538, vertices_298, vertices_412, vertices_300, vertices_716, vertices_868] (by decide +kernel)
  polygons := literalFinset [vertices_19, vertices_35, vertices_259, vertices_145, vertices_529, vertices_97, vertices_545, vertices_193, vertices_321, vertices_385, vertices_641, vertices_26, vertices_42, vertices_266, vertices_522, vertices_274, vertices_530, vertices_290, vertices_546, vertices_44, vertices_140, vertices_268, vertices_524, vertices_292, vertices_548, vertices_196, vertices_324, vertices_580, vertices_388, vertices_152, vertices_280, vertices_536, vertices_296, vertices_648, vertices_400, vertices_352, vertices_608, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_563), (false, vertices_403), (false, vertices_355), (false, vertices_453), (false, vertices_665), (false, vertices_737), (true, vertices_26), (true, vertices_42), (true, vertices_266), (true, vertices_522), (true, vertices_44), (true, vertices_140), (true, vertices_268), (true, vertices_524), (true, vertices_292), (true, vertices_548), (true, vertices_580), (true, vertices_280), (true, vertices_296)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 13 17 19 21 22 24 25 26 27
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_563) then 14 else
  if p.val = (false, vertices_403) then 15 else
  if p.val = (false, vertices_355) then 16 else
  if p.val = (false, vertices_453) then 18 else
  if p.val = (false, vertices_665) then 20 else
  if p.val = (false, vertices_737) then 23 else
  if p.val = (true, vertices_26) then 0 else
  if p.val = (true, vertices_42) then 1 else
  if p.val = (true, vertices_266) then 2 else
  if p.val = (true, vertices_522) then 3 else
  if p.val = (true, vertices_44) then 4 else
  if p.val = (true, vertices_140) then 5 else
  if p.val = (true, vertices_268) then 6 else
  if p.val = (true, vertices_524) then 7 else
  if p.val = (true, vertices_292) then 8 else
  if p.val = (true, vertices_548) then 9 else
  if p.val = (true, vertices_580) then 10 else
  if p.val = (true, vertices_280) then 11 else
  if p.val = (true, vertices_296) then 12 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_26), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_42), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_266), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_522), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_44), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_140), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_268), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_524), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_292), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_548), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_580), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_280), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_296), by decide +kernel⟩
  | 13 => Sum.inl 0
  | 14 => Sum.inr ⟨(false, vertices_563), by decide +kernel⟩
  | 15 => Sum.inr ⟨(false, vertices_403), by decide +kernel⟩
  | 16 => Sum.inr ⟨(false, vertices_355), by decide +kernel⟩
  | 17 => Sum.inl 1
  | 18 => Sum.inr ⟨(false, vertices_453), by decide +kernel⟩
  | 19 => Sum.inl 2
  | 20 => Sum.inr ⟨(false, vertices_665), by decide +kernel⟩
  | 21 => Sum.inl 3
  | 22 => Sum.inl 4
  | 23 => Sum.inr ⟨(false, vertices_737), by decide +kernel⟩
  | 24 => Sum.inl 5
  | 25 => Sum.inl 6
  | 26 => Sum.inl 7
  | 27 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 2 4 8 558 42 1
cert_row_4 1 1 2 3 6 7 412 140 2
cert_row_4 2 1 2 5 6 8 716 140 2
cert_row_4 3 1 4 5 7 8 868 292 2
cert_rows
cert_pivot_2 0 3 2 1
cert_heightProof 4
cert_coverFacet 0 558
cert_cover_5 0 0 0 1 2 4 42 558 1
cert_coverFacet 1 282
cert_cover_2 1 2 0 3 7 26 282 3
cert_coverFacet 2 538
cert_cover_2 2 2 0 3 8 26 538 3
cert_coverFacet 3 298
cert_cover_2 3 2 0 4 7 42 298 3
cert_coverFacet 4 412
cert_cover_5 4 1 1 2 3 6 140 412 2
cert_coverFacet 5 300
cert_cover_2 5 2 1 4 7 44 300 3
cert_coverFacet 6 716
cert_cover_5 6 2 1 2 5 6 140 716 2
cert_coverFacet 7 868
cert_cover_5 7 3 1 4 5 7 292 868 2
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q0_0013

end
end BundlePart3

section BundlePart4
/- Source: ProjectionCertificates/R_m14e10q0_0023.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q0_0023

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [55, 91, 803, 451, 157, 421, 201, 562, 850, 572, 716, 676, 600, 992, 19, 35, 67, 259, 21, 37, 133, 25, 73, 137, 289, 193, 385, 50, 82, 530, 546, 322, 770, 28, 140, 524, 52, 164, 548, 644, 88, 536, 200, 584, 560, 592, 416, 672, 800, 448, 704, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_55, vertices_91, vertices_803, vertices_451, vertices_157, vertices_421, vertices_201, vertices_562, vertices_850, vertices_572, vertices_716, vertices_676, vertices_600, vertices_992] (by decide +kernel)
  polygons := literalFinset [vertices_19, vertices_35, vertices_67, vertices_259, vertices_21, vertices_37, vertices_133, vertices_25, vertices_73, vertices_137, vertices_289, vertices_193, vertices_385, vertices_50, vertices_82, vertices_530, vertices_546, vertices_322, vertices_770, vertices_28, vertices_140, vertices_524, vertices_52, vertices_164, vertices_548, vertices_644, vertices_88, vertices_536, vertices_200, vertices_584, vertices_560, vertices_592, vertices_416, vertices_672, vertices_800, vertices_448, vertices_704, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_55), (false, vertices_91), (false, vertices_803), (false, vertices_451), (false, vertices_157), (false, vertices_421), (false, vertices_201), (true, vertices_530), (true, vertices_524), (true, vertices_548), (true, vertices_644), (true, vertices_536), (true, vertices_584), (true, vertices_560), (true, vertices_592), (true, vertices_672), (true, vertices_704), (true, vertices_832)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 16 12 20 21 22 23 24 25 26
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_55) then 13 else
  if p.val = (false, vertices_91) then 17 else
  if p.val = (false, vertices_803) then 18 else
  if p.val = (false, vertices_451) then 19 else
  if p.val = (false, vertices_157) then 14 else
  if p.val = (false, vertices_421) then 15 else
  if p.val = (false, vertices_201) then 0 else
  if p.val = (true, vertices_530) then 1 else
  if p.val = (true, vertices_524) then 2 else
  if p.val = (true, vertices_548) then 3 else
  if p.val = (true, vertices_644) then 4 else
  if p.val = (true, vertices_536) then 5 else
  if p.val = (true, vertices_584) then 6 else
  if p.val = (true, vertices_560) then 7 else
  if p.val = (true, vertices_592) then 8 else
  if p.val = (true, vertices_672) then 9 else
  if p.val = (true, vertices_704) then 10 else
  if p.val = (true, vertices_832) then 11 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_201), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_530), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_524), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_548), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_644), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_536), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_584), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_560), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_592), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_672), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_704), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_832), by decide +kernel⟩
  | 12 => Sum.inl 1
  | 13 => Sum.inr ⟨(false, vertices_55), by decide +kernel⟩
  | 14 => Sum.inr ⟨(false, vertices_157), by decide +kernel⟩
  | 15 => Sum.inr ⟨(false, vertices_421), by decide +kernel⟩
  | 16 => Sum.inl 0
  | 17 => Sum.inr ⟨(false, vertices_91), by decide +kernel⟩
  | 18 => Sum.inr ⟨(false, vertices_803), by decide +kernel⟩
  | 19 => Sum.inr ⟨(false, vertices_451), by decide +kernel⟩
  | 20 => Sum.inl 2
  | 21 => Sum.inl 3
  | 22 => Sum.inl 4
  | 23 => Sum.inl 5
  | 24 => Sum.inl 6
  | 25 => Sum.inl 7
  | 26 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 3 5 7 8 850 82 3
cert_row_4 1 1 2 3 4 8 572 28 3
cert_row_4 2 1 2 5 6 8 716 140 2
cert_row_4 3 4 5 6 7 8 992 416 1
cert_rows
cert_pivot_2 0 3 1 4
cert_heightProof 4
cert_coverFacet 0 562
cert_cover_2 0 3 0 4 8 50 562 3
cert_coverFacet 1 850
cert_cover_5 1 0 0 3 5 7 82 850 3
cert_coverFacet 2 572
cert_cover_5 2 1 1 2 3 4 28 572 3
cert_coverFacet 3 716
cert_cover_5 3 2 1 2 5 6 140 716 2
cert_coverFacet 4 676
cert_cover_2 4 4 1 6 8 164 676 3
cert_coverFacet 5 600
cert_cover_2 5 3 2 5 8 88 600 3
cert_coverFacet 6 992
cert_cover_5 6 3 4 5 6 7 416 992 1
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q0_0023

end
end BundlePart4

section BundlePart5
/- Source: ProjectionCertificates/R_m14e10q0_0024.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q0_0024

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [55, 91, 803, 451, 157, 421, 201, 562, 850, 604, 684, 564, 712, 992, 19, 35, 67, 259, 21, 37, 133, 25, 73, 137, 289, 193, 385, 50, 82, 530, 546, 322, 770, 28, 140, 524, 52, 532, 164, 548, 88, 200, 584, 648, 560, 592, 416, 672, 800, 448, 704, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_55, vertices_91, vertices_803, vertices_451, vertices_157, vertices_421, vertices_201, vertices_562, vertices_850, vertices_604, vertices_684, vertices_564, vertices_712, vertices_992] (by decide +kernel)
  polygons := literalFinset [vertices_19, vertices_35, vertices_67, vertices_259, vertices_21, vertices_37, vertices_133, vertices_25, vertices_73, vertices_137, vertices_289, vertices_193, vertices_385, vertices_50, vertices_82, vertices_530, vertices_546, vertices_322, vertices_770, vertices_28, vertices_140, vertices_524, vertices_52, vertices_532, vertices_164, vertices_548, vertices_88, vertices_200, vertices_584, vertices_648, vertices_560, vertices_592, vertices_416, vertices_672, vertices_800, vertices_448, vertices_704, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_55), (false, vertices_91), (false, vertices_803), (false, vertices_451), (false, vertices_157), (false, vertices_421), (false, vertices_201), (true, vertices_530), (true, vertices_524), (true, vertices_532), (true, vertices_548), (true, vertices_584), (true, vertices_648), (true, vertices_560), (true, vertices_592), (true, vertices_672), (true, vertices_704), (true, vertices_832)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 16 12 20 21 22 23 24 25 26
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_55) then 13 else
  if p.val = (false, vertices_91) then 17 else
  if p.val = (false, vertices_803) then 18 else
  if p.val = (false, vertices_451) then 19 else
  if p.val = (false, vertices_157) then 14 else
  if p.val = (false, vertices_421) then 15 else
  if p.val = (false, vertices_201) then 0 else
  if p.val = (true, vertices_530) then 1 else
  if p.val = (true, vertices_524) then 2 else
  if p.val = (true, vertices_532) then 3 else
  if p.val = (true, vertices_548) then 4 else
  if p.val = (true, vertices_584) then 5 else
  if p.val = (true, vertices_648) then 6 else
  if p.val = (true, vertices_560) then 7 else
  if p.val = (true, vertices_592) then 8 else
  if p.val = (true, vertices_672) then 9 else
  if p.val = (true, vertices_704) then 10 else
  if p.val = (true, vertices_832) then 11 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_201), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_530), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_524), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_532), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_548), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_584), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_648), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_560), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_592), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_672), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_704), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_832), by decide +kernel⟩
  | 12 => Sum.inl 1
  | 13 => Sum.inr ⟨(false, vertices_55), by decide +kernel⟩
  | 14 => Sum.inr ⟨(false, vertices_157), by decide +kernel⟩
  | 15 => Sum.inr ⟨(false, vertices_421), by decide +kernel⟩
  | 16 => Sum.inl 0
  | 17 => Sum.inr ⟨(false, vertices_91), by decide +kernel⟩
  | 18 => Sum.inr ⟨(false, vertices_803), by decide +kernel⟩
  | 19 => Sum.inr ⟨(false, vertices_451), by decide +kernel⟩
  | 20 => Sum.inl 2
  | 21 => Sum.inl 3
  | 22 => Sum.inl 4
  | 23 => Sum.inl 5
  | 24 => Sum.inl 6
  | 25 => Sum.inl 7
  | 26 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 3 5 7 8 850 82 3
cert_row_4 1 1 2 3 5 8 604 28 3
cert_row_4 2 1 2 4 6 8 684 140 2
cert_row_4 3 4 5 6 7 8 992 416 1
cert_rows
cert_pivot_2 0 3 1 4
cert_heightProof 4
cert_coverFacet 0 562
cert_cover_2 0 3 0 4 8 50 562 3
cert_coverFacet 1 850
cert_cover_5 1 0 0 3 5 7 82 850 3
cert_coverFacet 2 604
cert_cover_5 2 1 1 2 3 5 28 604 3
cert_coverFacet 3 684
cert_cover_5 3 2 1 2 4 6 140 684 2
cert_coverFacet 4 564
cert_cover_2 4 3 1 4 8 52 564 3
cert_coverFacet 5 712
cert_cover_2 5 5 2 6 8 200 712 3
cert_coverFacet 6 992
cert_cover_5 6 3 4 5 6 7 416 992 1
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q0_0024

end
end BundlePart5

section BundlePart6
/- Source: ProjectionCertificates/R_m14e10q0_0029.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q0_0029

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [327, 91, 299, 117, 805, 185, 202, 394, 962, 220, 692, 708, 836, 936, 11, 67, 259, 37, 69, 261, 25, 41, 49, 81, 289, 74, 138, 266, 194, 322, 386, 52, 84, 148, 548, 196, 324, 580, 644, 772, 88, 152, 168, 296, 200, 392, 176, 672, 800, 704, 832, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_327, vertices_91, vertices_299, vertices_117, vertices_805, vertices_185, vertices_202, vertices_394, vertices_962, vertices_220, vertices_692, vertices_708, vertices_836, vertices_936] (by decide +kernel)
  polygons := literalFinset [vertices_11, vertices_67, vertices_259, vertices_37, vertices_69, vertices_261, vertices_25, vertices_41, vertices_49, vertices_81, vertices_289, vertices_74, vertices_138, vertices_266, vertices_194, vertices_322, vertices_386, vertices_52, vertices_84, vertices_148, vertices_548, vertices_196, vertices_324, vertices_580, vertices_644, vertices_772, vertices_88, vertices_152, vertices_168, vertices_296, vertices_200, vertices_392, vertices_176, vertices_672, vertices_800, vertices_704, vertices_832, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_327), (false, vertices_91), (false, vertices_299), (false, vertices_117), (false, vertices_805), (false, vertices_185), (true, vertices_138), (true, vertices_194), (true, vertices_386), (true, vertices_148), (true, vertices_196), (true, vertices_580), (true, vertices_644), (true, vertices_200), (true, vertices_392), (true, vertices_672), (true, vertices_704), (true, vertices_832), (true, vertices_896)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 13 17 20 22 23 24 25 26 27
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_327) then 14 else
  if p.val = (false, vertices_91) then 15 else
  if p.val = (false, vertices_299) then 16 else
  if p.val = (false, vertices_117) then 18 else
  if p.val = (false, vertices_805) then 19 else
  if p.val = (false, vertices_185) then 21 else
  if p.val = (true, vertices_138) then 0 else
  if p.val = (true, vertices_194) then 1 else
  if p.val = (true, vertices_386) then 2 else
  if p.val = (true, vertices_148) then 3 else
  if p.val = (true, vertices_196) then 4 else
  if p.val = (true, vertices_580) then 5 else
  if p.val = (true, vertices_644) then 6 else
  if p.val = (true, vertices_200) then 7 else
  if p.val = (true, vertices_392) then 8 else
  if p.val = (true, vertices_672) then 9 else
  if p.val = (true, vertices_704) then 10 else
  if p.val = (true, vertices_832) then 11 else
  if p.val = (true, vertices_896) then 12 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_138), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_194), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_386), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_148), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_196), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_580), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_644), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_200), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_392), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_672), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_704), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_832), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_896), by decide +kernel⟩
  | 13 => Sum.inl 0
  | 14 => Sum.inr ⟨(false, vertices_327), by decide +kernel⟩
  | 15 => Sum.inr ⟨(false, vertices_91), by decide +kernel⟩
  | 16 => Sum.inr ⟨(false, vertices_299), by decide +kernel⟩
  | 17 => Sum.inl 1
  | 18 => Sum.inr ⟨(false, vertices_117), by decide +kernel⟩
  | 19 => Sum.inr ⟨(false, vertices_805), by decide +kernel⟩
  | 20 => Sum.inl 2
  | 21 => Sum.inr ⟨(false, vertices_185), by decide +kernel⟩
  | 22 => Sum.inl 3
  | 23 => Sum.inl 4
  | 24 => Sum.inl 5
  | 25 => Sum.inl 6
  | 26 => Sum.inl 7
  | 27 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 5 6 7 8 962 194 3
cert_row_4 1 1 2 3 5 6 220 84 1
cert_row_4 2 1 3 4 6 8 692 52 3
cert_row_4 3 2 4 6 7 8 936 168 3
cert_rows
cert_pivot_2 0 5 1 2
cert_heightProof 4
cert_coverFacet 0 202
cert_cover_2 0 2 0 5 6 74 202 3
cert_coverFacet 1 394
cert_cover_2 1 2 0 6 7 138 394 3
cert_coverFacet 2 962
cert_cover_5 2 0 0 5 6 7 194 962 3
cert_coverFacet 3 220
cert_cover_5 3 1 1 2 3 5 84 220 1
cert_coverFacet 4 692
cert_cover_5 4 2 1 3 4 6 52 692 3
cert_coverFacet 5 708
cert_cover_2 5 5 1 6 8 196 708 3
cert_coverFacet 6 836
cert_cover_2 6 5 1 7 8 324 836 3
cert_coverFacet 7 936
cert_cover_5 7 3 2 4 6 7 168 936 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q0_0029

end
end BundlePart6

section BundlePart7
/- Source: ProjectionCertificates/R_m14e10q0_0032.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q0_0032

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [331, 651, 595, 181, 425, 369, 657, 782, 866, 668, 396, 628, 420, 804, 11, 67, 515, 137, 265, 49, 81, 145, 529, 161, 289, 321, 641, 266, 522, 322, 578, 770, 140, 268, 524, 52, 148, 532, 164, 292, 548, 388, 772, 392, 648, 112, 592, 656, 352, 608, 416, 800]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_331, vertices_651, vertices_595, vertices_181, vertices_425, vertices_369, vertices_657, vertices_782, vertices_866, vertices_668, vertices_396, vertices_628, vertices_420, vertices_804] (by decide +kernel)
  polygons := literalFinset [vertices_11, vertices_67, vertices_515, vertices_137, vertices_265, vertices_49, vertices_81, vertices_145, vertices_529, vertices_161, vertices_289, vertices_321, vertices_641, vertices_266, vertices_522, vertices_322, vertices_578, vertices_770, vertices_140, vertices_268, vertices_524, vertices_52, vertices_148, vertices_532, vertices_164, vertices_292, vertices_548, vertices_388, vertices_772, vertices_392, vertices_648, vertices_112, vertices_592, vertices_656, vertices_352, vertices_608, vertices_416, vertices_800] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_331), (false, vertices_651), (false, vertices_595), (false, vertices_181), (false, vertices_425), (false, vertices_369), (false, vertices_657), (true, vertices_770), (true, vertices_140), (true, vertices_268), (true, vertices_524), (true, vertices_532), (true, vertices_292), (true, vertices_548), (true, vertices_388), (true, vertices_772), (true, vertices_608), (true, vertices_800)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 12 16 18 20 22 23 24 25 26
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_331) then 13 else
  if p.val = (false, vertices_651) then 14 else
  if p.val = (false, vertices_595) then 15 else
  if p.val = (false, vertices_181) then 17 else
  if p.val = (false, vertices_425) then 19 else
  if p.val = (false, vertices_369) then 21 else
  if p.val = (false, vertices_657) then 0 else
  if p.val = (true, vertices_770) then 1 else
  if p.val = (true, vertices_140) then 2 else
  if p.val = (true, vertices_268) then 3 else
  if p.val = (true, vertices_524) then 4 else
  if p.val = (true, vertices_532) then 5 else
  if p.val = (true, vertices_292) then 6 else
  if p.val = (true, vertices_548) then 7 else
  if p.val = (true, vertices_388) then 8 else
  if p.val = (true, vertices_772) then 9 else
  if p.val = (true, vertices_608) then 10 else
  if p.val = (true, vertices_800) then 11 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_657), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_770), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_140), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_268), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_524), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_532), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_292), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_548), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_388), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_772), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_608), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_800), by decide +kernel⟩
  | 12 => Sum.inl 0
  | 13 => Sum.inr ⟨(false, vertices_331), by decide +kernel⟩
  | 14 => Sum.inr ⟨(false, vertices_651), by decide +kernel⟩
  | 15 => Sum.inr ⟨(false, vertices_595), by decide +kernel⟩
  | 16 => Sum.inl 1
  | 17 => Sum.inr ⟨(false, vertices_181), by decide +kernel⟩
  | 18 => Sum.inl 2
  | 19 => Sum.inr ⟨(false, vertices_425), by decide +kernel⟩
  | 20 => Sum.inl 3
  | 21 => Sum.inr ⟨(false, vertices_369), by decide +kernel⟩
  | 22 => Sum.inl 4
  | 23 => Sum.inl 5
  | 24 => Sum.inl 6
  | 25 => Sum.inl 7
  | 26 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 1 2 3 6 8 668 140 2
cert_row_4 1 0 1 2 7 8 782 266 1
cert_row_4 2 0 4 5 7 8 866 322 1
cert_row_4 3 1 3 4 5 8 628 52 3
cert_rows
cert_pivot_2 6 2 0 1
cert_heightProof 4
cert_coverFacet 0 782
cert_cover_5 0 1 0 1 2 7 266 782 1
cert_coverFacet 1 866
cert_cover_5 1 2 0 4 5 7 322 866 1
cert_coverFacet 2 668
cert_cover_5 2 0 1 2 3 6 140 668 2
cert_coverFacet 3 396
cert_cover_2 3 2 1 6 7 140 396 3
cert_coverFacet 4 628
cert_cover_5 4 3 1 3 4 5 52 628 3
cert_coverFacet 5 420
cert_cover_2 5 4 1 6 7 164 420 3
cert_coverFacet 6 804
cert_cover_2 6 4 1 7 8 292 804 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q0_0032

end
end BundlePart7

section BundlePart8
/- Source: ProjectionCertificates/R_m14e10q0_0033.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q0_0033

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [103, 395, 307, 707, 61, 653, 581, 281, 482, 796, 628, 968, 816, 864, 35, 67, 131, 259, 13, 37, 69, 517, 25, 137, 265, 49, 273, 577, 641, 98, 290, 194, 386, 28, 524, 52, 532, 100, 580, 280, 392, 648, 776, 304, 560, 784, 352, 608, 800, 448, 704, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_103, vertices_395, vertices_307, vertices_707, vertices_61, vertices_653, vertices_581, vertices_281, vertices_482, vertices_796, vertices_628, vertices_968, vertices_816, vertices_864] (by decide +kernel)
  polygons := literalFinset [vertices_35, vertices_67, vertices_131, vertices_259, vertices_13, vertices_37, vertices_69, vertices_517, vertices_25, vertices_137, vertices_265, vertices_49, vertices_273, vertices_577, vertices_641, vertices_98, vertices_290, vertices_194, vertices_386, vertices_28, vertices_524, vertices_52, vertices_532, vertices_100, vertices_580, vertices_280, vertices_392, vertices_648, vertices_776, vertices_304, vertices_560, vertices_784, vertices_352, vertices_608, vertices_800, vertices_448, vertices_704, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_103), (false, vertices_395), (false, vertices_307), (false, vertices_707), (false, vertices_61), (false, vertices_653), (false, vertices_581), (false, vertices_281), (true, vertices_532), (true, vertices_776), (true, vertices_560), (true, vertices_784), (true, vertices_352), (true, vertices_608), (true, vertices_800), (true, vertices_448), (true, vertices_832)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 11 19 20 21 22 23 24 25
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_103) then 12 else
  if p.val = (false, vertices_395) then 16 else
  if p.val = (false, vertices_307) then 17 else
  if p.val = (false, vertices_707) then 18 else
  if p.val = (false, vertices_61) then 13 else
  if p.val = (false, vertices_653) then 14 else
  if p.val = (false, vertices_581) then 0 else
  if p.val = (false, vertices_281) then 1 else
  if p.val = (true, vertices_532) then 2 else
  if p.val = (true, vertices_776) then 3 else
  if p.val = (true, vertices_560) then 4 else
  if p.val = (true, vertices_784) then 5 else
  if p.val = (true, vertices_352) then 6 else
  if p.val = (true, vertices_608) then 7 else
  if p.val = (true, vertices_800) then 8 else
  if p.val = (true, vertices_448) then 9 else
  if p.val = (true, vertices_832) then 10 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_581), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_281), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_532), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_776), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_560), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_784), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_352), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_608), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_800), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_448), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_832), by decide +kernel⟩
  | 11 => Sum.inl 1
  | 12 => Sum.inr ⟨(false, vertices_103), by decide +kernel⟩
  | 13 => Sum.inr ⟨(false, vertices_61), by decide +kernel⟩
  | 14 => Sum.inr ⟨(false, vertices_653), by decide +kernel⟩
  | 15 => Sum.inl 0
  | 16 => Sum.inr ⟨(false, vertices_395), by decide +kernel⟩
  | 17 => Sum.inr ⟨(false, vertices_307), by decide +kernel⟩
  | 18 => Sum.inr ⟨(false, vertices_707), by decide +kernel⟩
  | 19 => Sum.inl 2
  | 20 => Sum.inl 3
  | 21 => Sum.inl 4
  | 22 => Sum.inl 5
  | 23 => Sum.inl 6
  | 24 => Sum.inl 7
  | 25 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 4 5 6 7 482 98 3
cert_row_4 1 1 3 4 5 8 628 52 3
cert_row_4 2 1 2 3 7 8 796 28 3
cert_row_4 3 2 5 6 7 8 968 392 1
cert_rows
cert_pivot_2 0 4 1 2
cert_heightProof 4
cert_coverFacet 0 482
cert_cover_5 0 0 0 4 5 6 98 482 3
cert_coverFacet 1 796
cert_cover_5 1 2 1 2 3 7 28 796 3
cert_coverFacet 2 628
cert_cover_5 2 1 1 3 4 5 52 628 3
cert_coverFacet 3 968
cert_cover_5 3 3 2 5 6 7 392 968 1
cert_coverFacet 4 816
cert_cover_2 4 4 3 7 8 304 816 3
cert_coverFacet 5 864
cert_cover_2 5 5 4 7 8 352 864 3
cert_coveringFacets
cert_coveringProof_6
cert_certificate 4 6
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q0_0033

end
end BundlePart8

section BundlePart9
/- Source: ProjectionCertificates/R_m14e10q0_0034.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q0_0034

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [227, 285, 557, 533, 361, 689, 465, 782, 682, 298, 722, 354, 834, 852, 13, 21, 517, 41, 265, 145, 273, 529, 97, 161, 545, 193, 321, 42, 266, 522, 98, 162, 290, 194, 322, 578, 642, 770, 268, 524, 276, 532, 772, 296, 552, 208, 336, 592, 656, 352, 672, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_227, vertices_285, vertices_557, vertices_533, vertices_361, vertices_689, vertices_465, vertices_782, vertices_682, vertices_298, vertices_722, vertices_354, vertices_834, vertices_852] (by decide +kernel)
  polygons := literalFinset [vertices_13, vertices_21, vertices_517, vertices_41, vertices_265, vertices_145, vertices_273, vertices_529, vertices_97, vertices_161, vertices_545, vertices_193, vertices_321, vertices_42, vertices_266, vertices_522, vertices_98, vertices_162, vertices_290, vertices_194, vertices_322, vertices_578, vertices_642, vertices_770, vertices_268, vertices_524, vertices_276, vertices_532, vertices_772, vertices_296, vertices_552, vertices_208, vertices_336, vertices_592, vertices_656, vertices_352, vertices_672, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_227), (false, vertices_285), (false, vertices_557), (false, vertices_533), (false, vertices_361), (false, vertices_689), (false, vertices_465), (true, vertices_42), (true, vertices_266), (true, vertices_522), (true, vertices_290), (true, vertices_322), (true, vertices_578), (true, vertices_642), (true, vertices_770), (true, vertices_772), (true, vertices_592), (true, vertices_832)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 12 14 17 19 22 23 24 25 26
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_227) then 13 else
  if p.val = (false, vertices_285) then 15 else
  if p.val = (false, vertices_557) then 16 else
  if p.val = (false, vertices_533) then 0 else
  if p.val = (false, vertices_361) then 18 else
  if p.val = (false, vertices_689) then 20 else
  if p.val = (false, vertices_465) then 21 else
  if p.val = (true, vertices_42) then 1 else
  if p.val = (true, vertices_266) then 2 else
  if p.val = (true, vertices_522) then 3 else
  if p.val = (true, vertices_290) then 4 else
  if p.val = (true, vertices_322) then 5 else
  if p.val = (true, vertices_578) then 6 else
  if p.val = (true, vertices_642) then 7 else
  if p.val = (true, vertices_770) then 8 else
  if p.val = (true, vertices_772) then 9 else
  if p.val = (true, vertices_592) then 10 else
  if p.val = (true, vertices_832) then 11 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_533), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_42), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_266), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_522), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_290), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_322), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_578), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_642), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_770), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_772), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_592), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_832), by decide +kernel⟩
  | 12 => Sum.inl 0
  | 13 => Sum.inr ⟨(false, vertices_227), by decide +kernel⟩
  | 14 => Sum.inl 1
  | 15 => Sum.inr ⟨(false, vertices_285), by decide +kernel⟩
  | 16 => Sum.inr ⟨(false, vertices_557), by decide +kernel⟩
  | 17 => Sum.inl 2
  | 18 => Sum.inr ⟨(false, vertices_361), by decide +kernel⟩
  | 19 => Sum.inl 3
  | 20 => Sum.inr ⟨(false, vertices_689), by decide +kernel⟩
  | 21 => Sum.inr ⟨(false, vertices_465), by decide +kernel⟩
  | 22 => Sum.inl 4
  | 23 => Sum.inl 5
  | 24 => Sum.inl 6
  | 25 => Sum.inl 7
  | 26 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 2 4 6 8 682 42 3
cert_row_4 1 0 1 2 7 8 782 266 1
cert_row_4 2 0 3 5 6 8 722 194 1
cert_row_4 3 1 3 5 7 8 852 276 2
cert_rows
cert_pivot_2 4 2 0 1
cert_heightProof 4
cert_coverFacet 0 782
cert_cover_5 0 1 0 1 2 7 266 782 1
cert_coverFacet 1 682
cert_cover_5 1 0 0 2 4 6 42 682 3
cert_coverFacet 2 298
cert_cover_2 2 2 0 4 7 42 298 3
cert_coverFacet 3 722
cert_cover_5 3 2 0 3 5 6 194 722 1
cert_coverFacet 4 354
cert_cover_2 4 4 0 5 7 98 354 3
cert_coverFacet 5 834
cert_cover_2 5 5 0 7 8 322 834 3
cert_coverFacet 6 852
cert_cover_5 6 3 1 3 5 7 276 852 2
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q0_0034

end
end BundlePart9

section BundlePart10
/- Source: ProjectionCertificates/R_m14e10q0_0035.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q0_0035

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [103, 299, 595, 275, 173, 661, 581, 409, 370, 620, 908, 808, 976, 864, 19, 35, 67, 259, 37, 69, 133, 517, 41, 137, 265, 145, 273, 529, 577, 82, 274, 98, 290, 44, 140, 524, 100, 580, 644, 296, 552, 392, 776, 336, 592, 400, 656, 352, 608, 800, 832, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_103, vertices_299, vertices_595, vertices_275, vertices_173, vertices_661, vertices_581, vertices_409, vertices_370, vertices_620, vertices_908, vertices_808, vertices_976, vertices_864] (by decide +kernel)
  polygons := literalFinset [vertices_19, vertices_35, vertices_67, vertices_259, vertices_37, vertices_69, vertices_133, vertices_517, vertices_41, vertices_137, vertices_265, vertices_145, vertices_273, vertices_529, vertices_577, vertices_82, vertices_274, vertices_98, vertices_290, vertices_44, vertices_140, vertices_524, vertices_100, vertices_580, vertices_644, vertices_296, vertices_552, vertices_392, vertices_776, vertices_336, vertices_592, vertices_400, vertices_656, vertices_352, vertices_608, vertices_800, vertices_832, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_103), (false, vertices_299), (false, vertices_595), (false, vertices_275), (false, vertices_173), (false, vertices_661), (false, vertices_581), (false, vertices_409), (true, vertices_524), (true, vertices_552), (true, vertices_776), (true, vertices_336), (true, vertices_352), (true, vertices_608), (true, vertices_800), (true, vertices_832), (true, vertices_896)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 11 15 18 20 21 22 23 24 25
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_103) then 12 else
  if p.val = (false, vertices_299) then 13 else
  if p.val = (false, vertices_595) then 14 else
  if p.val = (false, vertices_275) then 0 else
  if p.val = (false, vertices_173) then 16 else
  if p.val = (false, vertices_661) then 17 else
  if p.val = (false, vertices_581) then 1 else
  if p.val = (false, vertices_409) then 19 else
  if p.val = (true, vertices_524) then 2 else
  if p.val = (true, vertices_552) then 3 else
  if p.val = (true, vertices_776) then 4 else
  if p.val = (true, vertices_336) then 5 else
  if p.val = (true, vertices_352) then 6 else
  if p.val = (true, vertices_608) then 7 else
  if p.val = (true, vertices_800) then 8 else
  if p.val = (true, vertices_832) then 9 else
  if p.val = (true, vertices_896) then 10 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_275), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_581), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_524), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_552), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_776), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_336), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_352), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_608), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_800), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_832), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_896), by decide +kernel⟩
  | 11 => Sum.inl 0
  | 12 => Sum.inr ⟨(false, vertices_103), by decide +kernel⟩
  | 13 => Sum.inr ⟨(false, vertices_299), by decide +kernel⟩
  | 14 => Sum.inr ⟨(false, vertices_595), by decide +kernel⟩
  | 15 => Sum.inl 1
  | 16 => Sum.inr ⟨(false, vertices_173), by decide +kernel⟩
  | 17 => Sum.inr ⟨(false, vertices_661), by decide +kernel⟩
  | 18 => Sum.inl 2
  | 19 => Sum.inr ⟨(false, vertices_409), by decide +kernel⟩
  | 20 => Sum.inl 3
  | 21 => Sum.inl 4
  | 22 => Sum.inl 5
  | 23 => Sum.inl 6
  | 24 => Sum.inl 7
  | 25 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 3 4 5 7 370 82 2
cert_row_4 1 1 2 4 5 8 620 44 3
cert_row_4 2 1 2 6 7 8 908 140 3
cert_row_4 3 3 5 6 7 8 976 336 2
cert_rows
cert_pivot_2 0 4 1 3
cert_heightProof 4
cert_coverFacet 0 370
cert_cover_5 0 0 0 3 4 5 82 370 2
cert_coverFacet 1 620
cert_cover_5 1 1 1 2 4 5 44 620 3
cert_coverFacet 2 908
cert_cover_5 2 2 1 2 6 7 140 908 3
cert_coverFacet 3 808
cert_cover_2 3 4 2 7 8 296 808 3
cert_coverFacet 4 976
cert_cover_5 4 3 3 5 6 7 336 976 2
cert_coverFacet 5 864
cert_cover_2 5 5 4 7 8 352 864 3
cert_coveringFacets
cert_coveringProof_6
cert_certificate 4 6
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q0_0035

end
end BundlePart10

section BundlePart11
/- Source: ProjectionCertificates/R_m14e10q0_0036.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q0_0036

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [587, 541, 405, 677, 345, 961, 310, 570, 282, 330, 738, 354, 564, 484, 21, 133, 517, 25, 73, 521, 273, 321, 577, 385, 641, 26, 74, 266, 522, 50, 274, 98, 290, 546, 322, 578, 52, 276, 532, 164, 292, 548, 388, 280, 536, 328, 560, 224, 352, 672, 448, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_587, vertices_541, vertices_405, vertices_677, vertices_345, vertices_961, vertices_310, vertices_570, vertices_282, vertices_330, vertices_738, vertices_354, vertices_564, vertices_484] (by decide +kernel)
  polygons := literalFinset [vertices_21, vertices_133, vertices_517, vertices_25, vertices_73, vertices_521, vertices_273, vertices_321, vertices_577, vertices_385, vertices_641, vertices_26, vertices_74, vertices_266, vertices_522, vertices_50, vertices_274, vertices_98, vertices_290, vertices_546, vertices_322, vertices_578, vertices_52, vertices_276, vertices_532, vertices_164, vertices_292, vertices_548, vertices_388, vertices_280, vertices_536, vertices_328, vertices_560, vertices_224, vertices_352, vertices_672, vertices_448, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_587), (false, vertices_541), (false, vertices_405), (false, vertices_677), (false, vertices_345), (false, vertices_961), (true, vertices_26), (true, vertices_266), (true, vertices_50), (true, vertices_274), (true, vertices_98), (true, vertices_290), (true, vertices_546), (true, vertices_322), (true, vertices_52), (true, vertices_292), (true, vertices_560), (true, vertices_224), (true, vertices_352)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 13 15 19 21 22 23 25 26 27
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_587) then 14 else
  if p.val = (false, vertices_541) then 16 else
  if p.val = (false, vertices_405) then 17 else
  if p.val = (false, vertices_677) then 18 else
  if p.val = (false, vertices_345) then 20 else
  if p.val = (false, vertices_961) then 24 else
  if p.val = (true, vertices_26) then 0 else
  if p.val = (true, vertices_266) then 1 else
  if p.val = (true, vertices_50) then 2 else
  if p.val = (true, vertices_274) then 3 else
  if p.val = (true, vertices_98) then 4 else
  if p.val = (true, vertices_290) then 5 else
  if p.val = (true, vertices_546) then 6 else
  if p.val = (true, vertices_322) then 7 else
  if p.val = (true, vertices_52) then 8 else
  if p.val = (true, vertices_292) then 9 else
  if p.val = (true, vertices_560) then 10 else
  if p.val = (true, vertices_224) then 11 else
  if p.val = (true, vertices_352) then 12 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_26), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_266), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_50), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_274), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_98), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_290), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_546), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_322), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_52), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_292), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_560), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_224), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_352), by decide +kernel⟩
  | 13 => Sum.inl 0
  | 14 => Sum.inr ⟨(false, vertices_587), by decide +kernel⟩
  | 15 => Sum.inl 1
  | 16 => Sum.inr ⟨(false, vertices_541), by decide +kernel⟩
  | 17 => Sum.inr ⟨(false, vertices_405), by decide +kernel⟩
  | 18 => Sum.inr ⟨(false, vertices_677), by decide +kernel⟩
  | 19 => Sum.inl 2
  | 20 => Sum.inr ⟨(false, vertices_345), by decide +kernel⟩
  | 21 => Sum.inl 3
  | 22 => Sum.inl 4
  | 23 => Sum.inl 5
  | 24 => Sum.inr ⟨(false, vertices_961), by decide +kernel⟩
  | 25 => Sum.inl 6
  | 26 => Sum.inl 7
  | 27 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 2 3 4 8 570 26 3
cert_row_4 1 0 1 3 4 7 310 50 1
cert_row_4 2 0 4 5 6 8 738 98 3
cert_row_4 3 1 4 5 6 7 484 164 2
cert_rows
cert_pivot_2 2 3 0 1
cert_heightProof 4
cert_coverFacet 0 310
cert_cover_5 0 1 0 1 3 4 50 310 1
cert_coverFacet 1 570
cert_cover_5 1 0 0 2 3 4 26 570 3
cert_coverFacet 2 282
cert_cover_2 2 2 0 3 7 26 282 3
cert_coverFacet 3 330
cert_cover_2 3 2 0 5 7 74 330 3
cert_coverFacet 4 738
cert_cover_5 4 2 0 4 5 6 98 738 3
cert_coverFacet 5 354
cert_cover_2 5 4 0 5 7 98 354 3
cert_coverFacet 6 564
cert_cover_2 6 3 1 4 8 52 564 3
cert_coverFacet 7 484
cert_cover_5 7 3 1 4 5 6 164 484 2
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q0_0036

end
end BundlePart11

section BundlePart12
/- Source: ProjectionCertificates/R_m14e10q0_0037.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q0_0037

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [295, 555, 331, 229, 325, 713, 689, 794, 802, 348, 436, 724, 600, 816, 11, 35, 259, 37, 69, 261, 73, 521, 161, 545, 193, 321, 641, 266, 522, 290, 546, 770, 84, 148, 276, 164, 292, 196, 324, 88, 280, 536, 328, 584, 176, 304, 560, 592, 656, 784, 800, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_295, vertices_555, vertices_331, vertices_229, vertices_325, vertices_713, vertices_689, vertices_794, vertices_802, vertices_348, vertices_436, vertices_724, vertices_600, vertices_816] (by decide +kernel)
  polygons := literalFinset [vertices_11, vertices_35, vertices_259, vertices_37, vertices_69, vertices_261, vertices_73, vertices_521, vertices_161, vertices_545, vertices_193, vertices_321, vertices_641, vertices_266, vertices_522, vertices_290, vertices_546, vertices_770, vertices_84, vertices_148, vertices_276, vertices_164, vertices_292, vertices_196, vertices_324, vertices_88, vertices_280, vertices_536, vertices_328, vertices_584, vertices_176, vertices_304, vertices_560, vertices_592, vertices_656, vertices_784, vertices_800, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_295), (false, vertices_555), (false, vertices_331), (false, vertices_229), (false, vertices_325), (false, vertices_713), (false, vertices_689), (true, vertices_770), (true, vertices_84), (true, vertices_148), (true, vertices_276), (true, vertices_88), (true, vertices_280), (true, vertices_536), (true, vertices_304), (true, vertices_592), (true, vertices_784), (true, vertices_800)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 12 16 18 20 22 23 24 25 26
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_295) then 13 else
  if p.val = (false, vertices_555) then 14 else
  if p.val = (false, vertices_331) then 15 else
  if p.val = (false, vertices_229) then 17 else
  if p.val = (false, vertices_325) then 0 else
  if p.val = (false, vertices_713) then 19 else
  if p.val = (false, vertices_689) then 21 else
  if p.val = (true, vertices_770) then 1 else
  if p.val = (true, vertices_84) then 2 else
  if p.val = (true, vertices_148) then 3 else
  if p.val = (true, vertices_276) then 4 else
  if p.val = (true, vertices_88) then 5 else
  if p.val = (true, vertices_280) then 6 else
  if p.val = (true, vertices_536) then 7 else
  if p.val = (true, vertices_304) then 8 else
  if p.val = (true, vertices_592) then 9 else
  if p.val = (true, vertices_784) then 10 else
  if p.val = (true, vertices_800) then 11 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_325), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_770), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_84), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_148), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_276), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_88), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_280), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_536), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_304), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_592), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_784), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_800), by decide +kernel⟩
  | 12 => Sum.inl 0
  | 13 => Sum.inr ⟨(false, vertices_295), by decide +kernel⟩
  | 14 => Sum.inr ⟨(false, vertices_555), by decide +kernel⟩
  | 15 => Sum.inr ⟨(false, vertices_331), by decide +kernel⟩
  | 16 => Sum.inl 1
  | 17 => Sum.inr ⟨(false, vertices_229), by decide +kernel⟩
  | 18 => Sum.inl 2
  | 19 => Sum.inr ⟨(false, vertices_713), by decide +kernel⟩
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
cert_row_4 0 0 2 3 7 8 794 266 2
cert_row_4 1 1 2 3 5 7 348 84 1
cert_row_4 2 1 3 4 6 7 436 148 2
cert_row_4 3 1 3 5 6 8 724 84 3
cert_rows
cert_pivot_2 0 2 4 1
cert_heightProof 4
cert_coverFacet 0 794
cert_cover_5 0 0 0 2 3 7 266 794 2
cert_coverFacet 1 802
cert_cover_2 1 4 0 7 8 290 802 3
cert_coverFacet 2 348
cert_cover_5 2 1 1 2 3 5 84 348 1
cert_coverFacet 3 436
cert_cover_5 3 2 1 3 4 6 148 436 2
cert_coverFacet 4 724
cert_cover_5 4 3 1 3 5 6 84 724 3
cert_coverFacet 5 600
cert_cover_2 5 3 2 5 8 88 600 3
cert_coverFacet 6 816
cert_cover_2 6 4 3 7 8 304 816 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q0_0037

end
end BundlePart12

section BundlePart13
/- Source: ProjectionCertificates/R_m14e10q0_0040.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q0_0040

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [327, 91, 299, 61, 213, 805, 202, 394, 962, 692, 708, 836, 248, 936, 11, 67, 259, 21, 37, 69, 261, 25, 41, 81, 289, 74, 138, 266, 194, 322, 386, 52, 148, 548, 196, 324, 580, 644, 772, 56, 88, 168, 296, 200, 392, 176, 208, 672, 800, 704, 832, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_327, vertices_91, vertices_299, vertices_61, vertices_213, vertices_805, vertices_202, vertices_394, vertices_962, vertices_692, vertices_708, vertices_836, vertices_248, vertices_936] (by decide +kernel)
  polygons := literalFinset [vertices_11, vertices_67, vertices_259, vertices_21, vertices_37, vertices_69, vertices_261, vertices_25, vertices_41, vertices_81, vertices_289, vertices_74, vertices_138, vertices_266, vertices_194, vertices_322, vertices_386, vertices_52, vertices_148, vertices_548, vertices_196, vertices_324, vertices_580, vertices_644, vertices_772, vertices_56, vertices_88, vertices_168, vertices_296, vertices_200, vertices_392, vertices_176, vertices_208, vertices_672, vertices_800, vertices_704, vertices_832, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_327), (false, vertices_91), (false, vertices_299), (false, vertices_61), (false, vertices_213), (false, vertices_805), (true, vertices_138), (true, vertices_194), (true, vertices_386), (true, vertices_580), (true, vertices_644), (true, vertices_168), (true, vertices_200), (true, vertices_392), (true, vertices_176), (true, vertices_672), (true, vertices_704), (true, vertices_832), (true, vertices_896)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 13 17 21 22 23 24 25 26 27
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_327) then 14 else
  if p.val = (false, vertices_91) then 15 else
  if p.val = (false, vertices_299) then 16 else
  if p.val = (false, vertices_61) then 18 else
  if p.val = (false, vertices_213) then 19 else
  if p.val = (false, vertices_805) then 20 else
  if p.val = (true, vertices_138) then 0 else
  if p.val = (true, vertices_194) then 1 else
  if p.val = (true, vertices_386) then 2 else
  if p.val = (true, vertices_580) then 3 else
  if p.val = (true, vertices_644) then 4 else
  if p.val = (true, vertices_168) then 5 else
  if p.val = (true, vertices_200) then 6 else
  if p.val = (true, vertices_392) then 7 else
  if p.val = (true, vertices_176) then 8 else
  if p.val = (true, vertices_672) then 9 else
  if p.val = (true, vertices_704) then 10 else
  if p.val = (true, vertices_832) then 11 else
  if p.val = (true, vertices_896) then 12 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_138), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_194), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_386), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_580), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_644), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_168), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_200), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_392), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_176), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_672), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_704), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_832), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_896), by decide +kernel⟩
  | 13 => Sum.inl 0
  | 14 => Sum.inr ⟨(false, vertices_327), by decide +kernel⟩
  | 15 => Sum.inr ⟨(false, vertices_91), by decide +kernel⟩
  | 16 => Sum.inr ⟨(false, vertices_299), by decide +kernel⟩
  | 17 => Sum.inl 1
  | 18 => Sum.inr ⟨(false, vertices_61), by decide +kernel⟩
  | 19 => Sum.inr ⟨(false, vertices_213), by decide +kernel⟩
  | 20 => Sum.inr ⟨(false, vertices_805), by decide +kernel⟩
  | 21 => Sum.inl 2
  | 22 => Sum.inl 3
  | 23 => Sum.inl 4
  | 24 => Sum.inl 5
  | 25 => Sum.inl 6
  | 26 => Sum.inl 7
  | 27 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 5 6 7 8 962 194 3
cert_row_4 1 1 3 4 6 8 692 52 3
cert_row_4 2 2 3 4 5 6 248 56 3
cert_row_4 3 2 4 6 7 8 936 168 3
cert_rows
cert_pivot_2 0 1 3 2
cert_heightProof 4
cert_coverFacet 0 202
cert_cover_2 0 2 0 5 6 74 202 3
cert_coverFacet 1 394
cert_cover_2 1 2 0 6 7 138 394 3
cert_coverFacet 2 962
cert_cover_5 2 0 0 5 6 7 194 962 3
cert_coverFacet 3 692
cert_cover_5 3 1 1 3 4 6 52 692 3
cert_coverFacet 4 708
cert_cover_2 4 5 1 6 8 196 708 3
cert_coverFacet 5 836
cert_cover_2 5 5 1 7 8 324 836 3
cert_coverFacet 6 248
cert_cover_5 6 2 2 3 4 5 56 248 3
cert_coverFacet 7 936
cert_cover_5 7 3 2 4 6 7 168 936 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q0_0040

end
end BundlePart13

section BundlePart14
/- Source: ProjectionCertificates/R_m14e10q0_0041.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q0_0041

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [403, 803, 707, 309, 217, 625, 782, 394, 650, 124, 284, 716, 868, 408, 131, 259, 515, 49, 81, 145, 273, 289, 545, 193, 577, 138, 266, 522, 386, 642, 770, 28, 76, 268, 524, 52, 276, 100, 292, 580, 772, 88, 152, 280, 200, 392, 648, 112, 400, 608, 800, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_403, vertices_803, vertices_707, vertices_309, vertices_217, vertices_625, vertices_782, vertices_394, vertices_650, vertices_124, vertices_284, vertices_716, vertices_868, vertices_408] (by decide +kernel)
  polygons := literalFinset [vertices_131, vertices_259, vertices_515, vertices_49, vertices_81, vertices_145, vertices_273, vertices_289, vertices_545, vertices_193, vertices_577, vertices_138, vertices_266, vertices_522, vertices_386, vertices_642, vertices_770, vertices_28, vertices_76, vertices_268, vertices_524, vertices_52, vertices_276, vertices_100, vertices_292, vertices_580, vertices_772, vertices_88, vertices_152, vertices_280, vertices_200, vertices_392, vertices_648, vertices_112, vertices_400, vertices_608, vertices_800, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_403), (false, vertices_803), (false, vertices_707), (false, vertices_309), (false, vertices_217), (false, vertices_625), (true, vertices_138), (true, vertices_266), (true, vertices_522), (true, vertices_28), (true, vertices_76), (true, vertices_268), (true, vertices_524), (true, vertices_100), (true, vertices_580), (true, vertices_772), (true, vertices_280), (true, vertices_392), (true, vertices_648)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 13 17 19 21 23 24 25 26 27
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_403) then 14 else
  if p.val = (false, vertices_803) then 15 else
  if p.val = (false, vertices_707) then 16 else
  if p.val = (false, vertices_309) then 18 else
  if p.val = (false, vertices_217) then 20 else
  if p.val = (false, vertices_625) then 22 else
  if p.val = (true, vertices_138) then 0 else
  if p.val = (true, vertices_266) then 1 else
  if p.val = (true, vertices_522) then 2 else
  if p.val = (true, vertices_28) then 3 else
  if p.val = (true, vertices_76) then 4 else
  if p.val = (true, vertices_268) then 5 else
  if p.val = (true, vertices_524) then 6 else
  if p.val = (true, vertices_100) then 7 else
  if p.val = (true, vertices_580) then 8 else
  if p.val = (true, vertices_772) then 9 else
  if p.val = (true, vertices_280) then 10 else
  if p.val = (true, vertices_392) then 11 else
  if p.val = (true, vertices_648) then 12 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_138), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_266), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_522), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_28), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_76), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_268), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_524), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_100), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_580), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_772), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_280), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_392), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_648), by decide +kernel⟩
  | 13 => Sum.inl 0
  | 14 => Sum.inr ⟨(false, vertices_403), by decide +kernel⟩
  | 15 => Sum.inr ⟨(false, vertices_803), by decide +kernel⟩
  | 16 => Sum.inr ⟨(false, vertices_707), by decide +kernel⟩
  | 17 => Sum.inl 1
  | 18 => Sum.inr ⟨(false, vertices_309), by decide +kernel⟩
  | 19 => Sum.inl 2
  | 20 => Sum.inr ⟨(false, vertices_217), by decide +kernel⟩
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
cert_row_4 0 0 1 2 7 8 782 266 1
cert_row_4 1 1 2 3 4 5 124 28 3
cert_row_4 2 1 2 5 6 8 716 76 3
cert_row_4 3 1 4 5 7 8 868 100 3
cert_rows
cert_pivot_2 0 3 2 1
cert_heightProof 4
cert_coverFacet 0 782
cert_cover_5 0 0 0 1 2 7 266 782 1
cert_coverFacet 1 394
cert_cover_2 1 2 0 6 7 138 394 3
cert_coverFacet 2 650
cert_cover_2 2 2 0 6 8 138 650 3
cert_coverFacet 3 124
cert_cover_5 3 1 1 2 3 4 28 124 3
cert_coverFacet 4 284
cert_cover_2 4 2 1 3 7 28 284 3
cert_coverFacet 5 716
cert_cover_5 5 2 1 2 5 6 76 716 3
cert_coverFacet 6 868
cert_cover_5 6 3 1 4 5 7 100 868 3
cert_coverFacet 7 408
cert_cover_2 7 3 2 6 7 152 408 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q0_0041

end
end BundlePart14

section BundlePart15
/- Source: ProjectionCertificates/R_m14e10q0_0042.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q0_0042

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [587, 541, 405, 677, 345, 961, 566, 314, 538, 330, 738, 354, 308, 484, 21, 133, 517, 25, 73, 521, 273, 321, 577, 385, 641, 26, 74, 266, 522, 50, 530, 98, 290, 546, 322, 578, 52, 276, 532, 164, 292, 548, 388, 280, 536, 328, 304, 224, 352, 672, 448, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_587, vertices_541, vertices_405, vertices_677, vertices_345, vertices_961, vertices_566, vertices_314, vertices_538, vertices_330, vertices_738, vertices_354, vertices_308, vertices_484] (by decide +kernel)
  polygons := literalFinset [vertices_21, vertices_133, vertices_517, vertices_25, vertices_73, vertices_521, vertices_273, vertices_321, vertices_577, vertices_385, vertices_641, vertices_26, vertices_74, vertices_266, vertices_522, vertices_50, vertices_530, vertices_98, vertices_290, vertices_546, vertices_322, vertices_578, vertices_52, vertices_276, vertices_532, vertices_164, vertices_292, vertices_548, vertices_388, vertices_280, vertices_536, vertices_328, vertices_304, vertices_224, vertices_352, vertices_672, vertices_448, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_587), (false, vertices_541), (false, vertices_405), (false, vertices_677), (false, vertices_345), (false, vertices_961), (true, vertices_26), (true, vertices_266), (true, vertices_50), (true, vertices_530), (true, vertices_98), (true, vertices_290), (true, vertices_546), (true, vertices_322), (true, vertices_52), (true, vertices_292), (true, vertices_304), (true, vertices_224), (true, vertices_352)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 13 15 19 21 22 23 25 26 27
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_587) then 14 else
  if p.val = (false, vertices_541) then 16 else
  if p.val = (false, vertices_405) then 17 else
  if p.val = (false, vertices_677) then 18 else
  if p.val = (false, vertices_345) then 20 else
  if p.val = (false, vertices_961) then 24 else
  if p.val = (true, vertices_26) then 0 else
  if p.val = (true, vertices_266) then 1 else
  if p.val = (true, vertices_50) then 2 else
  if p.val = (true, vertices_530) then 3 else
  if p.val = (true, vertices_98) then 4 else
  if p.val = (true, vertices_290) then 5 else
  if p.val = (true, vertices_546) then 6 else
  if p.val = (true, vertices_322) then 7 else
  if p.val = (true, vertices_52) then 8 else
  if p.val = (true, vertices_292) then 9 else
  if p.val = (true, vertices_304) then 10 else
  if p.val = (true, vertices_224) then 11 else
  if p.val = (true, vertices_352) then 12 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_26), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_266), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_50), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_530), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_98), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_290), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_546), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_322), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_52), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_292), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_304), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_224), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_352), by decide +kernel⟩
  | 13 => Sum.inl 0
  | 14 => Sum.inr ⟨(false, vertices_587), by decide +kernel⟩
  | 15 => Sum.inl 1
  | 16 => Sum.inr ⟨(false, vertices_541), by decide +kernel⟩
  | 17 => Sum.inr ⟨(false, vertices_405), by decide +kernel⟩
  | 18 => Sum.inr ⟨(false, vertices_677), by decide +kernel⟩
  | 19 => Sum.inl 2
  | 20 => Sum.inr ⟨(false, vertices_345), by decide +kernel⟩
  | 21 => Sum.inl 3
  | 22 => Sum.inl 4
  | 23 => Sum.inl 5
  | 24 => Sum.inr ⟨(false, vertices_961), by decide +kernel⟩
  | 25 => Sum.inl 6
  | 26 => Sum.inl 7
  | 27 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 2 3 4 7 314 26 3
cert_row_4 1 0 1 3 4 8 566 50 1
cert_row_4 2 0 4 5 6 8 738 98 3
cert_row_4 3 1 4 5 6 7 484 164 2
cert_rows
cert_pivot_2 2 3 0 1
cert_heightProof 4
cert_coverFacet 0 566
cert_cover_5 0 1 0 1 3 4 50 566 1
cert_coverFacet 1 314
cert_cover_5 1 0 0 2 3 4 26 314 3
cert_coverFacet 2 538
cert_cover_2 2 2 0 3 8 26 538 3
cert_coverFacet 3 330
cert_cover_2 3 2 0 5 7 74 330 3
cert_coverFacet 4 738
cert_cover_5 4 2 0 4 5 6 98 738 3
cert_coverFacet 5 354
cert_cover_2 5 4 0 5 7 98 354 3
cert_coverFacet 6 308
cert_cover_2 6 3 1 4 7 52 308 3
cert_coverFacet 7 484
cert_cover_5 7 3 1 4 5 6 164 484 2
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q0_0042

end
end BundlePart15

section BundlePart16
/- Source: ProjectionCertificates/R_m14e10q0_0045.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q0_0045

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [155, 51, 419, 61, 205, 357, 961, 566, 914, 866, 604, 612, 664, 712, 19, 35, 131, 13, 37, 69, 25, 137, 49, 289, 193, 321, 385, 50, 146, 530, 290, 546, 386, 770, 28, 76, 52, 532, 100, 548, 580, 152, 536, 200, 584, 648, 656, 352, 608, 704, 832, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_155, vertices_51, vertices_419, vertices_61, vertices_205, vertices_357, vertices_961, vertices_566, vertices_914, vertices_866, vertices_604, vertices_612, vertices_664, vertices_712] (by decide +kernel)
  polygons := literalFinset [vertices_19, vertices_35, vertices_131, vertices_13, vertices_37, vertices_69, vertices_25, vertices_137, vertices_49, vertices_289, vertices_193, vertices_321, vertices_385, vertices_50, vertices_146, vertices_530, vertices_290, vertices_546, vertices_386, vertices_770, vertices_28, vertices_76, vertices_52, vertices_532, vertices_100, vertices_548, vertices_580, vertices_152, vertices_536, vertices_200, vertices_584, vertices_648, vertices_656, vertices_352, vertices_608, vertices_704, vertices_832, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_155), (false, vertices_51), (false, vertices_419), (false, vertices_61), (false, vertices_205), (false, vertices_357), (false, vertices_961), (true, vertices_530), (true, vertices_546), (true, vertices_770), (true, vertices_532), (true, vertices_548), (true, vertices_580), (true, vertices_536), (true, vertices_584), (true, vertices_648), (true, vertices_656), (true, vertices_608)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 12 15 19 20 21 22 24 25 26
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_155) then 13 else
  if p.val = (false, vertices_51) then 0 else
  if p.val = (false, vertices_419) then 14 else
  if p.val = (false, vertices_61) then 16 else
  if p.val = (false, vertices_205) then 17 else
  if p.val = (false, vertices_357) then 18 else
  if p.val = (false, vertices_961) then 23 else
  if p.val = (true, vertices_530) then 1 else
  if p.val = (true, vertices_546) then 2 else
  if p.val = (true, vertices_770) then 3 else
  if p.val = (true, vertices_532) then 4 else
  if p.val = (true, vertices_548) then 5 else
  if p.val = (true, vertices_580) then 6 else
  if p.val = (true, vertices_536) then 7 else
  if p.val = (true, vertices_584) then 8 else
  if p.val = (true, vertices_648) then 9 else
  if p.val = (true, vertices_656) then 10 else
  if p.val = (true, vertices_608) then 11 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_51), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_530), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_546), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_770), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_532), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_548), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_580), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_536), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_584), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_648), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_656), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_608), by decide +kernel⟩
  | 12 => Sum.inl 0
  | 13 => Sum.inr ⟨(false, vertices_155), by decide +kernel⟩
  | 14 => Sum.inr ⟨(false, vertices_419), by decide +kernel⟩
  | 15 => Sum.inl 1
  | 16 => Sum.inr ⟨(false, vertices_61), by decide +kernel⟩
  | 17 => Sum.inr ⟨(false, vertices_205), by decide +kernel⟩
  | 18 => Sum.inr ⟨(false, vertices_357), by decide +kernel⟩
  | 19 => Sum.inl 2
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
cert_row_4 0 0 3 6 7 8 914 146 3
cert_row_4 1 0 4 5 7 8 866 290 2
cert_row_4 2 0 1 3 4 8 566 50 1
cert_row_4 3 1 2 3 5 8 604 28 3
cert_rows
cert_pivot_2 6 7 0 1
cert_heightProof 4
cert_coverFacet 0 566
cert_cover_5 0 2 0 1 3 4 50 566 1
cert_coverFacet 1 914
cert_cover_5 1 0 0 3 6 7 146 914 3
cert_coverFacet 2 866
cert_cover_5 2 1 0 4 5 7 290 866 2
cert_coverFacet 3 604
cert_cover_5 3 3 1 2 3 5 28 604 3
cert_coverFacet 4 612
cert_cover_2 4 4 1 5 8 100 612 3
cert_coverFacet 5 664
cert_cover_2 5 3 2 6 8 152 664 3
cert_coverFacet 6 712
cert_cover_2 6 5 2 6 8 200 712 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q0_0045

end
end BundlePart16

section BundlePart17
/- Source: ProjectionCertificates/R_m14e10q0_0046.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q0_0046

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [775, 653, 421, 601, 233, 865, 662, 390, 186, 306, 850, 418, 376, 664, 133, 261, 517, 73, 137, 521, 97, 161, 289, 577, 769, 134, 262, 518, 50, 146, 274, 530, 162, 290, 386, 770, 388, 644, 56, 88, 152, 536, 104, 168, 648, 304, 336, 592, 656, 352, 416, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_775, vertices_653, vertices_421, vertices_601, vertices_233, vertices_865, vertices_662, vertices_390, vertices_186, vertices_306, vertices_850, vertices_418, vertices_376, vertices_664] (by decide +kernel)
  polygons := literalFinset [vertices_133, vertices_261, vertices_517, vertices_73, vertices_137, vertices_521, vertices_97, vertices_161, vertices_289, vertices_577, vertices_769, vertices_134, vertices_262, vertices_518, vertices_50, vertices_146, vertices_274, vertices_530, vertices_162, vertices_290, vertices_386, vertices_770, vertices_388, vertices_644, vertices_56, vertices_88, vertices_152, vertices_536, vertices_104, vertices_168, vertices_648, vertices_304, vertices_336, vertices_592, vertices_656, vertices_352, vertices_416, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_775), (false, vertices_653), (false, vertices_421), (false, vertices_601), (false, vertices_233), (false, vertices_865), (true, vertices_134), (true, vertices_50), (true, vertices_146), (true, vertices_274), (true, vertices_530), (true, vertices_162), (true, vertices_290), (true, vertices_386), (true, vertices_56), (true, vertices_152), (true, vertices_304), (true, vertices_336), (true, vertices_656)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 13 15 18 21 22 24 25 26 27
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_775) then 14 else
  if p.val = (false, vertices_653) then 16 else
  if p.val = (false, vertices_421) then 17 else
  if p.val = (false, vertices_601) then 19 else
  if p.val = (false, vertices_233) then 20 else
  if p.val = (false, vertices_865) then 23 else
  if p.val = (true, vertices_134) then 0 else
  if p.val = (true, vertices_50) then 1 else
  if p.val = (true, vertices_146) then 2 else
  if p.val = (true, vertices_274) then 3 else
  if p.val = (true, vertices_530) then 4 else
  if p.val = (true, vertices_162) then 5 else
  if p.val = (true, vertices_290) then 6 else
  if p.val = (true, vertices_386) then 7 else
  if p.val = (true, vertices_56) then 8 else
  if p.val = (true, vertices_152) then 9 else
  if p.val = (true, vertices_304) then 10 else
  if p.val = (true, vertices_336) then 11 else
  if p.val = (true, vertices_656) then 12 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_134), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_50), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_146), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_274), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_530), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_162), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_290), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_386), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_56), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_152), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_304), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_336), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_656), by decide +kernel⟩
  | 13 => Sum.inl 0
  | 14 => Sum.inr ⟨(false, vertices_775), by decide +kernel⟩
  | 15 => Sum.inl 1
  | 16 => Sum.inr ⟨(false, vertices_653), by decide +kernel⟩
  | 17 => Sum.inr ⟨(false, vertices_421), by decide +kernel⟩
  | 18 => Sum.inl 2
  | 19 => Sum.inr ⟨(false, vertices_601), by decide +kernel⟩
  | 20 => Sum.inr ⟨(false, vertices_233), by decide +kernel⟩
  | 21 => Sum.inl 3
  | 22 => Sum.inl 4
  | 23 => Sum.inr ⟨(false, vertices_865), by decide +kernel⟩
  | 24 => Sum.inl 5
  | 25 => Sum.inl 6
  | 26 => Sum.inl 7
  | 27 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 3 6 8 662 134 2
cert_row_4 1 0 2 3 4 6 186 50 1
cert_row_4 2 0 3 5 7 8 850 274 2
cert_row_4 3 2 3 4 5 7 376 56 3
cert_rows
cert_pivot_2 1 6 0 2
cert_heightProof 4
cert_coverFacet 0 662
cert_cover_5 0 0 0 1 3 6 134 662 2
cert_coverFacet 1 390
cert_cover_2 1 1 0 6 7 134 390 3
cert_coverFacet 2 186
cert_cover_5 2 1 0 2 3 4 50 186 1
cert_coverFacet 3 306
cert_cover_2 3 3 0 4 7 50 306 3
cert_coverFacet 4 850
cert_cover_5 4 2 0 3 5 7 274 850 2
cert_coverFacet 5 418
cert_cover_2 5 4 0 6 7 162 418 3
cert_coverFacet 6 376
cert_cover_5 6 3 2 3 4 5 56 376 3
cert_coverFacet 7 664
cert_cover_2 7 3 2 6 8 152 664 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q0_0046

end
end BundlePart17

section BundlePart18
/- Source: ProjectionCertificates/R_m14e10q0_0051.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q0_0051

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [551, 539, 211, 163, 93, 781, 229, 690, 364, 804, 344, 920, 464, 992, 19, 35, 131, 515, 13, 37, 69, 517, 25, 521, 81, 161, 193, 146, 530, 162, 546, 76, 268, 100, 292, 548, 772, 88, 280, 536, 328, 776, 208, 336, 400, 656, 224, 352, 672, 800, 448, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_551, vertices_539, vertices_211, vertices_163, vertices_93, vertices_781, vertices_229, vertices_690, vertices_364, vertices_804, vertices_344, vertices_920, vertices_464, vertices_992] (by decide +kernel)
  polygons := literalFinset [vertices_19, vertices_35, vertices_131, vertices_515, vertices_13, vertices_37, vertices_69, vertices_517, vertices_25, vertices_521, vertices_81, vertices_161, vertices_193, vertices_146, vertices_530, vertices_162, vertices_546, vertices_76, vertices_268, vertices_100, vertices_292, vertices_548, vertices_772, vertices_88, vertices_280, vertices_536, vertices_328, vertices_776, vertices_208, vertices_336, vertices_400, vertices_656, vertices_224, vertices_352, vertices_672, vertices_800, vertices_448, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_551), (false, vertices_539), (false, vertices_211), (false, vertices_163), (false, vertices_93), (false, vertices_781), (false, vertices_229), (true, vertices_292), (true, vertices_280), (true, vertices_328), (true, vertices_336), (true, vertices_400), (true, vertices_656), (true, vertices_352), (true, vertices_672), (true, vertices_800), (true, vertices_448), (true, vertices_896)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 12 16 20 21 22 23 24 25 26
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_551) then 13 else
  if p.val = (false, vertices_539) then 14 else
  if p.val = (false, vertices_211) then 15 else
  if p.val = (false, vertices_163) then 0 else
  if p.val = (false, vertices_93) then 17 else
  if p.val = (false, vertices_781) then 18 else
  if p.val = (false, vertices_229) then 19 else
  if p.val = (true, vertices_292) then 1 else
  if p.val = (true, vertices_280) then 2 else
  if p.val = (true, vertices_328) then 3 else
  if p.val = (true, vertices_336) then 4 else
  if p.val = (true, vertices_400) then 5 else
  if p.val = (true, vertices_656) then 6 else
  if p.val = (true, vertices_352) then 7 else
  if p.val = (true, vertices_672) then 8 else
  if p.val = (true, vertices_800) then 9 else
  if p.val = (true, vertices_448) then 10 else
  if p.val = (true, vertices_896) then 11 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_163), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_292), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_280), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_328), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_336), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_400), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_656), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_352), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_672), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_800), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_448), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_896), by decide +kernel⟩
  | 12 => Sum.inl 0
  | 13 => Sum.inr ⟨(false, vertices_551), by decide +kernel⟩
  | 14 => Sum.inr ⟨(false, vertices_539), by decide +kernel⟩
  | 15 => Sum.inr ⟨(false, vertices_211), by decide +kernel⟩
  | 16 => Sum.inl 1
  | 17 => Sum.inr ⟨(false, vertices_93), by decide +kernel⟩
  | 18 => Sum.inr ⟨(false, vertices_781), by decide +kernel⟩
  | 19 => Sum.inr ⟨(false, vertices_229), by decide +kernel⟩
  | 20 => Sum.inl 2
  | 21 => Sum.inl 3
  | 22 => Sum.inl 4
  | 23 => Sum.inl 5
  | 24 => Sum.inl 6
  | 25 => Sum.inl 7
  | 26 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 3 4 6 8 690 146 2
cert_row_4 1 1 2 4 5 7 364 76 2
cert_row_4 2 2 3 6 7 8 920 280 2
cert_row_4 3 4 5 6 7 8 992 224 3
cert_rows
cert_pivot_2 0 1 2 4
cert_heightProof 4
cert_coverFacet 0 690
cert_cover_5 0 0 0 3 4 6 146 690 2
cert_coverFacet 1 364
cert_cover_5 1 1 1 2 4 5 76 364 2
cert_coverFacet 2 804
cert_cover_2 2 4 1 7 8 292 804 3
cert_coverFacet 3 344
cert_cover_2 3 3 2 5 7 88 344 3
cert_coverFacet 4 920
cert_cover_5 4 2 2 3 6 7 280 920 2
cert_coverFacet 5 464
cert_cover_2 5 5 3 6 7 208 464 3
cert_coverFacet 6 992
cert_cover_5 6 3 4 5 6 7 224 992 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q0_0051

end
end BundlePart18

section BundlePart19
/- Source: ProjectionCertificates/R_m14e10q0_0052.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q0_0052

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [779, 589, 117, 805, 345, 433, 678, 426, 714, 802, 180, 724, 456, 464, 37, 69, 517, 73, 265, 521, 49, 81, 273, 289, 769, 138, 266, 522, 162, 290, 546, 642, 770, 52, 84, 148, 164, 548, 580, 644, 200, 328, 584, 392, 176, 208, 336, 400, 416, 800, 448, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_779, vertices_589, vertices_117, vertices_805, vertices_345, vertices_433, vertices_678, vertices_426, vertices_714, vertices_802, vertices_180, vertices_724, vertices_456, vertices_464] (by decide +kernel)
  polygons := literalFinset [vertices_37, vertices_69, vertices_517, vertices_73, vertices_265, vertices_521, vertices_49, vertices_81, vertices_273, vertices_289, vertices_769, vertices_138, vertices_266, vertices_522, vertices_162, vertices_290, vertices_546, vertices_642, vertices_770, vertices_52, vertices_84, vertices_148, vertices_164, vertices_548, vertices_580, vertices_644, vertices_200, vertices_328, vertices_584, vertices_392, vertices_176, vertices_208, vertices_336, vertices_400, vertices_416, vertices_800, vertices_448, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_779), (false, vertices_589), (false, vertices_117), (false, vertices_805), (false, vertices_345), (false, vertices_433), (true, vertices_138), (true, vertices_162), (true, vertices_290), (true, vertices_546), (true, vertices_642), (true, vertices_148), (true, vertices_164), (true, vertices_644), (true, vertices_200), (true, vertices_392), (true, vertices_208), (true, vertices_448), (true, vertices_704)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 13 15 19 21 23 24 25 26 27
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_779) then 14 else
  if p.val = (false, vertices_589) then 16 else
  if p.val = (false, vertices_117) then 17 else
  if p.val = (false, vertices_805) then 18 else
  if p.val = (false, vertices_345) then 20 else
  if p.val = (false, vertices_433) then 22 else
  if p.val = (true, vertices_138) then 0 else
  if p.val = (true, vertices_162) then 1 else
  if p.val = (true, vertices_290) then 2 else
  if p.val = (true, vertices_546) then 3 else
  if p.val = (true, vertices_642) then 4 else
  if p.val = (true, vertices_148) then 5 else
  if p.val = (true, vertices_164) then 6 else
  if p.val = (true, vertices_644) then 7 else
  if p.val = (true, vertices_200) then 8 else
  if p.val = (true, vertices_392) then 9 else
  if p.val = (true, vertices_208) then 10 else
  if p.val = (true, vertices_448) then 11 else
  if p.val = (true, vertices_704) then 12 else
  0
cert_priority
cert_nodeAtPriority_11 138 162 290 546 642 148 164 644 200 392 208 448 704 779 589 117 805 345 433
cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 2 4 6 7 426 138 2
cert_row_4 1 0 1 4 6 8 678 162 1
cert_row_4 2 0 2 5 6 8 714 138 2
cert_row_4 3 1 3 5 6 8 724 84 3
cert_rows
cert_pivot_2 7 4 0 1
cert_heightProof 4
cert_coverFacet 0 678
cert_cover_5 0 1 0 1 4 6 162 678 1
cert_coverFacet 1 426
cert_cover_5 1 0 0 2 4 6 138 426 2
cert_coverFacet 2 714
cert_cover_5 2 2 0 2 5 6 138 714 2
cert_coverFacet 3 802
cert_cover_2 3 4 0 7 8 290 802 3
cert_coverFacet 4 180
cert_cover_2 4 3 1 4 6 52 180 3
cert_coverFacet 5 724
cert_cover_5 5 3 1 3 5 6 84 724 3
cert_coverFacet 6 456
cert_cover_2 6 5 2 6 7 200 456 3
cert_coverFacet 7 464
cert_cover_2 7 5 3 6 7 208 464 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q0_0052

end
end BundlePart19

section BundlePart20
/- Source: ProjectionCertificates/R_m14e10q0_0054.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q0_0054

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [391, 779, 595, 147, 301, 589, 213, 690, 898, 108, 484, 632, 936, 240, 19, 131, 259, 515, 13, 69, 133, 261, 265, 521, 81, 145, 577, 146, 530, 386, 642, 770, 44, 76, 100, 292, 196, 388, 104, 296, 552, 584, 776, 112, 176, 560, 208, 592, 224, 416, 672, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_391, vertices_779, vertices_595, vertices_147, vertices_301, vertices_589, vertices_213, vertices_690, vertices_898, vertices_108, vertices_484, vertices_632, vertices_936, vertices_240] (by decide +kernel)
  polygons := literalFinset [vertices_19, vertices_131, vertices_259, vertices_515, vertices_13, vertices_69, vertices_133, vertices_261, vertices_265, vertices_521, vertices_81, vertices_145, vertices_577, vertices_146, vertices_530, vertices_386, vertices_642, vertices_770, vertices_44, vertices_76, vertices_100, vertices_292, vertices_196, vertices_388, vertices_104, vertices_296, vertices_552, vertices_584, vertices_776, vertices_112, vertices_176, vertices_560, vertices_208, vertices_592, vertices_224, vertices_416, vertices_672, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_391), (false, vertices_779), (false, vertices_595), (false, vertices_147), (false, vertices_301), (false, vertices_589), (false, vertices_213), (true, vertices_642), (true, vertices_100), (true, vertices_104), (true, vertices_552), (true, vertices_112), (true, vertices_176), (true, vertices_560), (true, vertices_224), (true, vertices_416), (true, vertices_672), (true, vertices_896)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 12 16 20 21 22 23 24 25 26
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_391) then 13 else
  if p.val = (false, vertices_779) then 14 else
  if p.val = (false, vertices_595) then 15 else
  if p.val = (false, vertices_147) then 0 else
  if p.val = (false, vertices_301) then 17 else
  if p.val = (false, vertices_589) then 18 else
  if p.val = (false, vertices_213) then 19 else
  if p.val = (true, vertices_642) then 1 else
  if p.val = (true, vertices_100) then 2 else
  if p.val = (true, vertices_104) then 3 else
  if p.val = (true, vertices_552) then 4 else
  if p.val = (true, vertices_112) then 5 else
  if p.val = (true, vertices_176) then 6 else
  if p.val = (true, vertices_560) then 7 else
  if p.val = (true, vertices_224) then 8 else
  if p.val = (true, vertices_416) then 9 else
  if p.val = (true, vertices_672) then 10 else
  if p.val = (true, vertices_896) then 11 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_147), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_642), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_100), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_104), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_552), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_112), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_176), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_560), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_224), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_416), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_672), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_896), by decide +kernel⟩
  | 12 => Sum.inl 0
  | 13 => Sum.inr ⟨(false, vertices_391), by decide +kernel⟩
  | 14 => Sum.inr ⟨(false, vertices_779), by decide +kernel⟩
  | 15 => Sum.inr ⟨(false, vertices_595), by decide +kernel⟩
  | 16 => Sum.inl 1
  | 17 => Sum.inr ⟨(false, vertices_301), by decide +kernel⟩
  | 18 => Sum.inr ⟨(false, vertices_589), by decide +kernel⟩
  | 19 => Sum.inr ⟨(false, vertices_213), by decide +kernel⟩
  | 20 => Sum.inl 2
  | 21 => Sum.inl 3
  | 22 => Sum.inl 4
  | 23 => Sum.inl 5
  | 24 => Sum.inl 6
  | 25 => Sum.inl 7
  | 26 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 3 4 6 8 690 146 2
cert_row_4 1 1 4 5 6 7 484 100 3
cert_row_4 2 2 3 4 5 8 632 104 1
cert_row_4 3 2 4 6 7 8 936 296 2
cert_rows
cert_pivot_2 0 1 3 2
cert_heightProof 4
cert_coverFacet 0 690
cert_cover_5 0 0 0 3 4 6 146 690 2
cert_coverFacet 1 898
cert_cover_2 1 6 0 7 8 386 898 3
cert_coverFacet 2 108
cert_cover_2 2 2 1 4 5 44 108 3
cert_coverFacet 3 484
cert_cover_5 3 1 1 4 5 6 100 484 3
cert_coverFacet 4 632
cert_cover_5 4 2 2 3 4 5 104 632 1
cert_coverFacet 5 936
cert_cover_5 5 3 2 4 6 7 296 936 2
cert_coverFacet 6 240
cert_cover_2 6 4 3 5 6 112 240 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q0_0054

end
end BundlePart20

section BundlePart21
/- Source: ProjectionCertificates/R_m14e10q0_0057.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q0_0057

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [775, 539, 179, 387, 61, 589, 421, 658, 962, 108, 868, 120, 728, 496, 19, 131, 259, 515, 13, 37, 261, 517, 25, 521, 49, 161, 385, 146, 530, 386, 642, 770, 44, 76, 100, 292, 580, 772, 56, 88, 536, 104, 584, 112, 176, 208, 656, 352, 416, 448, 704, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_775, vertices_539, vertices_179, vertices_387, vertices_61, vertices_589, vertices_421, vertices_658, vertices_962, vertices_108, vertices_868, vertices_120, vertices_728, vertices_496] (by decide +kernel)
  polygons := literalFinset [vertices_19, vertices_131, vertices_259, vertices_515, vertices_13, vertices_37, vertices_261, vertices_517, vertices_25, vertices_521, vertices_49, vertices_161, vertices_385, vertices_146, vertices_530, vertices_386, vertices_642, vertices_770, vertices_44, vertices_76, vertices_100, vertices_292, vertices_580, vertices_772, vertices_56, vertices_88, vertices_536, vertices_104, vertices_584, vertices_112, vertices_176, vertices_208, vertices_656, vertices_352, vertices_416, vertices_448, vertices_704, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_775), (false, vertices_539), (false, vertices_179), (false, vertices_387), (false, vertices_61), (false, vertices_589), (false, vertices_421), (true, vertices_642), (true, vertices_100), (true, vertices_88), (true, vertices_104), (true, vertices_112), (true, vertices_208), (true, vertices_656), (true, vertices_352), (true, vertices_448), (true, vertices_704), (true, vertices_832)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 12 16 20 21 22 23 24 25 26
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_775) then 13 else
  if p.val = (false, vertices_539) then 14 else
  if p.val = (false, vertices_179) then 15 else
  if p.val = (false, vertices_387) then 0 else
  if p.val = (false, vertices_61) then 17 else
  if p.val = (false, vertices_589) then 18 else
  if p.val = (false, vertices_421) then 19 else
  if p.val = (true, vertices_642) then 1 else
  if p.val = (true, vertices_100) then 2 else
  if p.val = (true, vertices_88) then 3 else
  if p.val = (true, vertices_104) then 4 else
  if p.val = (true, vertices_112) then 5 else
  if p.val = (true, vertices_208) then 6 else
  if p.val = (true, vertices_656) then 7 else
  if p.val = (true, vertices_352) then 8 else
  if p.val = (true, vertices_448) then 9 else
  if p.val = (true, vertices_704) then 10 else
  if p.val = (true, vertices_832) then 11 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_387), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_642), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_100), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_88), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_104), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_112), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_208), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_656), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_352), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_448), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_704), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_832), by decide +kernel⟩
  | 12 => Sum.inl 0
  | 13 => Sum.inr ⟨(false, vertices_775), by decide +kernel⟩
  | 14 => Sum.inr ⟨(false, vertices_539), by decide +kernel⟩
  | 15 => Sum.inr ⟨(false, vertices_179), by decide +kernel⟩
  | 16 => Sum.inl 1
  | 17 => Sum.inr ⟨(false, vertices_61), by decide +kernel⟩
  | 18 => Sum.inr ⟨(false, vertices_589), by decide +kernel⟩
  | 19 => Sum.inr ⟨(false, vertices_421), by decide +kernel⟩
  | 20 => Sum.inl 2
  | 21 => Sum.inl 3
  | 22 => Sum.inl 4
  | 23 => Sum.inl 5
  | 24 => Sum.inl 6
  | 25 => Sum.inl 7
  | 26 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 5 6 7 8 962 386 1
cert_row_4 1 1 4 5 7 8 868 100 3
cert_row_4 2 2 3 5 6 8 728 88 3
cert_row_4 3 3 4 5 6 7 496 112 3
cert_rows
cert_pivot_2 0 1 2 3
cert_heightProof 4
cert_coverFacet 0 658
cert_cover_2 0 3 0 6 8 146 658 3
cert_coverFacet 1 962
cert_cover_5 1 0 0 5 6 7 386 962 1
cert_coverFacet 2 108
cert_cover_2 2 2 1 4 5 44 108 3
cert_coverFacet 3 868
cert_cover_5 3 1 1 4 5 7 100 868 3
cert_coverFacet 4 120
cert_cover_2 4 3 2 4 5 56 120 3
cert_coverFacet 5 728
cert_cover_5 5 2 2 3 5 6 88 728 3
cert_coverFacet 6 496
cert_cover_5 6 3 3 4 5 6 112 496 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q0_0057

end
end BundlePart21

section BundlePart22
/- Source: ProjectionCertificates/R_m14e10q0_0058.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q0_0058

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [787, 173, 661, 613, 409, 809, 710, 218, 338, 658, 866, 228, 376, 232, 37, 133, 517, 41, 137, 265, 145, 273, 529, 545, 769, 82, 146, 274, 530, 194, 322, 578, 642, 770, 100, 164, 196, 580, 644, 88, 152, 280, 104, 168, 296, 200, 336, 656, 224, 352, 608, 800]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_787, vertices_173, vertices_661, vertices_613, vertices_409, vertices_809, vertices_710, vertices_218, vertices_338, vertices_658, vertices_866, vertices_228, vertices_376, vertices_232] (by decide +kernel)
  polygons := literalFinset [vertices_37, vertices_133, vertices_517, vertices_41, vertices_137, vertices_265, vertices_145, vertices_273, vertices_529, vertices_545, vertices_769, vertices_82, vertices_146, vertices_274, vertices_530, vertices_194, vertices_322, vertices_578, vertices_642, vertices_770, vertices_100, vertices_164, vertices_196, vertices_580, vertices_644, vertices_88, vertices_152, vertices_280, vertices_104, vertices_168, vertices_296, vertices_200, vertices_336, vertices_656, vertices_224, vertices_352, vertices_608, vertices_800] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_787), (false, vertices_173), (false, vertices_661), (false, vertices_613), (false, vertices_409), (false, vertices_809), (true, vertices_82), (true, vertices_146), (true, vertices_194), (true, vertices_322), (true, vertices_578), (true, vertices_642), (true, vertices_196), (true, vertices_88), (true, vertices_104), (true, vertices_200), (true, vertices_336), (true, vertices_224), (true, vertices_352)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 13 15 19 22 23 24 25 26 27
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_787) then 14 else
  if p.val = (false, vertices_173) then 16 else
  if p.val = (false, vertices_661) then 17 else
  if p.val = (false, vertices_613) then 18 else
  if p.val = (false, vertices_409) then 20 else
  if p.val = (false, vertices_809) then 21 else
  if p.val = (true, vertices_82) then 0 else
  if p.val = (true, vertices_146) then 1 else
  if p.val = (true, vertices_194) then 2 else
  if p.val = (true, vertices_322) then 3 else
  if p.val = (true, vertices_578) then 4 else
  if p.val = (true, vertices_642) then 5 else
  if p.val = (true, vertices_196) then 6 else
  if p.val = (true, vertices_88) then 7 else
  if p.val = (true, vertices_104) then 8 else
  if p.val = (true, vertices_200) then 9 else
  if p.val = (true, vertices_336) then 10 else
  if p.val = (true, vertices_224) then 11 else
  if p.val = (true, vertices_352) then 12 else
  0
cert_priority
cert_nodeAtPriority 0 82 1 146 2 194 322 578 642 196 88 104 200 336 224 352 787 173 661 613 409 809
cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 5 6 8 710 194 1
cert_row_4 1 0 2 3 5 6 218 82 1
cert_row_4 2 0 4 5 7 8 866 322 1
cert_row_4 3 2 3 4 5 7 376 88 2
cert_rows
cert_pivot_2 1 6 0 2
cert_heightProof 4
cert_coverFacet 0 710
cert_cover_5 0 0 0 1 5 6 194 710 1
cert_coverFacet 1 218
cert_cover_5 1 1 0 2 3 5 82 218 1
cert_coverFacet 2 338
cert_cover_2 2 3 0 5 7 82 338 3
cert_coverFacet 3 658
cert_cover_2 3 3 0 6 8 146 658 3
cert_coverFacet 4 866
cert_cover_5 4 2 0 4 5 7 322 866 1
cert_coverFacet 5 228
cert_cover_2 5 4 1 5 6 100 228 3
cert_coverFacet 6 376
cert_cover_5 6 3 2 3 4 5 88 376 2
cert_coverFacet 7 232
cert_cover_2 7 4 2 5 6 104 232 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q0_0058

end
end BundlePart22

section BundlePart23
/- Source: ProjectionCertificates/R_m14e10q0_0063.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q0_0063

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [155, 51, 803, 451, 61, 205, 357, 566, 914, 604, 612, 664, 712, 992, 19, 35, 131, 259, 13, 37, 69, 25, 137, 49, 289, 193, 321, 50, 146, 530, 546, 386, 770, 28, 76, 52, 532, 100, 548, 580, 152, 536, 200, 584, 648, 656, 352, 608, 800, 448, 704, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_155, vertices_51, vertices_803, vertices_451, vertices_61, vertices_205, vertices_357, vertices_566, vertices_914, vertices_604, vertices_612, vertices_664, vertices_712, vertices_992] (by decide +kernel)
  polygons := literalFinset [vertices_19, vertices_35, vertices_131, vertices_259, vertices_13, vertices_37, vertices_69, vertices_25, vertices_137, vertices_49, vertices_289, vertices_193, vertices_321, vertices_50, vertices_146, vertices_530, vertices_546, vertices_386, vertices_770, vertices_28, vertices_76, vertices_52, vertices_532, vertices_100, vertices_548, vertices_580, vertices_152, vertices_536, vertices_200, vertices_584, vertices_648, vertices_656, vertices_352, vertices_608, vertices_800, vertices_448, vertices_704, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_155), (false, vertices_51), (false, vertices_803), (false, vertices_451), (false, vertices_61), (false, vertices_205), (false, vertices_357), (true, vertices_530), (true, vertices_532), (true, vertices_548), (true, vertices_580), (true, vertices_536), (true, vertices_584), (true, vertices_648), (true, vertices_656), (true, vertices_608), (true, vertices_704), (true, vertices_896)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 12 16 20 21 22 23 24 25 26
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_155) then 13 else
  if p.val = (false, vertices_51) then 0 else
  if p.val = (false, vertices_803) then 14 else
  if p.val = (false, vertices_451) then 15 else
  if p.val = (false, vertices_61) then 17 else
  if p.val = (false, vertices_205) then 18 else
  if p.val = (false, vertices_357) then 19 else
  if p.val = (true, vertices_530) then 1 else
  if p.val = (true, vertices_532) then 2 else
  if p.val = (true, vertices_548) then 3 else
  if p.val = (true, vertices_580) then 4 else
  if p.val = (true, vertices_536) then 5 else
  if p.val = (true, vertices_584) then 6 else
  if p.val = (true, vertices_648) then 7 else
  if p.val = (true, vertices_656) then 8 else
  if p.val = (true, vertices_608) then 9 else
  if p.val = (true, vertices_704) then 10 else
  if p.val = (true, vertices_896) then 11 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_51), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_530), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_532), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_548), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_580), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_536), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_584), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_648), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_656), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_608), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_704), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_896), by decide +kernel⟩
  | 12 => Sum.inl 0
  | 13 => Sum.inr ⟨(false, vertices_155), by decide +kernel⟩
  | 14 => Sum.inr ⟨(false, vertices_803), by decide +kernel⟩
  | 15 => Sum.inr ⟨(false, vertices_451), by decide +kernel⟩
  | 16 => Sum.inl 1
  | 17 => Sum.inr ⟨(false, vertices_61), by decide +kernel⟩
  | 18 => Sum.inr ⟨(false, vertices_205), by decide +kernel⟩
  | 19 => Sum.inr ⟨(false, vertices_357), by decide +kernel⟩
  | 20 => Sum.inl 2
  | 21 => Sum.inl 3
  | 22 => Sum.inl 4
  | 23 => Sum.inl 5
  | 24 => Sum.inl 6
  | 25 => Sum.inl 7
  | 26 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 1 2 3 5 8 604 28 3
cert_row_4 1 0 1 3 4 8 566 50 1
cert_row_4 2 0 3 6 7 8 914 146 3
cert_row_4 3 4 5 6 7 8 992 352 2
cert_rows
cert_pivot_2 2 1 0 4
cert_heightProof 4
cert_coverFacet 0 566
cert_cover_5 0 1 0 1 3 4 50 566 1
cert_coverFacet 1 914
cert_cover_5 1 2 0 3 6 7 146 914 3
cert_coverFacet 2 604
cert_cover_5 2 0 1 2 3 5 28 604 3
cert_coverFacet 3 612
cert_cover_2 3 4 1 5 8 100 612 3
cert_coverFacet 4 664
cert_cover_2 4 3 2 6 8 152 664 3
cert_coverFacet 5 712
cert_cover_2 5 5 2 6 8 200 712 3
cert_coverFacet 6 992
cert_cover_5 6 3 4 5 6 7 352 992 2
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q0_0063

end
end BundlePart23

section BundlePart24
/- Source: ProjectionCertificates/R_m14e10q0_0064.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q0_0064

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [775, 653, 421, 233, 841, 369, 662, 390, 186, 306, 850, 418, 632, 664, 133, 261, 517, 73, 137, 521, 97, 161, 289, 321, 769, 134, 262, 518, 50, 146, 274, 530, 162, 290, 386, 770, 388, 644, 56, 152, 536, 104, 168, 584, 648, 112, 304, 336, 592, 656, 416, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_775, vertices_653, vertices_421, vertices_233, vertices_841, vertices_369, vertices_662, vertices_390, vertices_186, vertices_306, vertices_850, vertices_418, vertices_632, vertices_664] (by decide +kernel)
  polygons := literalFinset [vertices_133, vertices_261, vertices_517, vertices_73, vertices_137, vertices_521, vertices_97, vertices_161, vertices_289, vertices_321, vertices_769, vertices_134, vertices_262, vertices_518, vertices_50, vertices_146, vertices_274, vertices_530, vertices_162, vertices_290, vertices_386, vertices_770, vertices_388, vertices_644, vertices_56, vertices_152, vertices_536, vertices_104, vertices_168, vertices_584, vertices_648, vertices_112, vertices_304, vertices_336, vertices_592, vertices_656, vertices_416, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_775), (false, vertices_653), (false, vertices_421), (false, vertices_233), (false, vertices_841), (false, vertices_369), (true, vertices_134), (true, vertices_50), (true, vertices_146), (true, vertices_274), (true, vertices_530), (true, vertices_162), (true, vertices_290), (true, vertices_386), (true, vertices_56), (true, vertices_152), (true, vertices_536), (true, vertices_592), (true, vertices_656)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 13 15 18 21 23 24 25 26 27
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_775) then 14 else
  if p.val = (false, vertices_653) then 16 else
  if p.val = (false, vertices_421) then 17 else
  if p.val = (false, vertices_233) then 19 else
  if p.val = (false, vertices_841) then 20 else
  if p.val = (false, vertices_369) then 22 else
  if p.val = (true, vertices_134) then 0 else
  if p.val = (true, vertices_50) then 1 else
  if p.val = (true, vertices_146) then 2 else
  if p.val = (true, vertices_274) then 3 else
  if p.val = (true, vertices_530) then 4 else
  if p.val = (true, vertices_162) then 5 else
  if p.val = (true, vertices_290) then 6 else
  if p.val = (true, vertices_386) then 7 else
  if p.val = (true, vertices_56) then 8 else
  if p.val = (true, vertices_152) then 9 else
  if p.val = (true, vertices_536) then 10 else
  if p.val = (true, vertices_592) then 11 else
  if p.val = (true, vertices_656) then 12 else
  0
cert_priority
cert_nodeAtPriority_12 134 1 50 2 146 274 530 162 290 386 56 152 536 592 656 775 653 421 233 841 369
cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 3 6 8 662 134 2
cert_row_4 1 0 2 3 4 6 186 50 1
cert_row_4 2 0 3 5 7 8 850 274 2
cert_row_4 3 2 3 4 5 8 632 56 3
cert_rows
cert_pivot_2 1 6 0 2
cert_heightProof 4
cert_coverFacet 0 662
cert_cover_5 0 0 0 1 3 6 134 662 2
cert_coverFacet 1 390
cert_cover_2 1 1 0 6 7 134 390 3
cert_coverFacet 2 186
cert_cover_5 2 1 0 2 3 4 50 186 1
cert_coverFacet 3 306
cert_cover_2 3 3 0 4 7 50 306 3
cert_coverFacet 4 850
cert_cover_5 4 2 0 3 5 7 274 850 2
cert_coverFacet 5 418
cert_cover_2 5 4 0 6 7 162 418 3
cert_coverFacet 6 632
cert_cover_5 6 3 2 3 4 5 56 632 3
cert_coverFacet 7 664
cert_cover_2 7 3 2 6 8 152 664 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q0_0064

end
end BundlePart24

section BundlePart25
/- Source: ProjectionCertificates/R_m14e10q0_0067.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q0_0067

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [835, 61, 653, 805, 601, 369, 902, 666, 242, 594, 450, 172, 484, 184, 13, 37, 517, 25, 521, 49, 81, 289, 321, 577, 769, 82, 146, 530, 194, 322, 578, 386, 642, 770, 44, 140, 164, 292, 388, 644, 772, 56, 152, 536, 168, 648, 112, 176, 592, 224, 352, 448]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_835, vertices_61, vertices_653, vertices_805, vertices_601, vertices_369, vertices_902, vertices_666, vertices_242, vertices_594, vertices_450, vertices_172, vertices_484, vertices_184] (by decide +kernel)
  polygons := literalFinset [vertices_13, vertices_37, vertices_517, vertices_25, vertices_521, vertices_49, vertices_81, vertices_289, vertices_321, vertices_577, vertices_769, vertices_82, vertices_146, vertices_530, vertices_194, vertices_322, vertices_578, vertices_386, vertices_642, vertices_770, vertices_44, vertices_140, vertices_164, vertices_292, vertices_388, vertices_644, vertices_772, vertices_56, vertices_152, vertices_536, vertices_168, vertices_648, vertices_112, vertices_176, vertices_592, vertices_224, vertices_352, vertices_448] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_835), (false, vertices_61), (false, vertices_653), (false, vertices_805), (false, vertices_601), (false, vertices_369), (true, vertices_82), (true, vertices_146), (true, vertices_530), (true, vertices_194), (true, vertices_386), (true, vertices_642), (true, vertices_164), (true, vertices_388), (true, vertices_152), (true, vertices_168), (true, vertices_176), (true, vertices_224), (true, vertices_448)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 13 15 19 21 23 24 25 26 27
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_835) then 14 else
  if p.val = (false, vertices_61) then 16 else
  if p.val = (false, vertices_653) then 17 else
  if p.val = (false, vertices_805) then 18 else
  if p.val = (false, vertices_601) then 20 else
  if p.val = (false, vertices_369) then 22 else
  if p.val = (true, vertices_82) then 0 else
  if p.val = (true, vertices_146) then 1 else
  if p.val = (true, vertices_530) then 2 else
  if p.val = (true, vertices_194) then 3 else
  if p.val = (true, vertices_386) then 4 else
  if p.val = (true, vertices_642) then 5 else
  if p.val = (true, vertices_164) then 6 else
  if p.val = (true, vertices_388) then 7 else
  if p.val = (true, vertices_152) then 8 else
  if p.val = (true, vertices_168) then 9 else
  if p.val = (true, vertices_176) then 10 else
  if p.val = (true, vertices_224) then 11 else
  if p.val = (true, vertices_448) then 12 else
  0
cert_priority
cert_nodeAtPriority_11 82 146 530 194 386 642 164 388 152 168 176 224 448 835 61 653 805 601 369
cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 2 3 6 8 666 146 1
cert_row_4 1 0 1 6 7 8 902 386 1
cert_row_4 2 0 3 4 5 6 242 82 2
cert_row_4 3 1 4 5 6 7 484 164 2
cert_rows
cert_pivot_2 2 8 0 1
cert_heightProof 4
cert_coverFacet 0 902
cert_cover_5 0 1 0 1 6 7 386 902 1
cert_coverFacet 1 666
cert_cover_5 1 0 0 2 3 6 146 666 1
cert_coverFacet 2 242
cert_cover_5 2 2 0 3 4 5 82 242 2
cert_coverFacet 3 594
cert_cover_2 3 3 0 5 8 82 594 3
cert_coverFacet 4 450
cert_cover_2 4 5 0 6 7 194 450 3
cert_coverFacet 5 172
cert_cover_2 5 2 1 4 6 44 172 3
cert_coverFacet 6 484
cert_cover_5 6 3 1 4 5 6 164 484 2
cert_coverFacet 7 184
cert_cover_2 7 3 2 4 6 56 184 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q0_0067

end
end BundlePart25

section BundlePart26
/- Source: ProjectionCertificates/R_m14e10q0_0068.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q0_0068

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [647, 155, 275, 835, 205, 613, 345, 818, 658, 692, 228, 440, 232, 872, 19, 131, 259, 515, 69, 133, 517, 25, 73, 137, 273, 321, 577, 146, 274, 530, 642, 770, 100, 164, 548, 196, 644, 152, 280, 104, 168, 296, 200, 328, 176, 304, 560, 656, 224, 608, 800, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_647, vertices_155, vertices_275, vertices_835, vertices_205, vertices_613, vertices_345, vertices_818, vertices_658, vertices_692, vertices_228, vertices_440, vertices_232, vertices_872] (by decide +kernel)
  polygons := literalFinset [vertices_19, vertices_131, vertices_259, vertices_515, vertices_69, vertices_133, vertices_517, vertices_25, vertices_73, vertices_137, vertices_273, vertices_321, vertices_577, vertices_146, vertices_274, vertices_530, vertices_642, vertices_770, vertices_100, vertices_164, vertices_548, vertices_196, vertices_644, vertices_152, vertices_280, vertices_104, vertices_168, vertices_296, vertices_200, vertices_328, vertices_176, vertices_304, vertices_560, vertices_656, vertices_224, vertices_608, vertices_800, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_647), (false, vertices_155), (false, vertices_275), (false, vertices_835), (false, vertices_205), (false, vertices_613), (false, vertices_345), (true, vertices_530), (true, vertices_164), (true, vertices_104), (true, vertices_168), (true, vertices_296), (true, vertices_176), (true, vertices_304), (true, vertices_560), (true, vertices_656), (true, vertices_224), (true, vertices_800)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 12 16 19 21 22 23 24 25 26
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_647) then 13 else
  if p.val = (false, vertices_155) then 14 else
  if p.val = (false, vertices_275) then 0 else
  if p.val = (false, vertices_835) then 15 else
  if p.val = (false, vertices_205) then 17 else
  if p.val = (false, vertices_613) then 18 else
  if p.val = (false, vertices_345) then 20 else
  if p.val = (true, vertices_530) then 1 else
  if p.val = (true, vertices_164) then 2 else
  if p.val = (true, vertices_104) then 3 else
  if p.val = (true, vertices_168) then 4 else
  if p.val = (true, vertices_296) then 5 else
  if p.val = (true, vertices_176) then 6 else
  if p.val = (true, vertices_304) then 7 else
  if p.val = (true, vertices_560) then 8 else
  if p.val = (true, vertices_656) then 9 else
  if p.val = (true, vertices_224) then 10 else
  if p.val = (true, vertices_800) then 11 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_275), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_530), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_164), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_104), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_168), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_296), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_176), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_304), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_560), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_656), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_224), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_800), by decide +kernel⟩
  | 12 => Sum.inl 0
  | 13 => Sum.inr ⟨(false, vertices_647), by decide +kernel⟩
  | 14 => Sum.inr ⟨(false, vertices_155), by decide +kernel⟩
  | 15 => Sum.inr ⟨(false, vertices_835), by decide +kernel⟩
  | 16 => Sum.inl 1
  | 17 => Sum.inr ⟨(false, vertices_205), by decide +kernel⟩
  | 18 => Sum.inr ⟨(false, vertices_613), by decide +kernel⟩
  | 19 => Sum.inl 2
  | 20 => Sum.inr ⟨(false, vertices_345), by decide +kernel⟩
  | 21 => Sum.inl 3
  | 22 => Sum.inl 4
  | 23 => Sum.inl 5
  | 24 => Sum.inl 6
  | 25 => Sum.inl 7
  | 26 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 3 4 7 8 818 274 2
cert_row_4 1 1 3 4 6 8 692 164 1
cert_row_4 2 2 3 4 6 7 440 152 2
cert_row_4 3 2 4 5 7 8 872 104 3
cert_rows
cert_pivot_2 0 1 3 2
cert_heightProof 4
cert_coverFacet 0 818
cert_cover_5 0 0 0 3 4 7 274 818 2
cert_coverFacet 1 658
cert_cover_2 1 3 0 6 8 146 658 3
cert_coverFacet 2 692
cert_cover_5 2 1 1 3 4 6 164 692 1
cert_coverFacet 3 228
cert_cover_2 3 4 1 5 6 100 228 3
cert_coverFacet 4 440
cert_cover_5 4 2 2 3 4 6 152 440 2
cert_coverFacet 5 232
cert_cover_2 5 4 2 5 6 104 232 3
cert_coverFacet 6 872
cert_cover_5 6 3 2 4 5 7 104 872 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q0_0068

end
end BundlePart26

section BundlePart27
/- Source: ProjectionCertificates/R_m14e10q0_0069.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q0_0069

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [675, 93, 653, 837, 185, 625, 782, 410, 650, 866, 418, 284, 372, 432, 13, 69, 517, 25, 137, 49, 81, 161, 545, 577, 641, 138, 266, 522, 162, 290, 546, 386, 642, 770, 28, 268, 524, 84, 276, 324, 772, 152, 280, 648, 112, 176, 304, 400, 352, 608, 416, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_675, vertices_93, vertices_653, vertices_837, vertices_185, vertices_625, vertices_782, vertices_410, vertices_650, vertices_866, vertices_418, vertices_284, vertices_372, vertices_432] (by decide +kernel)
  polygons := literalFinset [vertices_13, vertices_69, vertices_517, vertices_25, vertices_137, vertices_49, vertices_81, vertices_161, vertices_545, vertices_577, vertices_641, vertices_138, vertices_266, vertices_522, vertices_162, vertices_290, vertices_546, vertices_386, vertices_642, vertices_770, vertices_28, vertices_268, vertices_524, vertices_84, vertices_276, vertices_324, vertices_772, vertices_152, vertices_280, vertices_648, vertices_112, vertices_176, vertices_304, vertices_400, vertices_352, vertices_608, vertices_416, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_675), (false, vertices_93), (false, vertices_653), (false, vertices_837), (false, vertices_185), (false, vertices_625), (true, vertices_138), (true, vertices_266), (true, vertices_522), (true, vertices_290), (true, vertices_386), (true, vertices_770), (true, vertices_268), (true, vertices_276), (true, vertices_280), (true, vertices_304), (true, vertices_400), (true, vertices_352), (true, vertices_416)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 13 15 19 21 23 24 25 26 27
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_675) then 14 else
  if p.val = (false, vertices_93) then 16 else
  if p.val = (false, vertices_653) then 17 else
  if p.val = (false, vertices_837) then 18 else
  if p.val = (false, vertices_185) then 20 else
  if p.val = (false, vertices_625) then 22 else
  if p.val = (true, vertices_138) then 0 else
  if p.val = (true, vertices_266) then 1 else
  if p.val = (true, vertices_522) then 2 else
  if p.val = (true, vertices_290) then 3 else
  if p.val = (true, vertices_386) then 4 else
  if p.val = (true, vertices_770) then 5 else
  if p.val = (true, vertices_268) then 6 else
  if p.val = (true, vertices_276) then 7 else
  if p.val = (true, vertices_280) then 8 else
  if p.val = (true, vertices_304) then 9 else
  if p.val = (true, vertices_400) then 10 else
  if p.val = (true, vertices_352) then 11 else
  if p.val = (true, vertices_416) then 12 else
  0
cert_priority
cert_nodeAtPriority_11 138 266 522 290 386 770 268 276 280 304 400 352 416 675 93 653 837 185 625
cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 2 3 6 7 410 138 2
cert_row_4 1 0 1 2 7 8 782 266 1
cert_row_4 2 0 4 5 7 8 866 290 2
cert_row_4 3 1 3 4 5 7 372 84 2
cert_rows
cert_pivot_2 6 2 0 1
cert_heightProof 4
cert_coverFacet 0 782
cert_cover_5 0 1 0 1 2 7 266 782 1
cert_coverFacet 1 410
cert_cover_5 1 0 0 2 3 6 138 410 2
cert_coverFacet 2 650
cert_cover_2 2 2 0 6 8 138 650 3
cert_coverFacet 3 866
cert_cover_5 3 2 0 4 5 7 290 866 2
cert_coverFacet 4 418
cert_cover_2 4 4 0 6 7 162 418 3
cert_coverFacet 5 284
cert_cover_2 5 2 1 3 7 28 284 3
cert_coverFacet 6 372
cert_cover_5 6 3 1 3 4 5 84 372 2
cert_coverFacet 7 432
cert_cover_2 7 4 3 6 7 176 432 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q0_0069

end
end BundlePart27

section BundlePart28
/- Source: ProjectionCertificates/R_m14e10q0_0070.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q0_0070

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [307, 659, 611, 357, 409, 961, 558, 282, 538, 298, 668, 300, 460, 740, 19, 35, 515, 145, 273, 97, 289, 321, 577, 385, 641, 26, 42, 266, 522, 274, 530, 290, 546, 44, 140, 268, 524, 100, 292, 548, 196, 324, 644, 152, 280, 536, 296, 392, 656, 608, 448, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_307, vertices_659, vertices_611, vertices_357, vertices_409, vertices_961, vertices_558, vertices_282, vertices_538, vertices_298, vertices_668, vertices_300, vertices_460, vertices_740] (by decide +kernel)
  polygons := literalFinset [vertices_19, vertices_35, vertices_515, vertices_145, vertices_273, vertices_97, vertices_289, vertices_321, vertices_577, vertices_385, vertices_641, vertices_26, vertices_42, vertices_266, vertices_522, vertices_274, vertices_530, vertices_290, vertices_546, vertices_44, vertices_140, vertices_268, vertices_524, vertices_100, vertices_292, vertices_548, vertices_196, vertices_324, vertices_644, vertices_152, vertices_280, vertices_536, vertices_296, vertices_392, vertices_656, vertices_608, vertices_448, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_307), (false, vertices_659), (false, vertices_611), (false, vertices_357), (false, vertices_409), (false, vertices_961), (true, vertices_26), (true, vertices_42), (true, vertices_266), (true, vertices_522), (true, vertices_44), (true, vertices_140), (true, vertices_268), (true, vertices_524), (true, vertices_548), (true, vertices_196), (true, vertices_644), (true, vertices_536), (true, vertices_296)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 13 17 19 21 22 23 25 26 27
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_307) then 14 else
  if p.val = (false, vertices_659) then 15 else
  if p.val = (false, vertices_611) then 16 else
  if p.val = (false, vertices_357) then 18 else
  if p.val = (false, vertices_409) then 20 else
  if p.val = (false, vertices_961) then 24 else
  if p.val = (true, vertices_26) then 0 else
  if p.val = (true, vertices_42) then 1 else
  if p.val = (true, vertices_266) then 2 else
  if p.val = (true, vertices_522) then 3 else
  if p.val = (true, vertices_44) then 4 else
  if p.val = (true, vertices_140) then 5 else
  if p.val = (true, vertices_268) then 6 else
  if p.val = (true, vertices_524) then 7 else
  if p.val = (true, vertices_548) then 8 else
  if p.val = (true, vertices_196) then 9 else
  if p.val = (true, vertices_644) then 10 else
  if p.val = (true, vertices_536) then 11 else
  if p.val = (true, vertices_296) then 12 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_26), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_42), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_266), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_522), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_44), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_140), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_268), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_524), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_548), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_196), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_644), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_536), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_296), by decide +kernel⟩
  | 13 => Sum.inl 0
  | 14 => Sum.inr ⟨(false, vertices_307), by decide +kernel⟩
  | 15 => Sum.inr ⟨(false, vertices_659), by decide +kernel⟩
  | 16 => Sum.inr ⟨(false, vertices_611), by decide +kernel⟩
  | 17 => Sum.inl 1
  | 18 => Sum.inr ⟨(false, vertices_357), by decide +kernel⟩
  | 19 => Sum.inl 2
  | 20 => Sum.inr ⟨(false, vertices_409), by decide +kernel⟩
  | 21 => Sum.inl 3
  | 22 => Sum.inl 4
  | 23 => Sum.inl 5
  | 24 => Sum.inr ⟨(false, vertices_961), by decide +kernel⟩
  | 25 => Sum.inl 6
  | 26 => Sum.inl 7
  | 27 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 2 4 8 558 42 1
cert_row_4 1 1 2 3 6 8 668 140 2
cert_row_4 2 1 2 5 6 7 460 140 2
cert_row_4 3 1 4 5 6 8 740 100 3
cert_rows
cert_pivot_2 0 3 2 1
cert_heightProof 4
cert_coverFacet 0 558
cert_cover_5 0 0 0 1 2 4 42 558 1
cert_coverFacet 1 282
cert_cover_2 1 2 0 3 7 26 282 3
cert_coverFacet 2 538
cert_cover_2 2 2 0 3 8 26 538 3
cert_coverFacet 3 298
cert_cover_2 3 2 0 4 7 42 298 3
cert_coverFacet 4 668
cert_cover_5 4 1 1 2 3 6 140 668 2
cert_coverFacet 5 300
cert_cover_2 5 2 1 4 7 44 300 3
cert_coverFacet 6 460
cert_cover_5 6 2 1 2 5 6 140 460 2
cert_coverFacet 7 740
cert_cover_5 7 3 1 4 5 6 100 740 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q0_0070

end
end BundlePart28

section BundlePart29
/- Source: ProjectionCertificates/R_m14e10q0_0071.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q0_0071

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [115, 403, 707, 109, 653, 581, 185, 838, 906, 338, 812, 372, 424, 432, 19, 67, 131, 13, 69, 517, 41, 137, 49, 145, 97, 577, 641, 82, 274, 322, 578, 386, 642, 770, 44, 524, 100, 292, 324, 580, 772, 168, 296, 392, 648, 776, 112, 176, 304, 336, 400, 416]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_115, vertices_403, vertices_707, vertices_109, vertices_653, vertices_581, vertices_185, vertices_838, vertices_906, vertices_338, vertices_812, vertices_372, vertices_424, vertices_432] (by decide +kernel)
  polygons := literalFinset [vertices_19, vertices_67, vertices_131, vertices_13, vertices_69, vertices_517, vertices_41, vertices_137, vertices_49, vertices_145, vertices_97, vertices_577, vertices_641, vertices_82, vertices_274, vertices_322, vertices_578, vertices_386, vertices_642, vertices_770, vertices_44, vertices_524, vertices_100, vertices_292, vertices_324, vertices_580, vertices_772, vertices_168, vertices_296, vertices_392, vertices_648, vertices_776, vertices_112, vertices_176, vertices_304, vertices_336, vertices_400, vertices_416] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_115), (false, vertices_403), (false, vertices_707), (false, vertices_109), (false, vertices_653), (false, vertices_581), (false, vertices_185), (true, vertices_322), (true, vertices_770), (true, vertices_292), (true, vertices_324), (true, vertices_772), (true, vertices_296), (true, vertices_392), (true, vertices_776), (true, vertices_304), (true, vertices_336), (true, vertices_416)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 12 16 19 21 22 23 24 25 26
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_115) then 13 else
  if p.val = (false, vertices_403) then 14 else
  if p.val = (false, vertices_707) then 15 else
  if p.val = (false, vertices_109) then 17 else
  if p.val = (false, vertices_653) then 18 else
  if p.val = (false, vertices_581) then 0 else
  if p.val = (false, vertices_185) then 20 else
  if p.val = (true, vertices_322) then 1 else
  if p.val = (true, vertices_770) then 2 else
  if p.val = (true, vertices_292) then 3 else
  if p.val = (true, vertices_324) then 4 else
  if p.val = (true, vertices_772) then 5 else
  if p.val = (true, vertices_296) then 6 else
  if p.val = (true, vertices_392) then 7 else
  if p.val = (true, vertices_776) then 8 else
  if p.val = (true, vertices_304) then 9 else
  if p.val = (true, vertices_336) then 10 else
  if p.val = (true, vertices_416) then 11 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_581), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_322), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_770), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_292), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_324), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_772), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_296), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_392), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_776), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_304), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_336), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_416), by decide +kernel⟩
  | 12 => Sum.inl 0
  | 13 => Sum.inr ⟨(false, vertices_115), by decide +kernel⟩
  | 14 => Sum.inr ⟨(false, vertices_403), by decide +kernel⟩
  | 15 => Sum.inr ⟨(false, vertices_707), by decide +kernel⟩
  | 16 => Sum.inl 1
  | 17 => Sum.inr ⟨(false, vertices_109), by decide +kernel⟩
  | 18 => Sum.inr ⟨(false, vertices_653), by decide +kernel⟩
  | 19 => Sum.inl 2
  | 20 => Sum.inr ⟨(false, vertices_185), by decide +kernel⟩
  | 21 => Sum.inl 3
  | 22 => Sum.inl 4
  | 23 => Sum.inl 5
  | 24 => Sum.inl 6
  | 25 => Sum.inl 7
  | 26 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 2 6 7 8 906 386 1
cert_row_4 1 0 1 5 7 8 838 322 1
cert_row_4 2 1 2 4 7 8 812 44 3
cert_row_4 3 1 3 4 5 7 372 100 1
cert_rows
cert_pivot_2 6 0 2 1
cert_heightProof 4
cert_coverFacet 0 838
cert_cover_5 0 1 0 1 5 7 322 838 1
cert_coverFacet 1 906
cert_cover_5 1 0 0 2 6 7 386 906 1
cert_coverFacet 2 338
cert_cover_2 2 3 0 5 7 82 338 3
cert_coverFacet 3 812
cert_cover_5 3 2 1 2 4 7 44 812 3
cert_coverFacet 4 372
cert_cover_5 4 3 1 3 4 5 100 372 1
cert_coverFacet 5 424
cert_cover_2 5 4 2 6 7 168 424 3
cert_coverFacet 6 432
cert_cover_2 6 4 3 6 7 176 432 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q0_0071

end
end BundlePart29
-- Explicit facial frame witnesses.

-- Public target certificates; internal witness data stays private.
namespace Nonrational.TerminalVerification
open Papers.RationalityTen.ChirotopeDensity.FiniteProjection
open Nonrational.TerminalData
set_option maxRecDepth 100000
set_option maxHeartbeats 0

public theorem projection_0210 : Certifies 210 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q0_0009.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0211 : Certifies 211 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q0_0011.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0212 : Certifies 212 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q0_0012.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0213 : Certifies 213 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q0_0013.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0214 : Certifies 214 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q0_0023.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0215 : Certifies 215 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q0_0024.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0216 : Certifies 216 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q0_0029.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0217 : Certifies 217 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q0_0032.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0218 : Certifies 218 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q0_0033.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0219 : Certifies 219 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q0_0034.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0220 : Certifies 220 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q0_0035.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0221 : Certifies 221 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q0_0036.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0222 : Certifies 222 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q0_0037.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0223 : Certifies 223 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q0_0040.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0224 : Certifies 224 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q0_0041.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0225 : Certifies 225 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q0_0042.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0226 : Certifies 226 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q0_0045.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0227 : Certifies 227 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q0_0046.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0228 : Certifies 228 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q0_0051.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0229 : Certifies 229 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q0_0052.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0230 : Certifies 230 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q0_0054.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0231 : Certifies 231 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q0_0057.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0232 : Certifies 232 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q0_0058.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0233 : Certifies 233 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q0_0063.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0234 : Certifies 234 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q0_0064.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0235 : Certifies 235 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q0_0067.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0236 : Certifies 236 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q0_0068.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0237 : Certifies 237 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q0_0069.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0238 : Certifies 238 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q0_0070.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0239 : Certifies 239 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q0_0071.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem certified_B007 (j : Fin 30) :
    Certifies (210 + j.val) := by
  fin_cases j
  · exact projection_0210
  · exact projection_0211
  · exact projection_0212
  · exact projection_0213
  · exact projection_0214
  · exact projection_0215
  · exact projection_0216
  · exact projection_0217
  · exact projection_0218
  · exact projection_0219
  · exact projection_0220
  · exact projection_0221
  · exact projection_0222
  · exact projection_0223
  · exact projection_0224
  · exact projection_0225
  · exact projection_0226
  · exact projection_0227
  · exact projection_0228
  · exact projection_0229
  · exact projection_0230
  · exact projection_0231
  · exact projection_0232
  · exact projection_0233
  · exact projection_0234
  · exact projection_0235
  · exact projection_0236
  · exact projection_0237
  · exact projection_0238
  · exact projection_0239

end Nonrational.TerminalVerification
