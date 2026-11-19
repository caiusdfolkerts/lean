module
public meta import LowerSchemas.Batches
public meta import ProjectionVertexSets
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Tactic.FinCases
public import Papers.FiniteProjectionChecks

@[expose] public section
set_option debug.skipKernelTC false

section BundlePart0
/- Source: ProjectionCertificates/P0_073.lean -/





@[expose] public section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_073

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [659, 803, 451, 213, 841, 593, 678, 418, 604, 236, 812, 660, 488, 131, 259, 515, 81, 145, 529, 193, 321, 577, 769, 162, 290, 546, 386, 642, 44, 76, 524, 84, 148, 532, 164, 548, 196, 644, 232, 296, 328, 584, 776, 592, 656, 416, 800, 448]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_659, vertices_803, vertices_451, vertices_213, vertices_841, vertices_593, vertices_678, vertices_418, vertices_604, vertices_236, vertices_812, vertices_660, vertices_488] (by decide +kernel)
  polygons := literalFinset [vertices_131, vertices_259, vertices_515, vertices_81, vertices_145, vertices_529, vertices_193, vertices_321, vertices_577, vertices_769, vertices_162, vertices_290, vertices_546, vertices_386, vertices_642, vertices_44, vertices_76, vertices_524, vertices_84, vertices_148, vertices_532, vertices_164, vertices_548, vertices_196, vertices_644, vertices_232, vertices_296, vertices_328, vertices_584, vertices_776, vertices_592, vertices_656, vertices_416, vertices_800, vertices_448] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_659), (false, vertices_803), (false, vertices_451), (false, vertices_213), (false, vertices_841), (false, vertices_593), (true, vertices_162), (true, vertices_44), (true, vertices_76), (true, vertices_524), (true, vertices_532), (true, vertices_164), (true, vertices_548), (true, vertices_644), (true, vertices_232), (true, vertices_296), (true, vertices_416)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 11 15 17 20 21 22 23 24 25
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_659) then 12 else
  if p.val = (false, vertices_803) then 13 else
  if p.val = (false, vertices_451) then 14 else
  if p.val = (false, vertices_213) then 16 else
  if p.val = (false, vertices_841) then 18 else
  if p.val = (false, vertices_593) then 10 else
  if p.val = (true, vertices_162) then 0 else
  if p.val = (true, vertices_44) then 1 else
  if p.val = (true, vertices_76) then 2 else
  if p.val = (true, vertices_524) then 3 else
  if p.val = (true, vertices_532) then 4 else
  if p.val = (true, vertices_164) then 5 else
  if p.val = (true, vertices_548) then 6 else
  if p.val = (true, vertices_644) then 7 else
  if p.val = (true, vertices_232) then 19 else
  if p.val = (true, vertices_296) then 8 else
  if p.val = (true, vertices_416) then 9 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_162), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_44), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_76), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_524), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_532), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_164), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_548), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_644), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_296), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_416), by decide +kernel⟩
  | 10 => Sum.inr ⟨(false, vertices_593), by decide +kernel⟩
  | 11 => Sum.inl 0
  | 12 => Sum.inr ⟨(false, vertices_659), by decide +kernel⟩
  | 13 => Sum.inr ⟨(false, vertices_803), by decide +kernel⟩
  | 14 => Sum.inr ⟨(false, vertices_451), by decide +kernel⟩
  | 15 => Sum.inl 1
  | 16 => Sum.inr ⟨(false, vertices_213), by decide +kernel⟩
  | 17 => Sum.inl 2
  | 18 => Sum.inr ⟨(false, vertices_841), by decide +kernel⟩
  | 19 => Sum.inr ⟨(true, vertices_232), by decide +kernel⟩
  | 20 => Sum.inl 3
  | 21 => Sum.inl 4
  | 22 => Sum.inl 5
  | 23 => Sum.inl 6
  | 24 => Sum.inl 7
  | 25 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row 0 0 1 4 6 8 678
cert_row 1 3 1 2 5 8 604
cert_row 2 1 2 4 7 8 812
cert_row_3 3 5 4 6 2 232
cert_rows
cert_pivot_2 0 3 1 2
cert_heightProof 4
cert_coverFacet 0 678
cert_cover_3 0 0 0 1 4 6
cert_coverFacet 1 418
cert_cover_4 1 0 4 6 7
cert_coverFacet 2 604
cert_cover_3 2 1 1 2 3 5
cert_coverFacet 3 236
cert_cover_3 3 1 3 2 4 5
cert_coverFacet 4 812
cert_cover_3 4 1 2 2 4 7
cert_coverFacet 5 660
cert_cover_4 5 1 3 6 8
cert_coverFacet 6 488
cert_cover_3 6 2 3 4 5 7
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_073

end
end BundlePart0

section BundlePart1
/- Source: ProjectionCertificates/P0_074.lean -/





@[expose] public section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_074

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [211, 403, 205, 525, 597, 793, 425, 710, 810, 850, 418, 674, 684, 147, 13, 69, 517, 137, 265, 521, 81, 273, 529, 193, 385, 82, 274, 162, 290, 546, 194, 578, 386, 642, 770, 140, 524, 196, 580, 644, 168, 296, 552, 776, 592, 784, 416, 672]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_211, vertices_403, vertices_205, vertices_525, vertices_597, vertices_793, vertices_425, vertices_710, vertices_810, vertices_850, vertices_418, vertices_674, vertices_684] (by decide +kernel)
  polygons := literalFinset [vertices_147, vertices_13, vertices_69, vertices_517, vertices_137, vertices_265, vertices_521, vertices_81, vertices_273, vertices_529, vertices_193, vertices_385, vertices_82, vertices_274, vertices_162, vertices_290, vertices_546, vertices_194, vertices_578, vertices_386, vertices_642, vertices_770, vertices_140, vertices_524, vertices_196, vertices_580, vertices_644, vertices_168, vertices_296, vertices_552, vertices_776, vertices_592, vertices_784, vertices_416, vertices_672] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_211), (false, vertices_403), (false, vertices_205), (false, vertices_525), (false, vertices_597), (false, vertices_793), (false, vertices_425), (true, vertices_162), (true, vertices_290), (true, vertices_546), (true, vertices_578), (true, vertices_642), (true, vertices_770), (true, vertices_644), (true, vertices_552), (true, vertices_672)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 10 13 16 19 20 21 22 23 24
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_211) then 11 else
  if p.val = (false, vertices_403) then 12 else
  if p.val = (false, vertices_205) then 14 else
  if p.val = (false, vertices_525) then 9 else
  if p.val = (false, vertices_597) then 15 else
  if p.val = (false, vertices_793) then 17 else
  if p.val = (false, vertices_425) then 18 else
  if p.val = (true, vertices_162) then 0 else
  if p.val = (true, vertices_290) then 1 else
  if p.val = (true, vertices_546) then 2 else
  if p.val = (true, vertices_578) then 3 else
  if p.val = (true, vertices_642) then 4 else
  if p.val = (true, vertices_770) then 5 else
  if p.val = (true, vertices_644) then 6 else
  if p.val = (true, vertices_552) then 7 else
  if p.val = (true, vertices_672) then 8 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_162), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_290), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_546), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_578), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_642), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_770), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_644), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_552), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_672), by decide +kernel⟩
  | 9 => Sum.inr ⟨(false, vertices_525), by decide +kernel⟩
  | 10 => Sum.inl 0
  | 11 => Sum.inr ⟨(false, vertices_211), by decide +kernel⟩
  | 12 => Sum.inr ⟨(false, vertices_403), by decide +kernel⟩
  | 13 => Sum.inl 1
  | 14 => Sum.inr ⟨(false, vertices_205), by decide +kernel⟩
  | 15 => Sum.inr ⟨(false, vertices_597), by decide +kernel⟩
  | 16 => Sum.inl 2
  | 17 => Sum.inr ⟨(false, vertices_793), by decide +kernel⟩
  | 18 => Sum.inr ⟨(false, vertices_425), by decide +kernel⟩
  | 19 => Sum.inl 3
  | 20 => Sum.inl 4
  | 21 => Sum.inl 5
  | 22 => Sum.inl 6
  | 23 => Sum.inl 7
  | 24 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row 0 3 0 5 7 8 850
cert_row 1 5 0 1 6 8 710
cert_row 2 0 2 4 7 8 810
cert_row 3 1 2 4 6 8 684
cert_rows
cert_pivot_2 3 5 0 1
cert_heightProof 4
cert_coverFacet 0 710
cert_cover_3 0 0 1 1 5 6
cert_coverFacet 1 810
cert_cover_3 1 0 2 2 4 7
cert_coverFacet 2 850
cert_cover_3 2 0 0 3 5 7
cert_coverFacet 3 418
cert_cover_4 3 0 4 6 7
cert_coverFacet 4 674
cert_cover_4 4 0 4 6 8
cert_coverFacet 5 684
cert_cover_3 5 1 3 2 4 6
cert_coveringFacets
cert_coveringProof_6
cert_certificate 4 6
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_074

end
end BundlePart1

section BundlePart2
/- Source: ProjectionCertificates/P0_075.lean -/





@[expose] public section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_075

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [451, 541, 397, 709, 313, 369, 593, 902, 810, 738, 354, 780, 632, 13, 133, 517, 25, 265, 305, 81, 529, 193, 321, 577, 385, 98, 290, 546, 194, 322, 386, 642, 770, 268, 524, 388, 644, 772, 56, 536, 296, 552, 776, 112, 592, 352, 608, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_451, vertices_541, vertices_397, vertices_709, vertices_313, vertices_369, vertices_593, vertices_902, vertices_810, vertices_738, vertices_354, vertices_780, vertices_632] (by decide +kernel)
  polygons := literalFinset [vertices_13, vertices_133, vertices_517, vertices_25, vertices_265, vertices_305, vertices_81, vertices_529, vertices_193, vertices_321, vertices_577, vertices_385, vertices_98, vertices_290, vertices_546, vertices_194, vertices_322, vertices_386, vertices_642, vertices_770, vertices_268, vertices_524, vertices_388, vertices_644, vertices_772, vertices_56, vertices_536, vertices_296, vertices_552, vertices_776, vertices_112, vertices_592, vertices_352, vertices_608, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_451), (false, vertices_541), (false, vertices_397), (false, vertices_709), (false, vertices_313), (false, vertices_369), (false, vertices_593), (true, vertices_98), (true, vertices_290), (true, vertices_546), (true, vertices_642), (true, vertices_770), (true, vertices_772), (true, vertices_552), (true, vertices_776), (true, vertices_608)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 10 12 16 17 20 21 22 23 24
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_451) then 11 else
  if p.val = (false, vertices_541) then 13 else
  if p.val = (false, vertices_397) then 14 else
  if p.val = (false, vertices_709) then 15 else
  if p.val = (false, vertices_313) then 18 else
  if p.val = (false, vertices_369) then 19 else
  if p.val = (false, vertices_593) then 9 else
  if p.val = (true, vertices_98) then 0 else
  if p.val = (true, vertices_290) then 1 else
  if p.val = (true, vertices_546) then 2 else
  if p.val = (true, vertices_642) then 3 else
  if p.val = (true, vertices_770) then 4 else
  if p.val = (true, vertices_772) then 5 else
  if p.val = (true, vertices_552) then 6 else
  if p.val = (true, vertices_776) then 7 else
  if p.val = (true, vertices_608) then 8 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_98), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_290), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_546), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_642), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_770), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_772), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_552), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_776), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_608), by decide +kernel⟩
  | 9 => Sum.inr ⟨(false, vertices_593), by decide +kernel⟩
  | 10 => Sum.inl 0
  | 11 => Sum.inr ⟨(false, vertices_451), by decide +kernel⟩
  | 12 => Sum.inl 1
  | 13 => Sum.inr ⟨(false, vertices_541), by decide +kernel⟩
  | 14 => Sum.inr ⟨(false, vertices_397), by decide +kernel⟩
  | 15 => Sum.inr ⟨(false, vertices_709), by decide +kernel⟩
  | 16 => Sum.inl 2
  | 17 => Sum.inl 3
  | 18 => Sum.inr ⟨(false, vertices_313), by decide +kernel⟩
  | 19 => Sum.inr ⟨(false, vertices_369), by decide +kernel⟩
  | 20 => Sum.inl 4
  | 21 => Sum.inl 5
  | 22 => Sum.inl 6
  | 23 => Sum.inl 7
  | 24 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row 0 1 0 6 7 8 902
cert_row 1 7 0 2 4 8 810
cert_row 2 0 4 5 6 8 738
cert_row 3 2 3 4 5 8 632
cert_rows
cert_pivot_2 1 7 0 2
cert_heightProof 4
cert_coverFacet 0 902
cert_cover_3 0 0 0 1 6 7
cert_coverFacet 1 810
cert_cover_3 1 0 1 2 4 7
cert_coverFacet 2 738
cert_cover_3 2 0 2 4 5 6
cert_coverFacet 3 354
cert_cover_4 3 0 4 5 7
cert_coverFacet 4 780
cert_cover_4 4 1 2 7 8
cert_coverFacet 5 632
cert_cover_3 5 2 3 3 4 5
cert_coveringFacets
cert_coveringProof_6
cert_certificate 4 6
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_075

end
end BundlePart2

section BundlePart3
/- Source: ProjectionCertificates/P0_076.lean -/





@[expose] public section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_076

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [395, 179, 803, 781, 665, 625, 838, 242, 610, 450, 460, 652, 724, 35, 131, 259, 137, 265, 521, 49, 145, 529, 545, 769, 178, 98, 546, 194, 322, 578, 386, 770, 140, 268, 524, 196, 324, 580, 644, 772, 392, 648, 112, 208, 592, 656, 608, 448]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_395, vertices_179, vertices_803, vertices_781, vertices_665, vertices_625, vertices_838, vertices_242, vertices_610, vertices_450, vertices_460, vertices_652, vertices_724] (by decide +kernel)
  polygons := literalFinset [vertices_35, vertices_131, vertices_259, vertices_137, vertices_265, vertices_521, vertices_49, vertices_145, vertices_529, vertices_545, vertices_769, vertices_178, vertices_98, vertices_546, vertices_194, vertices_322, vertices_578, vertices_386, vertices_770, vertices_140, vertices_268, vertices_524, vertices_196, vertices_324, vertices_580, vertices_644, vertices_772, vertices_392, vertices_648, vertices_112, vertices_208, vertices_592, vertices_656, vertices_608, vertices_448] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_395), (false, vertices_179), (false, vertices_803), (false, vertices_781), (false, vertices_665), (false, vertices_625), (true, vertices_98), (true, vertices_194), (true, vertices_322), (true, vertices_578), (true, vertices_140), (true, vertices_196), (true, vertices_324), (true, vertices_580), (true, vertices_644), (true, vertices_208), (true, vertices_448)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 11 15 17 19 21 22 23 24 25
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_395) then 12 else
  if p.val = (false, vertices_179) then 14 else
  if p.val = (false, vertices_803) then 13 else
  if p.val = (false, vertices_781) then 16 else
  if p.val = (false, vertices_665) then 18 else
  if p.val = (false, vertices_625) then 20 else
  if p.val = (true, vertices_98) then 0 else
  if p.val = (true, vertices_194) then 1 else
  if p.val = (true, vertices_322) then 2 else
  if p.val = (true, vertices_578) then 3 else
  if p.val = (true, vertices_140) then 4 else
  if p.val = (true, vertices_196) then 5 else
  if p.val = (true, vertices_324) then 6 else
  if p.val = (true, vertices_580) then 7 else
  if p.val = (true, vertices_644) then 8 else
  if p.val = (true, vertices_208) then 9 else
  if p.val = (true, vertices_448) then 10 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_98), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_194), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_322), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_578), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_140), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_196), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_324), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_580), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_644), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_208), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_448), by decide +kernel⟩
  | 11 => Sum.inl 0
  | 12 => Sum.inr ⟨(false, vertices_395), by decide +kernel⟩
  | 13 => Sum.inr ⟨(false, vertices_803), by decide +kernel⟩
  | 14 => Sum.inr ⟨(false, vertices_179), by decide +kernel⟩
  | 15 => Sum.inl 1
  | 16 => Sum.inr ⟨(false, vertices_781), by decide +kernel⟩
  | 17 => Sum.inl 2
  | 18 => Sum.inr ⟨(false, vertices_665), by decide +kernel⟩
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
cert_row 0 2 1 5 6 7 460
cert_row 1 7 0 1 5 8 838
cert_row 2 1 3 5 6 8 724
cert_row_3 3 4 3 6 0 178
cert_rows
cert_pivot_2 2 7 1 0
cert_heightProof 4
cert_coverFacet 0 838
cert_cover_3 0 0 1 1 5 7
cert_coverFacet 1 242
cert_cover_3 1 0 3 3 4 5
cert_coverFacet 2 610
cert_cover_4 2 0 4 5 8
cert_coverFacet 3 450
cert_cover_4 3 0 5 6 7
cert_coverFacet 4 460
cert_cover_3 4 1 0 2 5 6
cert_coverFacet 5 652
cert_cover_4 5 1 2 6 8
cert_coverFacet 6 724
cert_cover_3 6 1 2 3 5 6
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_076

end
end BundlePart3

section BundlePart4
/- Source: ProjectionCertificates/P0_077.lean -/





@[expose] public section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_077

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [675, 285, 653, 421, 345, 617, 353, 902, 850, 482, 610, 604, 788, 13, 133, 261, 281, 73, 521, 97, 161, 289, 545, 321, 641, 98, 162, 546, 322, 578, 386, 642, 770, 28, 524, 276, 532, 388, 644, 772, 88, 584, 336, 592, 784, 352, 608, 416]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_675, vertices_285, vertices_653, vertices_421, vertices_345, vertices_617, vertices_353, vertices_902, vertices_850, vertices_482, vertices_610, vertices_604, vertices_788] (by decide +kernel)
  polygons := literalFinset [vertices_13, vertices_133, vertices_261, vertices_281, vertices_73, vertices_521, vertices_97, vertices_161, vertices_289, vertices_545, vertices_321, vertices_641, vertices_98, vertices_162, vertices_546, vertices_322, vertices_578, vertices_386, vertices_642, vertices_770, vertices_28, vertices_524, vertices_276, vertices_532, vertices_388, vertices_644, vertices_772, vertices_88, vertices_584, vertices_336, vertices_592, vertices_784, vertices_352, vertices_608, vertices_416] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_675), (false, vertices_285), (false, vertices_653), (false, vertices_421), (false, vertices_345), (false, vertices_617), (false, vertices_353), (true, vertices_98), (true, vertices_322), (true, vertices_578), (true, vertices_386), (true, vertices_770), (true, vertices_532), (true, vertices_772), (true, vertices_592), (true, vertices_784)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 10 12 15 19 20 21 22 23 24
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_675) then 11 else
  if p.val = (false, vertices_285) then 17 else
  if p.val = (false, vertices_653) then 13 else
  if p.val = (false, vertices_421) then 14 else
  if p.val = (false, vertices_345) then 18 else
  if p.val = (false, vertices_617) then 16 else
  if p.val = (false, vertices_353) then 9 else
  if p.val = (true, vertices_98) then 0 else
  if p.val = (true, vertices_322) then 1 else
  if p.val = (true, vertices_578) then 2 else
  if p.val = (true, vertices_386) then 3 else
  if p.val = (true, vertices_770) then 4 else
  if p.val = (true, vertices_532) then 5 else
  if p.val = (true, vertices_772) then 6 else
  if p.val = (true, vertices_592) then 7 else
  if p.val = (true, vertices_784) then 8 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_98), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_322), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_578), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_386), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_770), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_532), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_772), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_592), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_784), by decide +kernel⟩
  | 9 => Sum.inr ⟨(false, vertices_353), by decide +kernel⟩
  | 10 => Sum.inl 0
  | 11 => Sum.inr ⟨(false, vertices_675), by decide +kernel⟩
  | 12 => Sum.inl 1
  | 13 => Sum.inr ⟨(false, vertices_653), by decide +kernel⟩
  | 14 => Sum.inr ⟨(false, vertices_421), by decide +kernel⟩
  | 15 => Sum.inl 2
  | 16 => Sum.inr ⟨(false, vertices_617), by decide +kernel⟩
  | 17 => Sum.inr ⟨(false, vertices_285), by decide +kernel⟩
  | 18 => Sum.inr ⟨(false, vertices_345), by decide +kernel⟩
  | 19 => Sum.inl 3
  | 20 => Sum.inl 4
  | 21 => Sum.inl 5
  | 22 => Sum.inl 6
  | 23 => Sum.inl 7
  | 24 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row 0 4 0 5 6 7 482
cert_row 1 6 0 1 7 8 902
cert_row 2 0 3 5 7 8 850
cert_row 3 1 2 3 5 8 604
cert_rows
cert_pivot_2 4 6 0 1
cert_heightProof 4
cert_coverFacet 0 902
cert_cover_3 0 0 1 1 6 7
cert_coverFacet 1 850
cert_cover_3 1 0 2 3 5 7
cert_coverFacet 2 482
cert_cover_3 2 0 0 4 5 6
cert_coverFacet 3 610
cert_cover_4 3 0 4 5 8
cert_coverFacet 4 604
cert_cover_3 4 1 3 2 3 5
cert_coverFacet 5 788
cert_cover_4 5 1 3 7 8
cert_coveringFacets
cert_coveringProof_6
cert_certificate 4 6
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_077

end
end BundlePart4

section BundlePart5
/- Source: ProjectionCertificates/P0_078.lean -/





@[expose] public section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_078

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [707, 901, 313, 601, 777, 465, 358, 678, 454, 626, 812, 568, 368, 25, 265, 521, 81, 273, 193, 577, 385, 641, 769, 38, 326, 134, 98, 546, 194, 578, 642, 292, 548, 388, 644, 772, 56, 536, 296, 552, 776, 112, 304, 560, 336, 592, 352, 448]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_707, vertices_901, vertices_313, vertices_601, vertices_777, vertices_465, vertices_358, vertices_678, vertices_454, vertices_626, vertices_812, vertices_568, vertices_368] (by decide +kernel)
  polygons := literalFinset [vertices_25, vertices_265, vertices_521, vertices_81, vertices_273, vertices_193, vertices_577, vertices_385, vertices_641, vertices_769, vertices_38, vertices_326, vertices_134, vertices_98, vertices_546, vertices_194, vertices_578, vertices_642, vertices_292, vertices_548, vertices_388, vertices_644, vertices_772, vertices_56, vertices_536, vertices_296, vertices_552, vertices_776, vertices_112, vertices_304, vertices_560, vertices_336, vertices_592, vertices_352, vertices_448] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_707), (false, vertices_901), (false, vertices_313), (false, vertices_601), (false, vertices_777), (false, vertices_465), (true, vertices_38), (true, vertices_326), (true, vertices_134), (true, vertices_98), (true, vertices_546), (true, vertices_292), (true, vertices_548), (true, vertices_552), (true, vertices_112), (true, vertices_560), (true, vertices_352)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 11 14 16 19 21 22 23 24 25
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_707) then 12 else
  if p.val = (false, vertices_901) then 15 else
  if p.val = (false, vertices_313) then 17 else
  if p.val = (false, vertices_601) then 18 else
  if p.val = (false, vertices_777) then 10 else
  if p.val = (false, vertices_465) then 20 else
  if p.val = (true, vertices_38) then 0 else
  if p.val = (true, vertices_326) then 13 else
  if p.val = (true, vertices_134) then 1 else
  if p.val = (true, vertices_98) then 2 else
  if p.val = (true, vertices_546) then 3 else
  if p.val = (true, vertices_292) then 4 else
  if p.val = (true, vertices_548) then 5 else
  if p.val = (true, vertices_552) then 6 else
  if p.val = (true, vertices_112) then 7 else
  if p.val = (true, vertices_560) then 8 else
  if p.val = (true, vertices_352) then 9 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_38), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_134), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_98), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_546), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_292), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_548), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_552), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_112), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_560), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_352), by decide +kernel⟩
  | 10 => Sum.inr ⟨(false, vertices_777), by decide +kernel⟩
  | 11 => Sum.inl 0
  | 12 => Sum.inr ⟨(false, vertices_707), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_326), by decide +kernel⟩
  | 14 => Sum.inl 1
  | 15 => Sum.inr ⟨(false, vertices_901), by decide +kernel⟩
  | 16 => Sum.inl 2
  | 17 => Sum.inr ⟨(false, vertices_313), by decide +kernel⟩
  | 18 => Sum.inr ⟨(false, vertices_601), by decide +kernel⟩
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
cert_row 0 6 0 1 4 8 678
cert_row 1 3 0 4 5 8 626
cert_row 2 2 1 4 7 8 812
cert_row_3 3 5 1 7 0 326
cert_rows
cert_pivot_2 6 3 2 0
cert_heightProof 4
cert_coverFacet 0 358
cert_cover_3 0 0 3 1 4 5
cert_coverFacet 1 678
cert_cover_3 1 0 0 1 4 6
cert_coverFacet 2 454
cert_cover_3 2 0 3 1 5 6
cert_coverFacet 3 626
cert_cover_3 3 0 1 3 4 5
cert_coverFacet 4 812
cert_cover_3 4 1 2 2 4 7
cert_coverFacet 5 568
cert_cover_4 5 2 3 4 8
cert_coverFacet 6 368
cert_cover_4 6 3 4 5 7
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_078

end
end BundlePart5

section BundlePart6
/- Source: ProjectionCertificates/P0_079.lean -/





@[expose] public section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_079

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [551, 651, 339, 403, 99, 397, 525, 357, 722, 610, 812, 920, 880, 275, 35, 67, 131, 515, 13, 37, 261, 517, 137, 521, 97, 321, 385, 82, 146, 98, 546, 578, 642, 268, 524, 292, 548, 392, 648, 776, 336, 592, 400, 656, 784, 352, 608, 800]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_551, vertices_651, vertices_339, vertices_403, vertices_99, vertices_397, vertices_525, vertices_357, vertices_722, vertices_610, vertices_812, vertices_920, vertices_880] (by decide +kernel)
  polygons := literalFinset [vertices_275, vertices_35, vertices_67, vertices_131, vertices_515, vertices_13, vertices_37, vertices_261, vertices_517, vertices_137, vertices_521, vertices_97, vertices_321, vertices_385, vertices_82, vertices_146, vertices_98, vertices_546, vertices_578, vertices_642, vertices_268, vertices_524, vertices_292, vertices_548, vertices_392, vertices_648, vertices_776, vertices_336, vertices_592, vertices_400, vertices_656, vertices_784, vertices_352, vertices_608, vertices_800] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_551), (false, vertices_651), (false, vertices_339), (false, vertices_403), (false, vertices_99), (false, vertices_397), (false, vertices_525), (false, vertices_357), (true, vertices_578), (true, vertices_776), (true, vertices_592), (true, vertices_656), (true, vertices_784), (true, vertices_608), (true, vertices_800)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 13 9 17 18 19 20 21 22 23
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_551) then 10 else
  if p.val = (false, vertices_651) then 14 else
  if p.val = (false, vertices_339) then 15 else
  if p.val = (false, vertices_403) then 16 else
  if p.val = (false, vertices_99) then 7 else
  if p.val = (false, vertices_397) then 11 else
  if p.val = (false, vertices_525) then 8 else
  if p.val = (false, vertices_357) then 12 else
  if p.val = (true, vertices_578) then 0 else
  if p.val = (true, vertices_776) then 1 else
  if p.val = (true, vertices_592) then 2 else
  if p.val = (true, vertices_656) then 3 else
  if p.val = (true, vertices_784) then 4 else
  if p.val = (true, vertices_608) then 5 else
  if p.val = (true, vertices_800) then 6 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_578), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_776), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_592), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_656), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_784), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_608), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_800), by decide +kernel⟩
  | 7 => Sum.inr ⟨(false, vertices_99), by decide +kernel⟩
  | 8 => Sum.inr ⟨(false, vertices_525), by decide +kernel⟩
  | 9 => Sum.inl 1
  | 10 => Sum.inr ⟨(false, vertices_551), by decide +kernel⟩
  | 11 => Sum.inr ⟨(false, vertices_397), by decide +kernel⟩
  | 12 => Sum.inr ⟨(false, vertices_357), by decide +kernel⟩
  | 13 => Sum.inl 0
  | 14 => Sum.inr ⟨(false, vertices_651), by decide +kernel⟩
  | 15 => Sum.inr ⟨(false, vertices_339), by decide +kernel⟩
  | 16 => Sum.inr ⟨(false, vertices_403), by decide +kernel⟩
  | 17 => Sum.inl 2
  | 18 => Sum.inl 3
  | 19 => Sum.inl 4
  | 20 => Sum.inl 5
  | 21 => Sum.inl 6
  | 22 => Sum.inl 7
  | 23 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row 0 0 3 5 6 8 722
cert_row 1 1 2 4 7 8 812
cert_row 2 2 3 6 7 8 920
cert_row 3 3 4 5 7 8 880
cert_rows
cert_pivot_2 0 1 2 3
cert_heightProof 4
cert_coverFacet 0 722
cert_cover_3 0 0 0 3 5 6
cert_coverFacet 1 610
cert_cover_4 1 0 4 5 8
cert_coverFacet 2 812
cert_cover_3 2 1 1 2 4 7
cert_coverFacet 3 920
cert_cover_3 3 2 2 3 6 7
cert_coverFacet 4 880
cert_cover_3 4 3 3 4 5 7
cert_coveringFacets_3
cert_coveringProof_7
cert_certificate 4 5
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_079

end
end BundlePart6

section BundlePart7
/- Source: ProjectionCertificates/P0_081.lean -/





@[expose] public section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_081

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [595, 901, 345, 425, 713, 785, 790, 422, 550, 362, 618, 338, 684, 73, 137, 265, 81, 273, 529, 577, 385, 641, 769, 38, 262, 518, 106, 82, 274, 530, 290, 546, 322, 578, 164, 548, 388, 644, 772, 168, 296, 552, 328, 584, 648, 336, 784, 416]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_595, vertices_901, vertices_345, vertices_425, vertices_713, vertices_785, vertices_790, vertices_422, vertices_550, vertices_362, vertices_618, vertices_338, vertices_684] (by decide +kernel)
  polygons := literalFinset [vertices_73, vertices_137, vertices_265, vertices_81, vertices_273, vertices_529, vertices_577, vertices_385, vertices_641, vertices_769, vertices_38, vertices_262, vertices_518, vertices_106, vertices_82, vertices_274, vertices_530, vertices_290, vertices_546, vertices_322, vertices_578, vertices_164, vertices_548, vertices_388, vertices_644, vertices_772, vertices_168, vertices_296, vertices_552, vertices_328, vertices_584, vertices_648, vertices_336, vertices_784, vertices_416] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_595), (false, vertices_901), (false, vertices_345), (false, vertices_425), (false, vertices_713), (false, vertices_785), (true, vertices_38), (true, vertices_262), (true, vertices_518), (true, vertices_106), (true, vertices_274), (true, vertices_290), (true, vertices_546), (true, vertices_322), (true, vertices_164), (true, vertices_548), (true, vertices_552)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 11 14 16 20 21 22 23 24 25
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_595) then 12 else
  if p.val = (false, vertices_901) then 15 else
  if p.val = (false, vertices_345) then 17 else
  if p.val = (false, vertices_425) then 18 else
  if p.val = (false, vertices_713) then 19 else
  if p.val = (false, vertices_785) then 10 else
  if p.val = (true, vertices_38) then 0 else
  if p.val = (true, vertices_262) then 1 else
  if p.val = (true, vertices_518) then 2 else
  if p.val = (true, vertices_106) then 13 else
  if p.val = (true, vertices_274) then 3 else
  if p.val = (true, vertices_290) then 4 else
  if p.val = (true, vertices_546) then 5 else
  if p.val = (true, vertices_322) then 6 else
  if p.val = (true, vertices_164) then 7 else
  if p.val = (true, vertices_548) then 8 else
  if p.val = (true, vertices_552) then 9 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_38), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_262), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_518), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_274), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_290), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_546), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_322), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_164), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_548), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_552), by decide +kernel⟩
  | 10 => Sum.inr ⟨(false, vertices_785), by decide +kernel⟩
  | 11 => Sum.inl 0
  | 12 => Sum.inr ⟨(false, vertices_595), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_106), by decide +kernel⟩
  | 14 => Sum.inl 1
  | 15 => Sum.inr ⟨(false, vertices_901), by decide +kernel⟩
  | 16 => Sum.inl 2
  | 17 => Sum.inr ⟨(false, vertices_345), by decide +kernel⟩
  | 18 => Sum.inr ⟨(false, vertices_425), by decide +kernel⟩
  | 19 => Sum.inr ⟨(false, vertices_713), by decide +kernel⟩
  | 20 => Sum.inl 3
  | 21 => Sum.inl 4
  | 22 => Sum.inl 5
  | 23 => Sum.inl 6
  | 24 => Sum.inl 7
  | 25 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row 0 3 0 1 7 8 790
cert_row 1 7 0 1 4 6 422
cert_row 2 1 2 4 6 8 684
cert_row_3 3 4 2 5 0 106
cert_rows
cert_pivot_2 3 7 1 0
cert_heightProof 4
cert_coverFacet 0 790
cert_cover_3 0 0 0 1 3 7
cert_coverFacet 1 422
cert_cover_3 1 0 1 1 4 6
cert_coverFacet 2 550
cert_cover_4 2 0 1 4 8
cert_coverFacet 3 362
cert_cover_3 3 0 3 2 4 7
cert_coverFacet 4 618
cert_cover_3 4 0 3 2 4 8
cert_coverFacet 5 338
cert_cover_4 5 0 3 5 7
cert_coverFacet 6 684
cert_cover_3 6 1 2 2 4 6
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_081

end
end BundlePart7

section BundlePart8
/- Source: ProjectionCertificates/P0_083.lean -/





@[expose] public section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_083

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [91, 539, 421, 681, 457, 369, 561, 790, 714, 338, 834, 692, 308, 964, 27, 73, 137, 521, 49, 81, 529, 161, 289, 545, 321, 385, 74, 522, 82, 274, 530, 322, 578, 770, 52, 276, 532, 164, 292, 388, 644, 772, 200, 648, 304, 560, 336, 672, 448, 704, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_91, vertices_539, vertices_421, vertices_681, vertices_457, vertices_369, vertices_561, vertices_790, vertices_714, vertices_338, vertices_834, vertices_692, vertices_308, vertices_964] (by decide +kernel)
  polygons := literalFinset [vertices_27, vertices_73, vertices_137, vertices_521, vertices_49, vertices_81, vertices_529, vertices_161, vertices_289, vertices_545, vertices_321, vertices_385, vertices_74, vertices_522, vertices_82, vertices_274, vertices_530, vertices_322, vertices_578, vertices_770, vertices_52, vertices_276, vertices_532, vertices_164, vertices_292, vertices_388, vertices_644, vertices_772, vertices_200, vertices_648, vertices_304, vertices_560, vertices_336, vertices_672, vertices_448, vertices_704, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_91), (false, vertices_539), (false, vertices_421), (false, vertices_681), (false, vertices_457), (false, vertices_369), (false, vertices_561), (true, vertices_274), (true, vertices_322), (true, vertices_578), (true, vertices_770), (true, vertices_52), (true, vertices_276), (true, vertices_532), (true, vertices_644), (true, vertices_772), (true, vertices_704), (true, vertices_832)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 12 15 17 20 22 23 24 25 26
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_91) then 13 else
  if p.val = (false, vertices_539) then 14 else
  if p.val = (false, vertices_421) then 16 else
  if p.val = (false, vertices_681) then 18 else
  if p.val = (false, vertices_457) then 19 else
  if p.val = (false, vertices_369) then 21 else
  if p.val = (false, vertices_561) then 11 else
  if p.val = (true, vertices_274) then 0 else
  if p.val = (true, vertices_322) then 1 else
  if p.val = (true, vertices_578) then 2 else
  if p.val = (true, vertices_770) then 3 else
  if p.val = (true, vertices_52) then 4 else
  if p.val = (true, vertices_276) then 5 else
  if p.val = (true, vertices_532) then 6 else
  if p.val = (true, vertices_644) then 7 else
  if p.val = (true, vertices_772) then 8 else
  if p.val = (true, vertices_704) then 9 else
  if p.val = (true, vertices_832) then 10 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_274), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_322), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_578), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_770), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_52), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_276), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_532), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_644), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_772), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_704), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_832), by decide +kernel⟩
  | 11 => Sum.inr ⟨(false, vertices_561), by decide +kernel⟩
  | 12 => Sum.inl 0
  | 13 => Sum.inr ⟨(false, vertices_91), by decide +kernel⟩
  | 14 => Sum.inr ⟨(false, vertices_539), by decide +kernel⟩
  | 15 => Sum.inl 1
  | 16 => Sum.inr ⟨(false, vertices_421), by decide +kernel⟩
  | 17 => Sum.inl 2
  | 18 => Sum.inr ⟨(false, vertices_681), by decide +kernel⟩
  | 19 => Sum.inr ⟨(false, vertices_457), by decide +kernel⟩
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
cert_row 0 2 0 5 6 8 714
cert_row 1 0 1 3 7 8 790
cert_row 2 3 1 4 6 8 692
cert_row 3 1 5 6 7 8 964
cert_rows
cert_pivot_2 2 0 3 1
cert_heightProof 4
cert_coverFacet 0 790
cert_cover_3 0 0 1 1 3 7
cert_coverFacet 1 714
cert_cover_3 1 0 0 2 5 6
cert_coverFacet 2 338
cert_cover_4 2 0 3 5 7
cert_coverFacet 3 834
cert_cover_4 3 0 5 7 8
cert_coverFacet 4 692
cert_cover_3 4 1 2 3 4 6
cert_coverFacet 5 308
cert_cover_4 5 1 3 4 7
cert_coverFacet 6 964
cert_cover_3 6 1 3 5 6 7
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_083

end
end BundlePart8

section BundlePart9
/- Source: ProjectionCertificates/P0_084.lean -/





@[expose] public section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_084

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [899, 597, 229, 805, 713, 417, 790, 602, 282, 394, 650, 124, 316, 488, 37, 69, 517, 161, 289, 193, 577, 385, 641, 769, 26, 138, 266, 522, 274, 530, 386, 642, 770, 60, 84, 276, 532, 100, 292, 772, 88, 280, 104, 296, 200, 584, 392, 648, 592, 224, 416]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_899, vertices_597, vertices_229, vertices_805, vertices_713, vertices_417, vertices_790, vertices_602, vertices_282, vertices_394, vertices_650, vertices_124, vertices_316, vertices_488] (by decide +kernel)
  polygons := literalFinset [vertices_37, vertices_69, vertices_517, vertices_161, vertices_289, vertices_193, vertices_577, vertices_385, vertices_641, vertices_769, vertices_26, vertices_138, vertices_266, vertices_522, vertices_274, vertices_530, vertices_386, vertices_642, vertices_770, vertices_60, vertices_84, vertices_276, vertices_532, vertices_100, vertices_292, vertices_772, vertices_88, vertices_280, vertices_104, vertices_296, vertices_200, vertices_584, vertices_392, vertices_648, vertices_592, vertices_224, vertices_416] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_899), (false, vertices_597), (false, vertices_229), (false, vertices_805), (false, vertices_713), (false, vertices_417), (true, vertices_26), (true, vertices_138), (true, vertices_266), (true, vertices_522), (true, vertices_274), (true, vertices_530), (true, vertices_60), (true, vertices_276), (true, vertices_88), (true, vertices_280), (true, vertices_104), (true, vertices_296), (true, vertices_392)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 13 18 15 22 23 24 25 26 27
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_899) then 14 else
  if p.val = (false, vertices_597) then 19 else
  if p.val = (false, vertices_229) then 20 else
  if p.val = (false, vertices_805) then 21 else
  if p.val = (false, vertices_713) then 16 else
  if p.val = (false, vertices_417) then 12 else
  if p.val = (true, vertices_26) then 0 else
  if p.val = (true, vertices_138) then 1 else
  if p.val = (true, vertices_266) then 2 else
  if p.val = (true, vertices_522) then 3 else
  if p.val = (true, vertices_274) then 4 else
  if p.val = (true, vertices_530) then 5 else
  if p.val = (true, vertices_60) then 17 else
  if p.val = (true, vertices_276) then 6 else
  if p.val = (true, vertices_88) then 7 else
  if p.val = (true, vertices_280) then 8 else
  if p.val = (true, vertices_104) then 9 else
  if p.val = (true, vertices_296) then 10 else
  if p.val = (true, vertices_392) then 11 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_26), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_138), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_266), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_522), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_274), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_530), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_276), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_88), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_280), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_104), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_296), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_392), by decide +kernel⟩
  | 12 => Sum.inr ⟨(false, vertices_417), by decide +kernel⟩
  | 13 => Sum.inl 0
  | 14 => Sum.inr ⟨(false, vertices_899), by decide +kernel⟩
  | 15 => Sum.inl 2
  | 16 => Sum.inr ⟨(false, vertices_713), by decide +kernel⟩
  | 17 => Sum.inr ⟨(true, vertices_60), by decide +kernel⟩
  | 18 => Sum.inl 1
  | 19 => Sum.inr ⟨(false, vertices_597), by decide +kernel⟩
  | 20 => Sum.inr ⟨(false, vertices_229), by decide +kernel⟩
  | 21 => Sum.inr ⟨(false, vertices_805), by decide +kernel⟩
  | 22 => Sum.inl 3
  | 23 => Sum.inl 4
  | 24 => Sum.inl 5
  | 25 => Sum.inl 6
  | 26 => Sum.inl 7
  | 27 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row 0 6 2 4 5 7 488
cert_row 1 7 0 1 3 8 790
cert_row 2 0 2 3 5 8 602
cert_row_3 3 3 2 4 1 60
cert_rows
cert_pivot_2 6 7 0 1
cert_heightProof 4
cert_coverFacet 0 790
cert_cover_3 0 0 1 1 3 7
cert_coverFacet 1 602
cert_cover_3 1 0 2 2 3 5
cert_coverFacet 2 282
cert_cover_4 2 0 2 3 7
cert_coverFacet 3 394
cert_cover_4 3 0 2 6 7
cert_coverFacet 4 650
cert_cover_4 4 0 2 6 8
cert_coverFacet 5 124
cert_cover_3 5 1 3 2 3 5
cert_coverFacet 6 316
cert_cover_3 6 1 3 2 3 7
cert_coverFacet 7 488
cert_cover_3 7 2 0 4 5 6
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_084

end
end BundlePart9

section BundlePart10
/- Source: ProjectionCertificates/P0_085.lean -/





@[expose] public section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_085

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [43, 779, 675, 901, 121, 345, 481, 58, 538, 626, 796, 468, 596, 740, 11, 35, 515, 89, 41, 265, 97, 161, 321, 385, 641, 769, 26, 42, 522, 50, 530, 546, 84, 276, 532, 196, 580, 388, 644, 772, 56, 280, 536, 776, 112, 336, 592, 224, 608, 672, 448]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_43, vertices_779, vertices_675, vertices_901, vertices_121, vertices_345, vertices_481, vertices_58, vertices_538, vertices_626, vertices_796, vertices_468, vertices_596, vertices_740] (by decide +kernel)
  polygons := literalFinset [vertices_11, vertices_35, vertices_515, vertices_89, vertices_41, vertices_265, vertices_97, vertices_161, vertices_321, vertices_385, vertices_641, vertices_769, vertices_26, vertices_42, vertices_522, vertices_50, vertices_530, vertices_546, vertices_84, vertices_276, vertices_532, vertices_196, vertices_580, vertices_388, vertices_644, vertices_772, vertices_56, vertices_280, vertices_536, vertices_776, vertices_112, vertices_336, vertices_592, vertices_224, vertices_608, vertices_672, vertices_448] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_43), (false, vertices_779), (false, vertices_675), (false, vertices_901), (false, vertices_121), (false, vertices_345), (false, vertices_481), (true, vertices_26), (true, vertices_50), (true, vertices_530), (true, vertices_84), (true, vertices_276), (true, vertices_532), (true, vertices_196), (true, vertices_580), (true, vertices_536), (true, vertices_592), (true, vertices_608)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 12 15 17 20 21 23 24 25 26
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_43) then 11 else
  if p.val = (false, vertices_779) then 13 else
  if p.val = (false, vertices_675) then 14 else
  if p.val = (false, vertices_901) then 16 else
  if p.val = (false, vertices_121) then 18 else
  if p.val = (false, vertices_345) then 19 else
  if p.val = (false, vertices_481) then 22 else
  if p.val = (true, vertices_26) then 0 else
  if p.val = (true, vertices_50) then 1 else
  if p.val = (true, vertices_530) then 2 else
  if p.val = (true, vertices_84) then 3 else
  if p.val = (true, vertices_276) then 4 else
  if p.val = (true, vertices_532) then 5 else
  if p.val = (true, vertices_196) then 6 else
  if p.val = (true, vertices_580) then 7 else
  if p.val = (true, vertices_536) then 8 else
  if p.val = (true, vertices_592) then 9 else
  if p.val = (true, vertices_608) then 10 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_26), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_50), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_530), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_84), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_276), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_532), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_196), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_580), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_536), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_592), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_608), by decide +kernel⟩
  | 11 => Sum.inr ⟨(false, vertices_43), by decide +kernel⟩
  | 12 => Sum.inl 0
  | 13 => Sum.inr ⟨(false, vertices_779), by decide +kernel⟩
  | 14 => Sum.inr ⟨(false, vertices_675), by decide +kernel⟩
  | 15 => Sum.inl 1
  | 16 => Sum.inr ⟨(false, vertices_901), by decide +kernel⟩
  | 17 => Sum.inl 2
  | 18 => Sum.inr ⟨(false, vertices_121), by decide +kernel⟩
  | 19 => Sum.inr ⟨(false, vertices_345), by decide +kernel⟩
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
cert_row 0 0 3 4 5 8 626
cert_row 1 2 1 3 7 8 796
cert_row 2 3 1 5 6 7 468
cert_row 3 1 4 5 6 8 740
cert_rows
cert_pivot_2 0 2 3 1
cert_heightProof 4
cert_coverFacet 0 58
cert_cover_4 0 0 2 3 4
cert_coverFacet 1 538
cert_cover_4 1 0 2 3 8
cert_coverFacet 2 626
cert_cover_3 2 0 0 3 4 5
cert_coverFacet 3 796
cert_cover_3 3 1 1 2 3 7
cert_coverFacet 4 468
cert_cover_3 4 1 2 3 5 6
cert_coverFacet 5 596
cert_cover_4 5 1 3 5 8
cert_coverFacet 6 740
cert_cover_3 6 1 3 4 5 6
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_085

end
end BundlePart10

section BundlePart11
/- Source: ProjectionCertificates/P0_090.lean -/





@[expose] public section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_090

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [87, 279, 357, 425, 241, 913, 614, 774, 722, 786, 300, 556, 908, 744, 23, 69, 261, 81, 145, 273, 97, 161, 289, 385, 70, 262, 518, 82, 274, 530, 578, 770, 44, 268, 524, 100, 292, 548, 772, 168, 296, 552, 392, 648, 208, 656, 784, 224, 608, 704, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_87, vertices_279, vertices_357, vertices_425, vertices_241, vertices_913, vertices_614, vertices_774, vertices_722, vertices_786, vertices_300, vertices_556, vertices_908, vertices_744] (by decide +kernel)
  polygons := literalFinset [vertices_23, vertices_69, vertices_261, vertices_81, vertices_145, vertices_273, vertices_97, vertices_161, vertices_289, vertices_385, vertices_70, vertices_262, vertices_518, vertices_82, vertices_274, vertices_530, vertices_578, vertices_770, vertices_44, vertices_268, vertices_524, vertices_100, vertices_292, vertices_548, vertices_772, vertices_168, vertices_296, vertices_552, vertices_392, vertices_648, vertices_208, vertices_656, vertices_784, vertices_224, vertices_608, vertices_704, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_87), (false, vertices_279), (false, vertices_357), (false, vertices_425), (false, vertices_241), (false, vertices_913), (true, vertices_518), (true, vertices_530), (true, vertices_578), (true, vertices_770), (true, vertices_44), (true, vertices_268), (true, vertices_524), (true, vertices_548), (true, vertices_772), (true, vertices_552), (true, vertices_648), (true, vertices_608), (true, vertices_704)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 13 16 18 20 23 24 25 26 27
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_87) then 14 else
  if p.val = (false, vertices_279) then 15 else
  if p.val = (false, vertices_357) then 17 else
  if p.val = (false, vertices_425) then 19 else
  if p.val = (false, vertices_241) then 21 else
  if p.val = (false, vertices_913) then 22 else
  if p.val = (true, vertices_518) then 0 else
  if p.val = (true, vertices_530) then 1 else
  if p.val = (true, vertices_578) then 2 else
  if p.val = (true, vertices_770) then 3 else
  if p.val = (true, vertices_44) then 4 else
  if p.val = (true, vertices_268) then 5 else
  if p.val = (true, vertices_524) then 6 else
  if p.val = (true, vertices_548) then 7 else
  if p.val = (true, vertices_772) then 8 else
  if p.val = (true, vertices_552) then 9 else
  if p.val = (true, vertices_648) then 10 else
  if p.val = (true, vertices_608) then 11 else
  if p.val = (true, vertices_704) then 12 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_518), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_530), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_578), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_770), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_44), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_268), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_524), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_548), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_772), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_552), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_648), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_608), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_704), by decide +kernel⟩
  | 13 => Sum.inl 0
  | 14 => Sum.inr ⟨(false, vertices_87), by decide +kernel⟩
  | 15 => Sum.inr ⟨(false, vertices_279), by decide +kernel⟩
  | 16 => Sum.inl 1
  | 17 => Sum.inr ⟨(false, vertices_357), by decide +kernel⟩
  | 18 => Sum.inl 2
  | 19 => Sum.inr ⟨(false, vertices_425), by decide +kernel⟩
  | 20 => Sum.inl 3
  | 21 => Sum.inr ⟨(false, vertices_241), by decide +kernel⟩
  | 22 => Sum.inr ⟨(false, vertices_913), by decide +kernel⟩
  | 23 => Sum.inl 4
  | 24 => Sum.inl 5
  | 25 => Sum.inl 6
  | 26 => Sum.inl 7
  | 27 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row 0 3 0 5 6 8 722
cert_row 1 0 1 4 5 8 614
cert_row 2 1 2 6 7 8 908
cert_row 3 2 4 5 6 8 744
cert_rows
cert_pivot_2 3 0 1 2
cert_heightProof 4
cert_coverFacet 0 614
cert_cover_3 0 0 1 1 4 5
cert_coverFacet 1 774
cert_cover_4 1 0 1 7 8
cert_coverFacet 2 722
cert_cover_3 2 0 0 3 5 6
cert_coverFacet 3 786
cert_cover_4 3 0 3 7 8
cert_coverFacet 4 300
cert_cover_4 4 1 2 4 7
cert_coverFacet 5 556
cert_cover_4 5 1 2 4 8
cert_coverFacet 6 908
cert_cover_3 6 1 2 2 6 7
cert_coverFacet 7 744
cert_cover_3 7 2 3 4 5 6
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_090

end
end BundlePart11

section BundlePart12
/- Source: ProjectionCertificates/P0_101.lean -/





@[expose] public section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_101

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [103, 167, 29, 397, 597, 345, 481, 654, 582, 610, 930, 540, 920, 880, 39, 13, 21, 69, 133, 25, 265, 81, 97, 161, 321, 385, 70, 134, 518, 98, 162, 546, 578, 642, 28, 140, 524, 532, 580, 280, 536, 392, 648, 336, 592, 784, 352, 608, 416, 800, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_103, vertices_167, vertices_29, vertices_397, vertices_597, vertices_345, vertices_481, vertices_654, vertices_582, vertices_610, vertices_930, vertices_540, vertices_920, vertices_880] (by decide +kernel)
  polygons := literalFinset [vertices_39, vertices_13, vertices_21, vertices_69, vertices_133, vertices_25, vertices_265, vertices_81, vertices_97, vertices_161, vertices_321, vertices_385, vertices_70, vertices_134, vertices_518, vertices_98, vertices_162, vertices_546, vertices_578, vertices_642, vertices_28, vertices_140, vertices_524, vertices_532, vertices_580, vertices_280, vertices_536, vertices_392, vertices_648, vertices_336, vertices_592, vertices_784, vertices_352, vertices_608, vertices_416, vertices_800, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_103), (false, vertices_167), (false, vertices_29), (false, vertices_397), (false, vertices_597), (false, vertices_345), (false, vertices_481), (true, vertices_518), (true, vertices_546), (true, vertices_578), (true, vertices_642), (true, vertices_524), (true, vertices_536), (true, vertices_648), (true, vertices_784), (true, vertices_608), (true, vertices_800), (true, vertices_896)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 12 15 18 20 21 23 24 25 26
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_103) then 13 else
  if p.val = (false, vertices_167) then 14 else
  if p.val = (false, vertices_29) then 11 else
  if p.val = (false, vertices_397) then 16 else
  if p.val = (false, vertices_597) then 17 else
  if p.val = (false, vertices_345) then 19 else
  if p.val = (false, vertices_481) then 22 else
  if p.val = (true, vertices_518) then 0 else
  if p.val = (true, vertices_546) then 1 else
  if p.val = (true, vertices_578) then 2 else
  if p.val = (true, vertices_642) then 3 else
  if p.val = (true, vertices_524) then 4 else
  if p.val = (true, vertices_536) then 5 else
  if p.val = (true, vertices_648) then 6 else
  if p.val = (true, vertices_784) then 7 else
  if p.val = (true, vertices_608) then 8 else
  if p.val = (true, vertices_800) then 9 else
  if p.val = (true, vertices_896) then 10 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_518), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_546), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_578), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_642), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_524), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_536), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_648), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_784), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_608), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_800), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_896), by decide +kernel⟩
  | 11 => Sum.inr ⟨(false, vertices_29), by decide +kernel⟩
  | 12 => Sum.inl 0
  | 13 => Sum.inr ⟨(false, vertices_103), by decide +kernel⟩
  | 14 => Sum.inr ⟨(false, vertices_167), by decide +kernel⟩
  | 15 => Sum.inl 1
  | 16 => Sum.inr ⟨(false, vertices_397), by decide +kernel⟩
  | 17 => Sum.inr ⟨(false, vertices_597), by decide +kernel⟩
  | 18 => Sum.inl 2
  | 19 => Sum.inr ⟨(false, vertices_345), by decide +kernel⟩
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
cert_row 0 1 0 2 6 8 654
cert_row 1 0 4 6 7 8 930
cert_row 2 2 3 6 7 8 920
cert_row 3 3 4 5 7 8 880
cert_rows
cert_pivot_2 1 0 2 3
cert_heightProof 4
cert_coverFacet 0 654
cert_cover_3 0 0 0 1 2 6
cert_coverFacet 1 582
cert_cover_4 1 0 1 5 8
cert_coverFacet 2 610
cert_cover_4 2 0 4 5 8
cert_coverFacet 3 930
cert_cover_3 3 0 1 4 6 7
cert_coverFacet 4 540
cert_cover_4 4 1 2 3 8
cert_coverFacet 5 920
cert_cover_3 5 2 2 3 6 7
cert_coverFacet 6 880
cert_cover_3 6 3 3 4 5 7
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_101

end
end BundlePart12

section BundlePart13
/- Source: ProjectionCertificates/P0_102.lean -/





@[expose] public section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_102

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [583, 781, 453, 409, 713, 310, 534, 358, 562, 738, 788, 696, 792, 496, 69, 261, 517, 137, 265, 521, 193, 577, 385, 22, 294, 70, 518, 50, 530, 98, 546, 578, 276, 532, 324, 772, 152, 280, 536, 648, 776, 176, 304, 560, 400, 784, 224, 352, 672, 448, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_583, vertices_781, vertices_453, vertices_409, vertices_713, vertices_310, vertices_534, vertices_358, vertices_562, vertices_738, vertices_788, vertices_696, vertices_792, vertices_496] (by decide +kernel)
  polygons := literalFinset [vertices_69, vertices_261, vertices_517, vertices_137, vertices_265, vertices_521, vertices_193, vertices_577, vertices_385, vertices_22, vertices_294, vertices_70, vertices_518, vertices_50, vertices_530, vertices_98, vertices_546, vertices_578, vertices_276, vertices_532, vertices_324, vertices_772, vertices_152, vertices_280, vertices_536, vertices_648, vertices_776, vertices_176, vertices_304, vertices_560, vertices_400, vertices_784, vertices_224, vertices_352, vertices_672, vertices_448, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_583), (false, vertices_781), (false, vertices_453), (false, vertices_409), (false, vertices_713), (true, vertices_22), (true, vertices_294), (true, vertices_50), (true, vertices_530), (true, vertices_98), (true, vertices_546), (true, vertices_276), (true, vertices_532), (true, vertices_536), (true, vertices_176), (true, vertices_304), (true, vertices_560), (true, vertices_784), (true, vertices_224), (true, vertices_352), (true, vertices_672)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 18 21 24 25 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_583) then 16 else
  if p.val = (false, vertices_781) then 19 else
  if p.val = (false, vertices_453) then 20 else
  if p.val = (false, vertices_409) then 22 else
  if p.val = (false, vertices_713) then 23 else
  if p.val = (true, vertices_22) then 0 else
  if p.val = (true, vertices_294) then 17 else
  if p.val = (true, vertices_50) then 1 else
  if p.val = (true, vertices_530) then 2 else
  if p.val = (true, vertices_98) then 3 else
  if p.val = (true, vertices_546) then 4 else
  if p.val = (true, vertices_276) then 5 else
  if p.val = (true, vertices_532) then 6 else
  if p.val = (true, vertices_536) then 7 else
  if p.val = (true, vertices_176) then 8 else
  if p.val = (true, vertices_304) then 9 else
  if p.val = (true, vertices_560) then 10 else
  if p.val = (true, vertices_784) then 11 else
  if p.val = (true, vertices_224) then 12 else
  if p.val = (true, vertices_352) then 13 else
  if p.val = (true, vertices_672) then 14 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_22), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_50), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_530), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_98), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_546), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_276), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_532), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_536), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_176), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_304), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_560), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_784), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_224), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_352), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_672), by decide +kernel⟩
  | 15 => Sum.inl 0
  | 16 => Sum.inr ⟨(false, vertices_583), by decide +kernel⟩
  | 17 => Sum.inr ⟨(true, vertices_294), by decide +kernel⟩
  | 18 => Sum.inl 1
  | 19 => Sum.inr ⟨(false, vertices_781), by decide +kernel⟩
  | 20 => Sum.inr ⟨(false, vertices_453), by decide +kernel⟩
  | 21 => Sum.inl 2
  | 22 => Sum.inr ⟨(false, vertices_409), by decide +kernel⟩
  | 23 => Sum.inr ⟨(false, vertices_713), by decide +kernel⟩
  | 24 => Sum.inl 3
  | 25 => Sum.inl 4
  | 26 => Sum.inl 5
  | 27 => Sum.inl 6
  | 28 => Sum.inl 7
  | 29 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row 0 2 3 4 6 8 696
cert_row 1 8 0 4 5 6 738
cert_row 2 3 4 5 6 7 496
cert_row_3 3 4 1 7 0 294
cert_rows
cert_pivot_2 2 8 3 0
cert_heightProof 4
cert_coverFacet 0 310
cert_cover_3 0 0 3 1 3 4
cert_coverFacet 1 534
cert_cover_4 1 0 1 3 8
cert_coverFacet 2 358
cert_cover_3 2 0 3 1 4 5
cert_coverFacet 3 562
cert_cover_4 3 0 3 4 8
cert_coverFacet 4 738
cert_cover_3 4 0 1 4 5 6
cert_coverFacet 5 788
cert_cover_4 5 1 3 7 8
cert_coverFacet 6 696
cert_cover_3 6 2 0 3 4 6
cert_coverFacet 7 792
cert_cover_4 7 2 3 7 8
cert_coverFacet 8 496
cert_cover_3 8 3 2 4 5 6
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_102

end
end BundlePart13

section BundlePart14
/- Source: ProjectionCertificates/P0_105.lean -/





@[expose] public section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_105

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [451, 29, 205, 533, 677, 345, 913, 230, 618, 842, 930, 796, 108, 556, 13, 21, 133, 517, 25, 73, 273, 529, 193, 321, 385, 641, 586, 98, 162, 546, 194, 322, 386, 770, 28, 44, 76, 524, 532, 100, 164, 548, 196, 280, 104, 552, 328, 776, 784, 672, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_451, vertices_29, vertices_205, vertices_533, vertices_677, vertices_345, vertices_913, vertices_230, vertices_618, vertices_842, vertices_930, vertices_796, vertices_108, vertices_556] (by decide +kernel)
  polygons := literalFinset [vertices_13, vertices_21, vertices_133, vertices_517, vertices_25, vertices_73, vertices_273, vertices_529, vertices_193, vertices_321, vertices_385, vertices_641, vertices_586, vertices_98, vertices_162, vertices_546, vertices_194, vertices_322, vertices_386, vertices_770, vertices_28, vertices_44, vertices_76, vertices_524, vertices_532, vertices_100, vertices_164, vertices_548, vertices_196, vertices_280, vertices_104, vertices_552, vertices_328, vertices_776, vertices_784, vertices_672, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_451), (false, vertices_29), (false, vertices_205), (false, vertices_533), (false, vertices_677), (false, vertices_345), (false, vertices_913), (true, vertices_586), (true, vertices_98), (true, vertices_162), (true, vertices_546), (true, vertices_770), (true, vertices_44), (true, vertices_524), (true, vertices_100), (true, vertices_104), (true, vertices_552), (true, vertices_776)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 12 15 18 20 22 23 24 25 26
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_451) then 13 else
  if p.val = (false, vertices_29) then 10 else
  if p.val = (false, vertices_205) then 16 else
  if p.val = (false, vertices_533) then 11 else
  if p.val = (false, vertices_677) then 17 else
  if p.val = (false, vertices_345) then 19 else
  if p.val = (false, vertices_913) then 21 else
  if p.val = (true, vertices_586) then 14 else
  if p.val = (true, vertices_98) then 0 else
  if p.val = (true, vertices_162) then 1 else
  if p.val = (true, vertices_546) then 2 else
  if p.val = (true, vertices_770) then 3 else
  if p.val = (true, vertices_44) then 4 else
  if p.val = (true, vertices_524) then 5 else
  if p.val = (true, vertices_100) then 6 else
  if p.val = (true, vertices_104) then 7 else
  if p.val = (true, vertices_552) then 8 else
  if p.val = (true, vertices_776) then 9 else
  0
cert_priority
cert_nodeAtPriority_7 0 98 1 162 2 546 770 44 524 100 104 552 776 29 533 451 586 205 677 345 913
cert_priority_injective
cert_incidenceProof
cert_row 0 3 1 2 7 8 796
cert_row 1 1 0 4 5 6 230
cert_row 2 4 0 6 7 8 930
cert_row_3 3 5 2 8 0 586
cert_rows
cert_pivot_2 3 1 4 0
cert_heightProof 4
cert_coverFacet 0 230
cert_cover_3 0 0 1 1 4 5
cert_coverFacet 1 618
cert_cover_3 1 0 3 2 4 5
cert_coverFacet 2 842
cert_cover_3 2 0 3 2 5 7
cert_coverFacet 3 930
cert_cover_3 3 0 2 4 6 7
cert_coverFacet 4 796
cert_cover_3 4 1 0 2 3 7
cert_coverFacet 5 108
cert_cover_4 5 1 2 4 5
cert_coverFacet 6 556
cert_cover_4 6 1 2 4 8
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_105

end
end BundlePart14

section BundlePart15
/- Source: ProjectionCertificates/P0_106.lean -/





@[expose] public section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_106

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [647, 781, 389, 617, 457, 721, 310, 150, 806, 626, 658, 468, 376, 808, 133, 261, 517, 73, 265, 521, 193, 577, 385, 641, 22, 294, 134, 518, 50, 146, 530, 546, 642, 148, 276, 388, 772, 104, 296, 552, 328, 776, 112, 304, 208, 336, 592, 656, 608, 800, 448]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_647, vertices_781, vertices_389, vertices_617, vertices_457, vertices_721, vertices_310, vertices_150, vertices_806, vertices_626, vertices_658, vertices_468, vertices_376, vertices_808] (by decide +kernel)
  polygons := literalFinset [vertices_133, vertices_261, vertices_517, vertices_73, vertices_265, vertices_521, vertices_193, vertices_577, vertices_385, vertices_641, vertices_22, vertices_294, vertices_134, vertices_518, vertices_50, vertices_146, vertices_530, vertices_546, vertices_642, vertices_148, vertices_276, vertices_388, vertices_772, vertices_104, vertices_296, vertices_552, vertices_328, vertices_776, vertices_112, vertices_304, vertices_208, vertices_336, vertices_592, vertices_656, vertices_608, vertices_800, vertices_448] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_647), (false, vertices_781), (false, vertices_389), (false, vertices_617), (false, vertices_457), (false, vertices_721), (true, vertices_22), (true, vertices_294), (true, vertices_50), (true, vertices_146), (true, vertices_530), (true, vertices_546), (true, vertices_148), (true, vertices_276), (true, vertices_296), (true, vertices_112), (true, vertices_304), (true, vertices_336), (true, vertices_800)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 13 16 18 21 23 24 25 26 27
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_647) then 14 else
  if p.val = (false, vertices_781) then 17 else
  if p.val = (false, vertices_389) then 12 else
  if p.val = (false, vertices_617) then 19 else
  if p.val = (false, vertices_457) then 20 else
  if p.val = (false, vertices_721) then 22 else
  if p.val = (true, vertices_22) then 0 else
  if p.val = (true, vertices_294) then 15 else
  if p.val = (true, vertices_50) then 1 else
  if p.val = (true, vertices_146) then 2 else
  if p.val = (true, vertices_530) then 3 else
  if p.val = (true, vertices_546) then 4 else
  if p.val = (true, vertices_148) then 5 else
  if p.val = (true, vertices_276) then 6 else
  if p.val = (true, vertices_296) then 7 else
  if p.val = (true, vertices_112) then 8 else
  if p.val = (true, vertices_304) then 9 else
  if p.val = (true, vertices_336) then 10 else
  if p.val = (true, vertices_800) then 11 else
  0
cert_priority
cert_nodeAtPriority_56 22 50 146 530 546 148 276 296 112 304 336 800 389 647 294 781 617 457 721
cert_priority_injective
cert_incidenceProof
cert_row 0 8 0 3 4 5 626
cert_row 1 6 1 3 5 7 468
cert_row 2 2 3 4 5 7 376
cert_row_3 3 4 1 7 0 294
cert_rows
cert_pivot_2 8 6 2 0
cert_heightProof 4
cert_coverFacet 0 310
cert_cover_3 0 0 3 1 3 4
cert_coverFacet 1 150
cert_cover_4 1 0 1 3 6
cert_coverFacet 2 806
cert_cover_3 2 0 3 1 4 8
cert_coverFacet 3 626
cert_cover_3 3 0 0 3 4 5
cert_coverFacet 4 658
cert_cover_4 4 0 3 6 8
cert_coverFacet 5 468
cert_cover_3 5 1 1 3 5 6
cert_coverFacet 6 376
cert_cover_3 6 2 2 3 4 5
cert_coverFacet 7 808
cert_cover_4 7 2 4 7 8
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_106

end
end BundlePart15

section BundlePart16
/- Source: ProjectionCertificates/P0_107.lean -/





@[expose] public section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_107

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [563, 147, 835, 387, 453, 617, 241, 406, 786, 316, 236, 844, 180, 824, 19, 131, 259, 515, 49, 145, 97, 545, 193, 321, 577, 385, 146, 274, 530, 386, 770, 44, 76, 268, 52, 148, 276, 164, 196, 324, 388, 312, 104, 552, 584, 776, 176, 560, 784, 224, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_563, vertices_147, vertices_835, vertices_387, vertices_453, vertices_617, vertices_241, vertices_406, vertices_786, vertices_316, vertices_236, vertices_844, vertices_180, vertices_824] (by decide +kernel)
  polygons := literalFinset [vertices_19, vertices_131, vertices_259, vertices_515, vertices_49, vertices_145, vertices_97, vertices_545, vertices_193, vertices_321, vertices_577, vertices_385, vertices_146, vertices_274, vertices_530, vertices_386, vertices_770, vertices_44, vertices_76, vertices_268, vertices_52, vertices_148, vertices_276, vertices_164, vertices_196, vertices_324, vertices_388, vertices_312, vertices_104, vertices_552, vertices_584, vertices_776, vertices_176, vertices_560, vertices_784, vertices_224, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_563), (false, vertices_147), (false, vertices_835), (false, vertices_387), (false, vertices_453), (false, vertices_617), (false, vertices_241), (true, vertices_274), (true, vertices_44), (true, vertices_76), (true, vertices_268), (true, vertices_52), (true, vertices_148), (true, vertices_276), (true, vertices_164), (true, vertices_312), (true, vertices_776), (true, vertices_784)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 12 15 17 20 22 23 24 25 26
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_563) then 13 else
  if p.val = (false, vertices_147) then 10 else
  if p.val = (false, vertices_835) then 14 else
  if p.val = (false, vertices_387) then 11 else
  if p.val = (false, vertices_453) then 16 else
  if p.val = (false, vertices_617) then 18 else
  if p.val = (false, vertices_241) then 21 else
  if p.val = (true, vertices_274) then 0 else
  if p.val = (true, vertices_44) then 1 else
  if p.val = (true, vertices_76) then 2 else
  if p.val = (true, vertices_268) then 3 else
  if p.val = (true, vertices_52) then 4 else
  if p.val = (true, vertices_148) then 5 else
  if p.val = (true, vertices_276) then 6 else
  if p.val = (true, vertices_164) then 7 else
  if p.val = (true, vertices_312) then 19 else
  if p.val = (true, vertices_776) then 8 else
  if p.val = (true, vertices_784) then 9 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_274), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_44), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_76), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_268), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_52), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_148), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_276), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_164), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_776), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_784), by decide +kernel⟩
  | 10 => Sum.inr ⟨(false, vertices_147), by decide +kernel⟩
  | 11 => Sum.inr ⟨(false, vertices_387), by decide +kernel⟩
  | 12 => Sum.inl 0
  | 13 => Sum.inr ⟨(false, vertices_563), by decide +kernel⟩
  | 14 => Sum.inr ⟨(false, vertices_835), by decide +kernel⟩
  | 15 => Sum.inl 1
  | 16 => Sum.inr ⟨(false, vertices_453), by decide +kernel⟩
  | 17 => Sum.inl 2
  | 18 => Sum.inr ⟨(false, vertices_617), by decide +kernel⟩
  | 19 => Sum.inr ⟨(true, vertices_312), by decide +kernel⟩
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
cert_row 0 0 1 3 6 7 406
cert_row 1 6 1 2 4 5 236
cert_row 2 1 2 5 7 8 844
cert_row_3 3 4 3 7 2 312
cert_rows
cert_pivot_2 0 6 1 2
cert_heightProof 4
cert_coverFacet 0 406
cert_cover_3 0 0 0 1 3 6
cert_coverFacet 1 786
cert_cover_4 1 0 3 7 8
cert_coverFacet 2 316
cert_cover_3 2 1 3 2 3 4
cert_coverFacet 3 236
cert_cover_3 3 1 1 2 4 5
cert_coverFacet 4 844
cert_cover_3 4 1 2 2 5 7
cert_coverFacet 5 180
cert_cover_4 5 1 3 4 6
cert_coverFacet 6 824
cert_cover_3 6 2 3 3 4 8
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_107

end
end BundlePart16

section BundlePart17
/- Source: ProjectionCertificates/P0_121.lean -/





@[expose] public section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_121

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [787, 709, 601, 281, 457, 929, 110, 590, 678, 314, 538, 802, 484, 360, 25, 73, 265, 273, 529, 193, 577, 385, 641, 769, 78, 38, 518, 26, 42, 522, 274, 530, 290, 546, 770, 100, 164, 196, 580, 644, 280, 536, 104, 296, 328, 584, 352, 416, 672, 800, 448]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_787, vertices_709, vertices_601, vertices_281, vertices_457, vertices_929, vertices_110, vertices_590, vertices_678, vertices_314, vertices_538, vertices_802, vertices_484, vertices_360] (by decide +kernel)
  polygons := literalFinset [vertices_25, vertices_73, vertices_265, vertices_273, vertices_529, vertices_193, vertices_577, vertices_385, vertices_641, vertices_769, vertices_78, vertices_38, vertices_518, vertices_26, vertices_42, vertices_522, vertices_274, vertices_530, vertices_290, vertices_546, vertices_770, vertices_100, vertices_164, vertices_196, vertices_580, vertices_644, vertices_280, vertices_536, vertices_104, vertices_296, vertices_328, vertices_584, vertices_352, vertices_416, vertices_672, vertices_800, vertices_448] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_787), (false, vertices_709), (false, vertices_601), (false, vertices_281), (false, vertices_457), (false, vertices_929), (true, vertices_78), (true, vertices_38), (true, vertices_518), (true, vertices_26), (true, vertices_42), (true, vertices_522), (true, vertices_290), (true, vertices_546), (true, vertices_100), (true, vertices_164), (true, vertices_104), (true, vertices_296), (true, vertices_352)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 13 16 18 21 22 24 25 26 27
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_787) then 14 else
  if p.val = (false, vertices_709) then 17 else
  if p.val = (false, vertices_601) then 19 else
  if p.val = (false, vertices_281) then 12 else
  if p.val = (false, vertices_457) then 20 else
  if p.val = (false, vertices_929) then 23 else
  if p.val = (true, vertices_78) then 15 else
  if p.val = (true, vertices_38) then 0 else
  if p.val = (true, vertices_518) then 1 else
  if p.val = (true, vertices_26) then 2 else
  if p.val = (true, vertices_42) then 3 else
  if p.val = (true, vertices_522) then 4 else
  if p.val = (true, vertices_290) then 5 else
  if p.val = (true, vertices_546) then 6 else
  if p.val = (true, vertices_100) then 7 else
  if p.val = (true, vertices_164) then 8 else
  if p.val = (true, vertices_104) then 9 else
  if p.val = (true, vertices_296) then 10 else
  if p.val = (true, vertices_352) then 11 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_38), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_518), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_26), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_42), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_522), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_290), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_546), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_100), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_164), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_104), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_296), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_352), by decide +kernel⟩
  | 12 => Sum.inr ⟨(false, vertices_281), by decide +kernel⟩
  | 13 => Sum.inl 0
  | 14 => Sum.inr ⟨(false, vertices_787), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_78), by decide +kernel⟩
  | 16 => Sum.inl 1
  | 17 => Sum.inr ⟨(false, vertices_709), by decide +kernel⟩
  | 18 => Sum.inl 2
  | 19 => Sum.inr ⟨(false, vertices_601), by decide +kernel⟩
  | 20 => Sum.inr ⟨(false, vertices_457), by decide +kernel⟩
  | 21 => Sum.inl 3
  | 22 => Sum.inl 4
  | 23 => Sum.inr ⟨(false, vertices_929), by decide +kernel⟩
  | 24 => Sum.inl 5
  | 25 => Sum.inl 6
  | 26 => Sum.inl 7
  | 27 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row 0 8 0 1 4 6 678
cert_row 1 3 0 2 4 7 314
cert_row 2 4 1 5 6 7 484
cert_row_3 3 2 1 5 0 78
cert_rows
cert_pivot_2 8 3 4 0
cert_heightProof 4
cert_coverFacet 0 110
cert_cover_3 0 0 3 1 2 4
cert_coverFacet 1 590
cert_cover_3 1 0 3 1 2 8
cert_coverFacet 2 678
cert_cover_3 2 0 0 1 4 6
cert_coverFacet 3 314
cert_cover_3 3 0 1 2 3 4
cert_coverFacet 4 538
cert_cover_4 4 0 2 3 8
cert_coverFacet 5 802
cert_cover_4 5 0 4 7 8
cert_coverFacet 6 484
cert_cover_3 6 1 2 4 5 6
cert_coverFacet 7 360
cert_cover_4 7 2 4 5 7
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_121

end
end BundlePart17

section BundlePart18
/- Source: ProjectionCertificates/P0_122.lean -/





@[expose] public section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_122

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [295, 179, 387, 613, 453, 713, 673, 154, 794, 458, 818, 844, 804, 696, 35, 131, 259, 37, 69, 261, 161, 545, 193, 577, 385, 641, 26, 138, 266, 50, 146, 786, 290, 386, 292, 548, 324, 580, 772, 152, 536, 200, 328, 584, 648, 776, 176, 560, 672, 800, 448]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_295, vertices_179, vertices_387, vertices_613, vertices_453, vertices_713, vertices_673, vertices_154, vertices_794, vertices_458, vertices_818, vertices_844, vertices_804, vertices_696] (by decide +kernel)
  polygons := literalFinset [vertices_35, vertices_131, vertices_259, vertices_37, vertices_69, vertices_261, vertices_161, vertices_545, vertices_193, vertices_577, vertices_385, vertices_641, vertices_26, vertices_138, vertices_266, vertices_50, vertices_146, vertices_786, vertices_290, vertices_386, vertices_292, vertices_548, vertices_324, vertices_580, vertices_772, vertices_152, vertices_536, vertices_200, vertices_328, vertices_584, vertices_648, vertices_776, vertices_176, vertices_560, vertices_672, vertices_800, vertices_448] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_295), (false, vertices_179), (false, vertices_387), (false, vertices_613), (false, vertices_453), (false, vertices_713), (false, vertices_673), (true, vertices_26), (true, vertices_138), (true, vertices_266), (true, vertices_786), (true, vertices_772), (true, vertices_152), (true, vertices_536), (true, vertices_328), (true, vertices_776), (true, vertices_560), (true, vertices_800)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 16 12 19 21 22 23 24 25 26
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_295) then 13 else
  if p.val = (false, vertices_179) then 17 else
  if p.val = (false, vertices_387) then 10 else
  if p.val = (false, vertices_613) then 14 else
  if p.val = (false, vertices_453) then 15 else
  if p.val = (false, vertices_713) then 20 else
  if p.val = (false, vertices_673) then 11 else
  if p.val = (true, vertices_26) then 0 else
  if p.val = (true, vertices_138) then 1 else
  if p.val = (true, vertices_266) then 2 else
  if p.val = (true, vertices_786) then 18 else
  if p.val = (true, vertices_772) then 3 else
  if p.val = (true, vertices_152) then 4 else
  if p.val = (true, vertices_536) then 5 else
  if p.val = (true, vertices_328) then 6 else
  if p.val = (true, vertices_776) then 7 else
  if p.val = (true, vertices_560) then 8 else
  if p.val = (true, vertices_800) then 9 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_26), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_138), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_266), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_772), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_152), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_536), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_328), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_776), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_560), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_800), by decide +kernel⟩
  | 10 => Sum.inr ⟨(false, vertices_387), by decide +kernel⟩
  | 11 => Sum.inr ⟨(false, vertices_673), by decide +kernel⟩
  | 12 => Sum.inl 1
  | 13 => Sum.inr ⟨(false, vertices_295), by decide +kernel⟩
  | 14 => Sum.inr ⟨(false, vertices_613), by decide +kernel⟩
  | 15 => Sum.inr ⟨(false, vertices_453), by decide +kernel⟩
  | 16 => Sum.inl 0
  | 17 => Sum.inr ⟨(false, vertices_179), by decide +kernel⟩
  | 18 => Sum.inr ⟨(true, vertices_786), by decide +kernel⟩
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
cert_row 0 1 2 5 7 8 844
cert_row 1 5 0 2 6 7 458
cert_row 2 2 3 4 6 8 696
cert_row_3 3 7 3 8 0 786
cert_rows
cert_pivot_2 1 5 2 0
cert_heightProof 4
cert_coverFacet 0 154
cert_cover_4 0 0 2 3 6
cert_coverFacet 1 794
cert_cover_3 1 0 3 2 3 7
cert_coverFacet 2 458
cert_cover_3 2 0 1 2 5 6
cert_coverFacet 3 818
cert_cover_3 3 0 3 3 4 7
cert_coverFacet 4 844
cert_cover_3 4 1 0 2 5 7
cert_coverFacet 5 804
cert_cover_4 5 1 4 7 8
cert_coverFacet 6 696
cert_cover_3 6 2 2 3 4 6
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_122

end
end BundlePart18

section BundlePart19
/- Source: ProjectionCertificates/P0_130.lean -/





@[expose] public section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_130

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [675, 213, 613, 165, 601, 913, 422, 794, 362, 618, 898, 372, 404, 344, 37, 69, 133, 81, 145, 529, 161, 545, 577, 641, 106, 266, 522, 162, 290, 546, 386, 642, 770, 84, 148, 276, 100, 164, 292, 388, 88, 280, 536, 328, 584, 336, 400, 784, 352, 608, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_675, vertices_213, vertices_613, vertices_165, vertices_601, vertices_913, vertices_422, vertices_794, vertices_362, vertices_618, vertices_898, vertices_372, vertices_404, vertices_344] (by decide +kernel)
  polygons := literalFinset [vertices_37, vertices_69, vertices_133, vertices_81, vertices_145, vertices_529, vertices_161, vertices_545, vertices_577, vertices_641, vertices_106, vertices_266, vertices_522, vertices_162, vertices_290, vertices_546, vertices_386, vertices_642, vertices_770, vertices_84, vertices_148, vertices_276, vertices_100, vertices_164, vertices_292, vertices_388, vertices_88, vertices_280, vertices_536, vertices_328, vertices_584, vertices_336, vertices_400, vertices_784, vertices_352, vertices_608, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_675), (false, vertices_213), (false, vertices_613), (false, vertices_165), (false, vertices_601), (false, vertices_913), (true, vertices_106), (true, vertices_266), (true, vertices_522), (true, vertices_290), (true, vertices_386), (true, vertices_770), (true, vertices_276), (true, vertices_292), (true, vertices_388), (true, vertices_280), (true, vertices_328), (true, vertices_336), (true, vertices_352)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 13 16 19 21 23 24 25 26 27
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_675) then 14 else
  if p.val = (false, vertices_213) then 17 else
  if p.val = (false, vertices_613) then 18 else
  if p.val = (false, vertices_165) then 12 else
  if p.val = (false, vertices_601) then 20 else
  if p.val = (false, vertices_913) then 22 else
  if p.val = (true, vertices_106) then 15 else
  if p.val = (true, vertices_266) then 0 else
  if p.val = (true, vertices_522) then 1 else
  if p.val = (true, vertices_290) then 2 else
  if p.val = (true, vertices_386) then 3 else
  if p.val = (true, vertices_770) then 4 else
  if p.val = (true, vertices_276) then 5 else
  if p.val = (true, vertices_292) then 6 else
  if p.val = (true, vertices_388) then 7 else
  if p.val = (true, vertices_280) then 8 else
  if p.val = (true, vertices_328) then 9 else
  if p.val = (true, vertices_336) then 10 else
  if p.val = (true, vertices_352) then 11 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_266), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_522), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_290), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_386), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_770), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_276), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_292), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_388), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_280), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_328), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_336), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_352), by decide +kernel⟩
  | 12 => Sum.inr ⟨(false, vertices_165), by decide +kernel⟩
  | 13 => Sum.inl 0
  | 14 => Sum.inr ⟨(false, vertices_675), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_106), by decide +kernel⟩
  | 16 => Sum.inl 1
  | 17 => Sum.inr ⟨(false, vertices_213), by decide +kernel⟩
  | 18 => Sum.inr ⟨(false, vertices_613), by decide +kernel⟩
  | 19 => Sum.inl 2
  | 20 => Sum.inr ⟨(false, vertices_601), by decide +kernel⟩
  | 21 => Sum.inl 3
  | 22 => Sum.inr ⟨(false, vertices_913), by decide +kernel⟩
  | 23 => Sum.inl 4
  | 24 => Sum.inl 5
  | 25 => Sum.inl 6
  | 26 => Sum.inl 7
  | 27 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row 0 6 0 1 4 7 422
cert_row 1 8 0 2 3 7 794
cert_row 2 1 3 4 5 7 372
cert_row_3 3 4 2 5 0 106
cert_rows
cert_pivot_2 6 8 1 0
cert_heightProof 4
cert_coverFacet 0 422
cert_cover_3 0 0 0 1 4 6
cert_coverFacet 1 794
cert_cover_3 1 0 1 2 3 7
cert_coverFacet 2 362
cert_cover_3 2 0 3 2 4 7
cert_coverFacet 3 618
cert_cover_3 3 0 3 2 4 8
cert_coverFacet 4 898
cert_cover_4 4 0 6 7 8
cert_coverFacet 5 372
cert_cover_3 5 1 2 3 4 5
cert_coverFacet 6 404
cert_cover_4 6 1 3 6 7
cert_coverFacet 7 344
cert_cover_4 7 2 3 5 7
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_130

end
end BundlePart19

section BundlePart20
/- Source: ProjectionCertificates/P0_131.lean -/





@[expose] public section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_131

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [779, 541, 117, 805, 281, 465, 353, 410, 682, 482, 802, 724, 740, 664, 21, 37, 517, 25, 265, 521, 81, 273, 97, 289, 321, 769, 138, 266, 522, 162, 290, 546, 386, 770, 84, 532, 100, 548, 708, 152, 280, 536, 648, 208, 400, 656, 224, 352, 672, 800, 448]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_779, vertices_541, vertices_117, vertices_805, vertices_281, vertices_465, vertices_353, vertices_410, vertices_682, vertices_482, vertices_802, vertices_724, vertices_740, vertices_664] (by decide +kernel)
  polygons := literalFinset [vertices_21, vertices_37, vertices_517, vertices_25, vertices_265, vertices_521, vertices_81, vertices_273, vertices_97, vertices_289, vertices_321, vertices_769, vertices_138, vertices_266, vertices_522, vertices_162, vertices_290, vertices_546, vertices_386, vertices_770, vertices_84, vertices_532, vertices_100, vertices_548, vertices_708, vertices_152, vertices_280, vertices_536, vertices_648, vertices_208, vertices_400, vertices_656, vertices_224, vertices_352, vertices_672, vertices_800, vertices_448] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_779), (false, vertices_541), (false, vertices_117), (false, vertices_805), (false, vertices_281), (false, vertices_465), (false, vertices_353), (true, vertices_138), (true, vertices_162), (true, vertices_290), (true, vertices_546), (true, vertices_386), (true, vertices_708), (true, vertices_152), (true, vertices_648), (true, vertices_656), (true, vertices_224), (true, vertices_672)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 12 19 14 16 22 23 24 25 26
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_779) then 13 else
  if p.val = (false, vertices_541) then 15 else
  if p.val = (false, vertices_117) then 17 else
  if p.val = (false, vertices_805) then 20 else
  if p.val = (false, vertices_281) then 10 else
  if p.val = (false, vertices_465) then 18 else
  if p.val = (false, vertices_353) then 11 else
  if p.val = (true, vertices_138) then 0 else
  if p.val = (true, vertices_162) then 1 else
  if p.val = (true, vertices_290) then 2 else
  if p.val = (true, vertices_546) then 3 else
  if p.val = (true, vertices_386) then 4 else
  if p.val = (true, vertices_708) then 21 else
  if p.val = (true, vertices_152) then 5 else
  if p.val = (true, vertices_648) then 6 else
  if p.val = (true, vertices_656) then 7 else
  if p.val = (true, vertices_224) then 8 else
  if p.val = (true, vertices_672) then 9 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_138), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_162), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_290), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_546), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_386), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_152), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_648), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_656), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_224), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_672), by decide +kernel⟩
  | 10 => Sum.inr ⟨(false, vertices_281), by decide +kernel⟩
  | 11 => Sum.inr ⟨(false, vertices_353), by decide +kernel⟩
  | 12 => Sum.inl 0
  | 13 => Sum.inr ⟨(false, vertices_779), by decide +kernel⟩
  | 14 => Sum.inl 2
  | 15 => Sum.inr ⟨(false, vertices_541), by decide +kernel⟩
  | 16 => Sum.inl 3
  | 17 => Sum.inr ⟨(false, vertices_117), by decide +kernel⟩
  | 18 => Sum.inr ⟨(false, vertices_465), by decide +kernel⟩
  | 19 => Sum.inl 1
  | 20 => Sum.inr ⟨(false, vertices_805), by decide +kernel⟩
  | 21 => Sum.inr ⟨(true, vertices_708), by decide +kernel⟩
  | 22 => Sum.inl 4
  | 23 => Sum.inl 5
  | 24 => Sum.inl 6
  | 25 => Sum.inl 7
  | 26 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row 0 3 0 2 6 7 410
cert_row 1 2 0 4 6 8 682
cert_row 2 0 4 5 6 7 482
cert_row_3 3 6 5 8 1 708
cert_rows
cert_pivot_2 3 2 0 1
cert_heightProof 4
cert_coverFacet 0 410
cert_cover_3 0 0 0 2 3 6
cert_coverFacet 1 682
cert_cover_3 1 0 1 2 4 6
cert_coverFacet 2 482
cert_cover_3 2 0 2 4 5 6
cert_coverFacet 3 802
cert_cover_4 3 0 4 7 8
cert_coverFacet 4 724
cert_cover_3 4 1 3 3 5 6
cert_coverFacet 5 740
cert_cover_3 5 1 3 4 5 6
cert_coverFacet 6 664
cert_cover_4 6 2 3 6 8
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_131

end
end BundlePart20

section BundlePart21
/- Source: ProjectionCertificates/P0_132.lean -/





@[expose] public section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_132

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [107, 781, 661, 389, 297, 713, 481, 790, 810, 586, 242, 306, 722, 436, 133, 261, 517, 41, 73, 265, 521, 97, 289, 193, 385, 641, 42, 74, 522, 50, 210, 274, 530, 98, 290, 578, 770, 148, 276, 532, 388, 772, 296, 584, 776, 176, 304, 656, 224, 416, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_107, vertices_781, vertices_661, vertices_389, vertices_297, vertices_713, vertices_481, vertices_790, vertices_810, vertices_586, vertices_242, vertices_306, vertices_722, vertices_436] (by decide +kernel)
  polygons := literalFinset [vertices_133, vertices_261, vertices_517, vertices_41, vertices_73, vertices_265, vertices_521, vertices_97, vertices_289, vertices_193, vertices_385, vertices_641, vertices_42, vertices_74, vertices_522, vertices_50, vertices_210, vertices_274, vertices_530, vertices_98, vertices_290, vertices_578, vertices_770, vertices_148, vertices_276, vertices_532, vertices_388, vertices_772, vertices_296, vertices_584, vertices_776, vertices_176, vertices_304, vertices_656, vertices_224, vertices_416, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_107), (false, vertices_781), (false, vertices_661), (false, vertices_389), (false, vertices_297), (false, vertices_713), (false, vertices_481), (true, vertices_522), (true, vertices_50), (true, vertices_210), (true, vertices_274), (true, vertices_530), (true, vertices_290), (true, vertices_578), (true, vertices_770), (true, vertices_276), (true, vertices_176), (true, vertices_304)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 12 15 18 20 21 23 24 25 26
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_107) then 13 else
  if p.val = (false, vertices_781) then 16 else
  if p.val = (false, vertices_661) then 17 else
  if p.val = (false, vertices_389) then 10 else
  if p.val = (false, vertices_297) then 11 else
  if p.val = (false, vertices_713) then 19 else
  if p.val = (false, vertices_481) then 22 else
  if p.val = (true, vertices_522) then 0 else
  if p.val = (true, vertices_50) then 1 else
  if p.val = (true, vertices_210) then 14 else
  if p.val = (true, vertices_274) then 2 else
  if p.val = (true, vertices_530) then 3 else
  if p.val = (true, vertices_290) then 4 else
  if p.val = (true, vertices_578) then 5 else
  if p.val = (true, vertices_770) then 6 else
  if p.val = (true, vertices_276) then 7 else
  if p.val = (true, vertices_176) then 8 else
  if p.val = (true, vertices_304) then 9 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_522), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_50), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_274), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_530), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_290), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_578), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_770), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_276), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_176), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_304), by decide +kernel⟩
  | 10 => Sum.inr ⟨(false, vertices_389), by decide +kernel⟩
  | 11 => Sum.inr ⟨(false, vertices_297), by decide +kernel⟩
  | 12 => Sum.inl 0
  | 13 => Sum.inr ⟨(false, vertices_107), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_210), by decide +kernel⟩
  | 15 => Sum.inl 1
  | 16 => Sum.inr ⟨(false, vertices_781), by decide +kernel⟩
  | 17 => Sum.inr ⟨(false, vertices_661), by decide +kernel⟩
  | 18 => Sum.inl 2
  | 19 => Sum.inr ⟨(false, vertices_713), by decide +kernel⟩
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
cert_row 0 2 0 4 7 8 810
cert_row 1 8 0 1 3 7 790
cert_row 2 1 3 4 6 7 436
cert_row_3 3 5 3 6 0 210
cert_rows
cert_pivot_2 2 8 1 0
cert_heightProof 4
cert_coverFacet 0 790
cert_cover_3 0 0 1 1 3 7
cert_coverFacet 1 810
cert_cover_3 1 0 0 2 4 7
cert_coverFacet 2 586
cert_cover_4 2 0 2 5 8
cert_coverFacet 3 242
cert_cover_3 3 0 3 3 4 5
cert_coverFacet 4 306
cert_cover_4 4 0 3 4 7
cert_coverFacet 5 722
cert_cover_3 5 0 3 3 5 8
cert_coverFacet 6 436
cert_cover_3 6 1 2 3 4 6
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_132

end
end BundlePart21

section BundlePart22
/- Source: ProjectionCertificates/P0_136.lean -/





@[expose] public section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_136

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [779, 805, 313, 601, 113, 737, 406, 678, 774, 218, 282, 714, 420, 496, 25, 265, 521, 49, 81, 97, 289, 545, 577, 769, 134, 262, 518, 26, 202, 266, 522, 146, 274, 642, 770, 164, 292, 548, 388, 772, 88, 280, 584, 112, 304, 208, 400, 224, 416, 672, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_779, vertices_805, vertices_313, vertices_601, vertices_113, vertices_737, vertices_406, vertices_678, vertices_774, vertices_218, vertices_282, vertices_714, vertices_420, vertices_496] (by decide +kernel)
  polygons := literalFinset [vertices_25, vertices_265, vertices_521, vertices_49, vertices_81, vertices_97, vertices_289, vertices_545, vertices_577, vertices_769, vertices_134, vertices_262, vertices_518, vertices_26, vertices_202, vertices_266, vertices_522, vertices_146, vertices_274, vertices_642, vertices_770, vertices_164, vertices_292, vertices_548, vertices_388, vertices_772, vertices_88, vertices_280, vertices_584, vertices_112, vertices_304, vertices_208, vertices_400, vertices_224, vertices_416, vertices_672, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_779), (false, vertices_805), (false, vertices_313), (false, vertices_601), (false, vertices_113), (false, vertices_737), (true, vertices_134), (true, vertices_262), (true, vertices_518), (true, vertices_26), (true, vertices_202), (true, vertices_146), (true, vertices_274), (true, vertices_642), (true, vertices_164), (true, vertices_388), (true, vertices_208), (true, vertices_400), (true, vertices_416)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 13 16 18 21 22 24 25 26 27
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_779) then 14 else
  if p.val = (false, vertices_805) then 17 else
  if p.val = (false, vertices_313) then 19 else
  if p.val = (false, vertices_601) then 20 else
  if p.val = (false, vertices_113) then 12 else
  if p.val = (false, vertices_737) then 23 else
  if p.val = (true, vertices_134) then 0 else
  if p.val = (true, vertices_262) then 1 else
  if p.val = (true, vertices_518) then 2 else
  if p.val = (true, vertices_26) then 3 else
  if p.val = (true, vertices_202) then 15 else
  if p.val = (true, vertices_146) then 4 else
  if p.val = (true, vertices_274) then 5 else
  if p.val = (true, vertices_642) then 6 else
  if p.val = (true, vertices_164) then 7 else
  if p.val = (true, vertices_388) then 8 else
  if p.val = (true, vertices_208) then 9 else
  if p.val = (true, vertices_400) then 10 else
  if p.val = (true, vertices_416) then 11 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_134), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_262), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_518), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_26), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_146), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_274), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_642), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_164), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_388), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_208), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_400), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_416), by decide +kernel⟩
  | 12 => Sum.inr ⟨(false, vertices_113), by decide +kernel⟩
  | 13 => Sum.inl 0
  | 14 => Sum.inr ⟨(false, vertices_779), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_202), by decide +kernel⟩
  | 16 => Sum.inl 1
  | 17 => Sum.inr ⟨(false, vertices_805), by decide +kernel⟩
  | 18 => Sum.inl 2
  | 19 => Sum.inr ⟨(false, vertices_313), by decide +kernel⟩
  | 20 => Sum.inr ⟨(false, vertices_601), by decide +kernel⟩
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
cert_row 0 8 0 1 4 6 678
cert_row 1 1 0 3 6 7 406
cert_row 2 3 4 5 6 7 496
cert_row_3 3 5 2 6 0 202
cert_rows
cert_pivot_2 8 1 3 0
cert_heightProof 4
cert_coverFacet 0 406
cert_cover_3 0 0 1 1 3 6
cert_coverFacet 1 678
cert_cover_3 1 0 0 1 4 6
cert_coverFacet 2 774
cert_cover_4 2 0 1 7 8
cert_coverFacet 3 218
cert_cover_3 3 0 3 2 3 5
cert_coverFacet 4 282
cert_cover_4 4 0 2 3 7
cert_coverFacet 5 714
cert_cover_3 5 0 3 2 5 8
cert_coverFacet 6 420
cert_cover_4 6 1 4 6 7
cert_coverFacet 7 496
cert_cover_3 7 3 2 4 5 6
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_136

end
end BundlePart22

section BundlePart23
/- Source: ProjectionCertificates/P0_137.lean -/





@[expose] public section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_137

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [659, 613, 681, 433, 849, 353, 558, 398, 342, 598, 650, 402, 364, 424, 145, 273, 529, 97, 161, 289, 545, 321, 577, 641, 14, 86, 262, 518, 138, 522, 146, 274, 530, 386, 642, 44, 268, 100, 548, 324, 580, 168, 296, 552, 392, 648, 336, 592, 400, 352, 416]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_659, vertices_613, vertices_681, vertices_433, vertices_849, vertices_353, vertices_558, vertices_398, vertices_342, vertices_598, vertices_650, vertices_402, vertices_364, vertices_424] (by decide +kernel)
  polygons := literalFinset [vertices_145, vertices_273, vertices_529, vertices_97, vertices_161, vertices_289, vertices_545, vertices_321, vertices_577, vertices_641, vertices_14, vertices_86, vertices_262, vertices_518, vertices_138, vertices_522, vertices_146, vertices_274, vertices_530, vertices_386, vertices_642, vertices_44, vertices_268, vertices_100, vertices_548, vertices_324, vertices_580, vertices_168, vertices_296, vertices_552, vertices_392, vertices_648, vertices_336, vertices_592, vertices_400, vertices_352, vertices_416] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_659), (false, vertices_613), (false, vertices_681), (false, vertices_433), (false, vertices_849), (false, vertices_353), (true, vertices_14), (true, vertices_86), (true, vertices_262), (true, vertices_518), (true, vertices_138), (true, vertices_522), (true, vertices_274), (true, vertices_386), (true, vertices_44), (true, vertices_268), (true, vertices_324), (true, vertices_296), (true, vertices_392)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 13 16 18 20 23 24 25 26 27
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_659) then 14 else
  if p.val = (false, vertices_613) then 17 else
  if p.val = (false, vertices_681) then 19 else
  if p.val = (false, vertices_433) then 21 else
  if p.val = (false, vertices_849) then 22 else
  if p.val = (false, vertices_353) then 12 else
  if p.val = (true, vertices_14) then 0 else
  if p.val = (true, vertices_86) then 15 else
  if p.val = (true, vertices_262) then 1 else
  if p.val = (true, vertices_518) then 2 else
  if p.val = (true, vertices_138) then 3 else
  if p.val = (true, vertices_522) then 4 else
  if p.val = (true, vertices_274) then 5 else
  if p.val = (true, vertices_386) then 6 else
  if p.val = (true, vertices_44) then 7 else
  if p.val = (true, vertices_268) then 8 else
  if p.val = (true, vertices_324) then 9 else
  if p.val = (true, vertices_296) then 10 else
  if p.val = (true, vertices_392) then 11 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_14), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_262), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_518), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_138), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_522), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_274), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_386), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_44), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_268), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_324), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_296), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_392), by decide +kernel⟩
  | 12 => Sum.inr ⟨(false, vertices_353), by decide +kernel⟩
  | 13 => Sum.inl 0
  | 14 => Sum.inr ⟨(false, vertices_659), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_86), by decide +kernel⟩
  | 16 => Sum.inl 1
  | 17 => Sum.inr ⟨(false, vertices_613), by decide +kernel⟩
  | 18 => Sum.inl 2
  | 19 => Sum.inr ⟨(false, vertices_681), by decide +kernel⟩
  | 20 => Sum.inl 3
  | 21 => Sum.inr ⟨(false, vertices_433), by decide +kernel⟩
  | 22 => Sum.inr ⟨(false, vertices_849), by decide +kernel⟩
  | 23 => Sum.inl 4
  | 24 => Sum.inl 5
  | 25 => Sum.inl 6
  | 26 => Sum.inl 7
  | 27 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row 0 8 0 1 2 4 558
cert_row 1 6 0 1 2 7 398
cert_row 2 2 1 4 5 7 364
cert_row_3 3 3 1 5 0 86
cert_rows
cert_pivot_2 8 6 2 0
cert_heightProof 4
cert_coverFacet 0 558
cert_cover_3 0 0 0 1 2 4
cert_coverFacet 1 398
cert_cover_3 1 0 1 1 2 6
cert_coverFacet 2 342
cert_cover_3 2 0 3 1 3 7
cert_coverFacet 3 598
cert_cover_3 3 0 3 1 3 8
cert_coverFacet 4 650
cert_cover_4 4 0 2 6 8
cert_coverFacet 5 402
cert_cover_4 5 0 3 6 7
cert_coverFacet 6 364
cert_cover_3 6 1 2 2 4 5
cert_coverFacet 7 424
cert_cover_4 7 2 4 6 7
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_137

end
end BundlePart23

section BundlePart24
/- Source: ProjectionCertificates/P0_138.lean -/





@[expose] public section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_138

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [803, 781, 681, 457, 369, 225, 654, 310, 150, 774, 242, 674, 220, 348, 137, 265, 521, 97, 161, 289, 545, 193, 321, 769, 22, 134, 262, 518, 50, 146, 162, 290, 546, 642, 770, 92, 140, 268, 524, 148, 276, 772, 200, 328, 648, 112, 304, 208, 336, 224, 672]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_803, vertices_781, vertices_681, vertices_457, vertices_369, vertices_225, vertices_654, vertices_310, vertices_150, vertices_774, vertices_242, vertices_674, vertices_220, vertices_348] (by decide +kernel)
  polygons := literalFinset [vertices_137, vertices_265, vertices_521, vertices_97, vertices_161, vertices_289, vertices_545, vertices_193, vertices_321, vertices_769, vertices_22, vertices_134, vertices_262, vertices_518, vertices_50, vertices_146, vertices_162, vertices_290, vertices_546, vertices_642, vertices_770, vertices_92, vertices_140, vertices_268, vertices_524, vertices_148, vertices_276, vertices_772, vertices_200, vertices_328, vertices_648, vertices_112, vertices_304, vertices_208, vertices_336, vertices_224, vertices_672] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_803), (false, vertices_781), (false, vertices_681), (false, vertices_457), (false, vertices_369), (false, vertices_225), (true, vertices_22), (true, vertices_134), (true, vertices_262), (true, vertices_518), (true, vertices_50), (true, vertices_146), (true, vertices_162), (true, vertices_642), (true, vertices_92), (true, vertices_140), (true, vertices_148), (true, vertices_276), (true, vertices_208)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 13 15 18 21 23 24 25 26 27
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_803) then 14 else
  if p.val = (false, vertices_781) then 16 else
  if p.val = (false, vertices_681) then 19 else
  if p.val = (false, vertices_457) then 20 else
  if p.val = (false, vertices_369) then 22 else
  if p.val = (false, vertices_225) then 12 else
  if p.val = (true, vertices_22) then 0 else
  if p.val = (true, vertices_134) then 1 else
  if p.val = (true, vertices_262) then 2 else
  if p.val = (true, vertices_518) then 3 else
  if p.val = (true, vertices_50) then 4 else
  if p.val = (true, vertices_146) then 5 else
  if p.val = (true, vertices_162) then 6 else
  if p.val = (true, vertices_642) then 7 else
  if p.val = (true, vertices_92) then 17 else
  if p.val = (true, vertices_140) then 8 else
  if p.val = (true, vertices_148) then 9 else
  if p.val = (true, vertices_276) then 10 else
  if p.val = (true, vertices_208) then 11 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_22), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_134), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_262), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_518), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_50), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_146), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_162), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_642), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_140), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_148), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_276), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_208), by decide +kernel⟩
  | 12 => Sum.inr ⟨(false, vertices_225), by decide +kernel⟩
  | 13 => Sum.inl 0
  | 14 => Sum.inr ⟨(false, vertices_803), by decide +kernel⟩
  | 15 => Sum.inl 1
  | 16 => Sum.inr ⟨(false, vertices_781), by decide +kernel⟩
  | 17 => Sum.inr ⟨(true, vertices_92), by decide +kernel⟩
  | 18 => Sum.inl 2
  | 19 => Sum.inr ⟨(false, vertices_681), by decide +kernel⟩
  | 20 => Sum.inr ⟨(false, vertices_457), by decide +kernel⟩
  | 21 => Sum.inl 3
  | 22 => Sum.inr ⟨(false, vertices_369), by decide +kernel⟩
  | 23 => Sum.inl 4
  | 24 => Sum.inl 5
  | 25 => Sum.inl 6
  | 26 => Sum.inl 7
  | 27 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row 0 8 0 1 2 6 654
cert_row 1 7 0 1 3 4 310
cert_row 2 0 3 4 5 6 242
cert_row_3 3 3 2 5 1 92
cert_rows
cert_pivot_2 8 7 0 1
cert_heightProof 4
cert_coverFacet 0 654
cert_cover_3 0 0 0 1 2 6
cert_coverFacet 1 310
cert_cover_3 1 0 1 1 3 4
cert_coverFacet 2 150
cert_cover_4 2 0 1 3 6
cert_coverFacet 3 774
cert_cover_4 3 0 1 7 8
cert_coverFacet 4 242
cert_cover_3 4 0 2 3 4 5
cert_coverFacet 5 674
cert_cover_4 5 0 4 6 8
cert_coverFacet 6 220
cert_cover_3 6 1 3 2 3 6
cert_coverFacet 7 348
cert_cover_3 7 1 3 2 3 7
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_138

end
end BundlePart24

section BundlePart25
/- Source: ProjectionCertificates/P0_143.lean -/





@[expose] public section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_143

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [611, 419, 643, 901, 841, 369, 542, 182, 646, 562, 348, 780, 436, 632, 35, 131, 515, 97, 289, 321, 577, 385, 641, 769, 22, 134, 518, 50, 530, 162, 546, 642, 28, 268, 524, 180, 276, 388, 644, 772, 88, 536, 328, 584, 776, 112, 304, 560, 336, 608, 416]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_611, vertices_419, vertices_643, vertices_901, vertices_841, vertices_369, vertices_542, vertices_182, vertices_646, vertices_562, vertices_348, vertices_780, vertices_436, vertices_632] (by decide +kernel)
  polygons := literalFinset [vertices_35, vertices_131, vertices_515, vertices_97, vertices_289, vertices_321, vertices_577, vertices_385, vertices_641, vertices_769, vertices_22, vertices_134, vertices_518, vertices_50, vertices_530, vertices_162, vertices_546, vertices_642, vertices_28, vertices_268, vertices_524, vertices_180, vertices_276, vertices_388, vertices_644, vertices_772, vertices_88, vertices_536, vertices_328, vertices_584, vertices_776, vertices_112, vertices_304, vertices_560, vertices_336, vertices_608, vertices_416] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_611), (false, vertices_419), (false, vertices_643), (false, vertices_901), (false, vertices_841), (false, vertices_369), (true, vertices_22), (true, vertices_134), (true, vertices_518), (true, vertices_50), (true, vertices_530), (true, vertices_28), (true, vertices_268), (true, vertices_524), (true, vertices_180), (true, vertices_276), (true, vertices_88), (true, vertices_536), (true, vertices_560)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 13 16 19 21 23 24 25 26 27
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_611) then 14 else
  if p.val = (false, vertices_419) then 15 else
  if p.val = (false, vertices_643) then 12 else
  if p.val = (false, vertices_901) then 17 else
  if p.val = (false, vertices_841) then 20 else
  if p.val = (false, vertices_369) then 22 else
  if p.val = (true, vertices_22) then 0 else
  if p.val = (true, vertices_134) then 1 else
  if p.val = (true, vertices_518) then 2 else
  if p.val = (true, vertices_50) then 3 else
  if p.val = (true, vertices_530) then 4 else
  if p.val = (true, vertices_28) then 5 else
  if p.val = (true, vertices_268) then 6 else
  if p.val = (true, vertices_524) then 7 else
  if p.val = (true, vertices_180) then 18 else
  if p.val = (true, vertices_276) then 8 else
  if p.val = (true, vertices_88) then 9 else
  if p.val = (true, vertices_536) then 10 else
  if p.val = (true, vertices_560) then 11 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_22), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_134), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_518), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_50), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_530), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_28), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_268), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_524), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_276), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_88), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_536), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_560), by decide +kernel⟩
  | 12 => Sum.inr ⟨(false, vertices_643), by decide +kernel⟩
  | 13 => Sum.inl 0
  | 14 => Sum.inr ⟨(false, vertices_611), by decide +kernel⟩
  | 15 => Sum.inr ⟨(false, vertices_419), by decide +kernel⟩
  | 16 => Sum.inl 1
  | 17 => Sum.inr ⟨(false, vertices_901), by decide +kernel⟩
  | 18 => Sum.inr ⟨(true, vertices_180), by decide +kernel⟩
  | 19 => Sum.inl 2
  | 20 => Sum.inr ⟨(false, vertices_841), by decide +kernel⟩
  | 21 => Sum.inl 3
  | 22 => Sum.inr ⟨(false, vertices_369), by decide +kernel⟩
  | 23 => Sum.inl 4
  | 24 => Sum.inl 5
  | 25 => Sum.inl 6
  | 26 => Sum.inl 7
  | 27 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row 0 0 1 2 3 8 542
cert_row 1 7 1 2 3 5 348
cert_row 2 2 3 4 5 8 632
cert_row_3 3 4 3 6 1 180
cert_rows
cert_pivot_2 0 7 2 1
cert_heightProof 4
cert_coverFacet 0 542
cert_cover_3 0 0 0 1 2 3
cert_coverFacet 1 182
cert_cover_3 1 0 3 1 3 4
cert_coverFacet 2 646
cert_cover_4 2 0 1 6 8
cert_coverFacet 3 562
cert_cover_4 3 0 3 4 8
cert_coverFacet 4 348
cert_cover_3 4 1 1 2 3 5
cert_coverFacet 5 780
cert_cover_4 5 1 2 7 8
cert_coverFacet 6 436
cert_cover_3 6 1 3 3 4 7
cert_coverFacet 7 632
cert_cover_3 7 2 2 3 4 5
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_143

end
end BundlePart25

section BundlePart26
/- Source: ProjectionCertificates/P0_148.lean -/





@[expose] public section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_148

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [707, 405, 197, 837, 793, 689, 230, 570, 362, 842, 674, 356, 420, 440, 69, 133, 261, 145, 273, 529, 193, 577, 641, 769, 42, 330, 522, 98, 162, 546, 194, 578, 642, 100, 164, 292, 196, 324, 388, 56, 280, 536, 296, 776, 176, 560, 400, 352, 416, 672, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_707, vertices_405, vertices_197, vertices_837, vertices_793, vertices_689, vertices_230, vertices_570, vertices_362, vertices_842, vertices_674, vertices_356, vertices_420, vertices_440] (by decide +kernel)
  polygons := literalFinset [vertices_69, vertices_133, vertices_261, vertices_145, vertices_273, vertices_529, vertices_193, vertices_577, vertices_641, vertices_769, vertices_42, vertices_330, vertices_522, vertices_98, vertices_162, vertices_546, vertices_194, vertices_578, vertices_642, vertices_100, vertices_164, vertices_292, vertices_196, vertices_324, vertices_388, vertices_56, vertices_280, vertices_536, vertices_296, vertices_776, vertices_176, vertices_560, vertices_400, vertices_352, vertices_416, vertices_672, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_707), (false, vertices_405), (false, vertices_197), (false, vertices_837), (false, vertices_793), (false, vertices_689), (true, vertices_42), (true, vertices_330), (true, vertices_522), (true, vertices_98), (true, vertices_162), (true, vertices_546), (true, vertices_100), (true, vertices_164), (true, vertices_292), (true, vertices_56), (true, vertices_296), (true, vertices_352), (true, vertices_416)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 13 16 19 21 23 24 25 26 27
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_707) then 14 else
  if p.val = (false, vertices_405) then 17 else
  if p.val = (false, vertices_197) then 12 else
  if p.val = (false, vertices_837) then 18 else
  if p.val = (false, vertices_793) then 20 else
  if p.val = (false, vertices_689) then 22 else
  if p.val = (true, vertices_42) then 0 else
  if p.val = (true, vertices_330) then 15 else
  if p.val = (true, vertices_522) then 1 else
  if p.val = (true, vertices_98) then 2 else
  if p.val = (true, vertices_162) then 3 else
  if p.val = (true, vertices_546) then 4 else
  if p.val = (true, vertices_100) then 5 else
  if p.val = (true, vertices_164) then 6 else
  if p.val = (true, vertices_292) then 7 else
  if p.val = (true, vertices_56) then 8 else
  if p.val = (true, vertices_296) then 9 else
  if p.val = (true, vertices_352) then 10 else
  if p.val = (true, vertices_416) then 11 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_42), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_522), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_98), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_162), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_546), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_100), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_164), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_292), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_56), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_296), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_352), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_416), by decide +kernel⟩
  | 12 => Sum.inr ⟨(false, vertices_197), by decide +kernel⟩
  | 13 => Sum.inl 0
  | 14 => Sum.inr ⟨(false, vertices_707), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_330), by decide +kernel⟩
  | 16 => Sum.inl 1
  | 17 => Sum.inr ⟨(false, vertices_405), by decide +kernel⟩
  | 18 => Sum.inr ⟨(false, vertices_837), by decide +kernel⟩
  | 19 => Sum.inl 2
  | 20 => Sum.inr ⟨(false, vertices_793), by decide +kernel⟩
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
cert_row 0 1 0 4 5 6 230
cert_row 1 8 0 2 3 4 570
cert_row 2 3 2 4 6 7 440
cert_row_3 3 5 2 7 0 330
cert_rows
cert_pivot_2 1 8 3 0
cert_heightProof 4
cert_coverFacet 0 230
cert_cover_3 0 0 0 1 4 5
cert_coverFacet 1 570
cert_cover_3 1 0 1 2 3 4
cert_coverFacet 2 362
cert_cover_3 2 0 3 2 4 5
cert_coverFacet 3 842
cert_cover_3 3 0 3 2 5 8
cert_coverFacet 4 674
cert_cover_4 4 0 4 6 8
cert_coverFacet 5 356
cert_cover_4 5 1 4 5 7
cert_coverFacet 6 420
cert_cover_4 6 1 4 6 7
cert_coverFacet 7 440
cert_cover_3 7 2 2 3 4 6
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_148

end
end BundlePart26

section BundlePart27
/- Source: ProjectionCertificates/P0_150.lean -/





@[expose] public section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_150

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [835, 653, 793, 457, 737, 286, 54, 230, 454, 818, 610, 540, 396, 692, 137, 265, 521, 193, 321, 577, 641, 769, 22, 38, 198, 262, 50, 274, 98, 546, 322, 578, 770, 28, 140, 268, 524, 52, 532, 164, 388, 644, 280, 536, 392, 560, 784, 224, 608, 672, 448]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_835, vertices_653, vertices_793, vertices_457, vertices_737, vertices_286, vertices_54, vertices_230, vertices_454, vertices_818, vertices_610, vertices_540, vertices_396, vertices_692] (by decide +kernel)
  polygons := literalFinset [vertices_137, vertices_265, vertices_521, vertices_193, vertices_321, vertices_577, vertices_641, vertices_769, vertices_22, vertices_38, vertices_198, vertices_262, vertices_50, vertices_274, vertices_98, vertices_546, vertices_322, vertices_578, vertices_770, vertices_28, vertices_140, vertices_268, vertices_524, vertices_52, vertices_532, vertices_164, vertices_388, vertices_644, vertices_280, vertices_536, vertices_392, vertices_560, vertices_784, vertices_224, vertices_608, vertices_672, vertices_448] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_835), (false, vertices_653), (false, vertices_793), (false, vertices_457), (false, vertices_737), (true, vertices_22), (true, vertices_38), (true, vertices_198), (true, vertices_262), (true, vertices_50), (true, vertices_274), (true, vertices_98), (true, vertices_546), (true, vertices_28), (true, vertices_268), (true, vertices_52), (true, vertices_532), (true, vertices_164), (true, vertices_388), (true, vertices_560)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 14 17 19 22 23 25 26 27 28
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_835) then 15 else
  if p.val = (false, vertices_653) then 18 else
  if p.val = (false, vertices_793) then 20 else
  if p.val = (false, vertices_457) then 21 else
  if p.val = (false, vertices_737) then 24 else
  if p.val = (true, vertices_22) then 0 else
  if p.val = (true, vertices_38) then 1 else
  if p.val = (true, vertices_198) then 16 else
  if p.val = (true, vertices_262) then 2 else
  if p.val = (true, vertices_50) then 3 else
  if p.val = (true, vertices_274) then 4 else
  if p.val = (true, vertices_98) then 5 else
  if p.val = (true, vertices_546) then 6 else
  if p.val = (true, vertices_28) then 7 else
  if p.val = (true, vertices_268) then 8 else
  if p.val = (true, vertices_52) then 9 else
  if p.val = (true, vertices_532) then 10 else
  if p.val = (true, vertices_164) then 11 else
  if p.val = (true, vertices_388) then 12 else
  if p.val = (true, vertices_560) then 13 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_22), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_38), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_262), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_50), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_274), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_98), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_546), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_28), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_268), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_52), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_532), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_164), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_388), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_560), by decide +kernel⟩
  | 14 => Sum.inl 0
  | 15 => Sum.inr ⟨(false, vertices_835), by decide +kernel⟩
  | 16 => Sum.inr ⟨(true, vertices_198), by decide +kernel⟩
  | 17 => Sum.inl 1
  | 18 => Sum.inr ⟨(false, vertices_653), by decide +kernel⟩
  | 19 => Sum.inl 2
  | 20 => Sum.inr ⟨(false, vertices_793), by decide +kernel⟩
  | 21 => Sum.inr ⟨(false, vertices_457), by decide +kernel⟩
  | 22 => Sum.inl 3
  | 23 => Sum.inl 4
  | 24 => Sum.inr ⟨(false, vertices_737), by decide +kernel⟩
  | 25 => Sum.inl 5
  | 26 => Sum.inl 6
  | 27 => Sum.inl 7
  | 28 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row 0 2 0 1 3 7 286
cert_row 1 7 0 3 4 8 818
cert_row 2 3 1 4 6 8 692
cert_row_3 3 5 1 6 0 198
cert_rows
cert_pivot_2 2 7 3 0
cert_heightProof 4
cert_coverFacet 0 286
cert_cover_3 0 0 0 1 2 3
cert_coverFacet 1 54
cert_cover_4 1 0 1 3 4
cert_coverFacet 2 230
cert_cover_3 2 0 3 1 4 5
cert_coverFacet 3 454
cert_cover_3 3 0 3 1 5 7
cert_coverFacet 4 818
cert_cover_3 4 0 1 3 4 7
cert_coverFacet 5 610
cert_cover_4 5 0 4 5 8
cert_coverFacet 6 540
cert_cover_4 6 1 2 3 8
cert_coverFacet 7 396
cert_cover_4 7 1 2 6 7
cert_coverFacet 8 692
cert_cover_3 8 1 2 3 4 6
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_150

end
end BundlePart27

section BundlePart28
/- Source: ProjectionCertificates/P0_160.lean -/





@[expose] public section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_160

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [835, 597, 665, 809, 457, 209, 214, 166, 806, 582, 426, 450, 188, 572, 137, 265, 521, 81, 145, 529, 193, 321, 577, 769, 38, 70, 134, 518, 162, 290, 194, 322, 578, 386, 770, 60, 84, 148, 532, 164, 548, 580, 152, 536, 168, 296, 552, 392, 208, 800, 448]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_835, vertices_597, vertices_665, vertices_809, vertices_457, vertices_209, vertices_214, vertices_166, vertices_806, vertices_582, vertices_426, vertices_450, vertices_188, vertices_572] (by decide +kernel)
  polygons := literalFinset [vertices_137, vertices_265, vertices_521, vertices_81, vertices_145, vertices_529, vertices_193, vertices_321, vertices_577, vertices_769, vertices_38, vertices_70, vertices_134, vertices_518, vertices_162, vertices_290, vertices_194, vertices_322, vertices_578, vertices_386, vertices_770, vertices_60, vertices_84, vertices_148, vertices_532, vertices_164, vertices_548, vertices_580, vertices_152, vertices_536, vertices_168, vertices_296, vertices_552, vertices_392, vertices_208, vertices_800, vertices_448] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_835), (false, vertices_597), (false, vertices_665), (false, vertices_809), (false, vertices_457), (false, vertices_209), (true, vertices_38), (true, vertices_70), (true, vertices_134), (true, vertices_518), (true, vertices_162), (true, vertices_290), (true, vertices_194), (true, vertices_386), (true, vertices_60), (true, vertices_148), (true, vertices_164), (true, vertices_548), (true, vertices_168)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 13 15 18 22 23 24 25 26 27
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_835) then 14 else
  if p.val = (false, vertices_597) then 16 else
  if p.val = (false, vertices_665) then 19 else
  if p.val = (false, vertices_809) then 20 else
  if p.val = (false, vertices_457) then 21 else
  if p.val = (false, vertices_209) then 12 else
  if p.val = (true, vertices_38) then 0 else
  if p.val = (true, vertices_70) then 1 else
  if p.val = (true, vertices_134) then 2 else
  if p.val = (true, vertices_518) then 3 else
  if p.val = (true, vertices_162) then 4 else
  if p.val = (true, vertices_290) then 5 else
  if p.val = (true, vertices_194) then 6 else
  if p.val = (true, vertices_386) then 7 else
  if p.val = (true, vertices_60) then 17 else
  if p.val = (true, vertices_148) then 8 else
  if p.val = (true, vertices_164) then 9 else
  if p.val = (true, vertices_548) then 10 else
  if p.val = (true, vertices_168) then 11 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_38), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_70), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_134), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_518), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_162), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_290), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_194), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_386), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_148), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_164), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_548), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_168), by decide +kernel⟩
  | 12 => Sum.inr ⟨(false, vertices_209), by decide +kernel⟩
  | 13 => Sum.inl 0
  | 14 => Sum.inr ⟨(false, vertices_835), by decide +kernel⟩
  | 15 => Sum.inl 1
  | 16 => Sum.inr ⟨(false, vertices_597), by decide +kernel⟩
  | 17 => Sum.inr ⟨(true, vertices_60), by decide +kernel⟩
  | 18 => Sum.inl 2
  | 19 => Sum.inr ⟨(false, vertices_665), by decide +kernel⟩
  | 20 => Sum.inr ⟨(false, vertices_809), by decide +kernel⟩
  | 21 => Sum.inr ⟨(false, vertices_457), by decide +kernel⟩
  | 22 => Sum.inl 3
  | 23 => Sum.inl 4
  | 24 => Sum.inl 5
  | 25 => Sum.inl 6
  | 26 => Sum.inl 7
  | 27 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row 0 5 0 1 3 6 214
cert_row 1 8 0 1 4 7 806
cert_row 2 0 2 4 6 7 426
cert_row_3 3 3 2 4 1 60
cert_rows
cert_pivot_2 5 8 0 1
cert_heightProof 4
cert_coverFacet 0 214
cert_cover_3 0 0 0 1 3 5
cert_coverFacet 1 166
cert_cover_4 1 0 1 4 6
cert_coverFacet 2 806
cert_cover_3 2 0 1 1 4 7
cert_coverFacet 3 582
cert_cover_4 3 0 1 5 8
cert_coverFacet 4 426
cert_cover_3 4 0 2 2 4 6
cert_coverFacet 5 450
cert_cover_4 5 0 5 6 7
cert_coverFacet 6 188
cert_cover_3 6 1 3 2 3 6
cert_coverFacet 7 572
cert_cover_3 7 1 3 2 3 8
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_160

end
end BundlePart28

section BundlePart29
/- Source: ProjectionCertificates/P0_161.lean -/





@[expose] public section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_161

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [899, 837, 601, 153, 457, 689, 110, 334, 806, 186, 394, 674, 628, 120, 25, 73, 137, 145, 529, 321, 577, 385, 641, 769, 78, 38, 262, 42, 138, 266, 162, 546, 386, 642, 770, 100, 548, 324, 580, 772, 56, 88, 152, 104, 328, 392, 112, 176, 560, 592, 672]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_899, vertices_837, vertices_601, vertices_153, vertices_457, vertices_689, vertices_110, vertices_334, vertices_806, vertices_186, vertices_394, vertices_674, vertices_628, vertices_120] (by decide +kernel)
  polygons := literalFinset [vertices_25, vertices_73, vertices_137, vertices_145, vertices_529, vertices_321, vertices_577, vertices_385, vertices_641, vertices_769, vertices_78, vertices_38, vertices_262, vertices_42, vertices_138, vertices_266, vertices_162, vertices_546, vertices_386, vertices_642, vertices_770, vertices_100, vertices_548, vertices_324, vertices_580, vertices_772, vertices_56, vertices_88, vertices_152, vertices_104, vertices_328, vertices_392, vertices_112, vertices_176, vertices_560, vertices_592, vertices_672] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_899), (false, vertices_837), (false, vertices_601), (false, vertices_153), (false, vertices_457), (false, vertices_689), (true, vertices_78), (true, vertices_38), (true, vertices_262), (true, vertices_42), (true, vertices_138), (true, vertices_266), (true, vertices_162), (true, vertices_546), (true, vertices_100), (true, vertices_548), (true, vertices_56), (true, vertices_104), (true, vertices_112)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 13 16 18 21 23 24 25 26 27
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_899) then 14 else
  if p.val = (false, vertices_837) then 17 else
  if p.val = (false, vertices_601) then 19 else
  if p.val = (false, vertices_153) then 12 else
  if p.val = (false, vertices_457) then 20 else
  if p.val = (false, vertices_689) then 22 else
  if p.val = (true, vertices_78) then 15 else
  if p.val = (true, vertices_38) then 0 else
  if p.val = (true, vertices_262) then 1 else
  if p.val = (true, vertices_42) then 2 else
  if p.val = (true, vertices_138) then 3 else
  if p.val = (true, vertices_266) then 4 else
  if p.val = (true, vertices_162) then 5 else
  if p.val = (true, vertices_546) then 6 else
  if p.val = (true, vertices_100) then 7 else
  if p.val = (true, vertices_548) then 8 else
  if p.val = (true, vertices_56) then 9 else
  if p.val = (true, vertices_104) then 10 else
  if p.val = (true, vertices_112) then 11 else
  0
cert_priority
cert_nodeAtPriority_56 38 262 42 138 266 162 546 100 548 56 104 112 153 899 78 837 601 457 689
cert_priority_injective
cert_incidenceProof
cert_row 0 7 0 1 4 8 806
cert_row 1 6 0 2 3 4 186
cert_row 2 3 1 4 5 8 628
cert_row_3 3 2 1 5 0 78
cert_rows
cert_pivot_2 7 6 3 0
cert_heightProof 4
cert_coverFacet 0 110
cert_cover_3 0 0 3 1 2 4
cert_coverFacet 1 334
cert_cover_3 1 0 3 1 2 7
cert_coverFacet 2 806
cert_cover_3 2 0 0 1 4 7
cert_coverFacet 3 186
cert_cover_3 3 0 1 2 3 4
cert_coverFacet 4 394
cert_cover_4 4 0 2 6 7
cert_coverFacet 5 674
cert_cover_4 5 0 4 6 8
cert_coverFacet 6 628
cert_cover_3 6 1 2 3 4 5
cert_coverFacet 7 120
cert_cover_4 7 2 3 4 5
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_161

end
end BundlePart29
