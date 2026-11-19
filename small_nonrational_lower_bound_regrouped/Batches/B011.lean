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
/- Source: ProjectionCertificates/R_m14e10q1_0569.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0569

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [779, 355, 675, 653, 457, 241, 662, 178, 306, 786, 796, 460, 372, 212, 35, 259, 515, 137, 265, 521, 97, 161, 193, 321, 641, 50, 146, 274, 530, 162, 290, 642, 770, 140, 268, 524, 84, 148, 276, 532, 196, 324, 644, 456, 776, 112, 176, 304, 208, 784, 352]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_779, vertices_355, vertices_675, vertices_653, vertices_457, vertices_241, vertices_662, vertices_178, vertices_306, vertices_786, vertices_796, vertices_460, vertices_372, vertices_212] (by decide +kernel)
  polygons := literalFinset [vertices_35, vertices_259, vertices_515, vertices_137, vertices_265, vertices_521, vertices_97, vertices_161, vertices_193, vertices_321, vertices_641, vertices_50, vertices_146, vertices_274, vertices_530, vertices_162, vertices_290, vertices_642, vertices_770, vertices_140, vertices_268, vertices_524, vertices_84, vertices_148, vertices_276, vertices_532, vertices_196, vertices_324, vertices_644, vertices_456, vertices_776, vertices_112, vertices_176, vertices_304, vertices_208, vertices_784, vertices_352] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_779), (false, vertices_355), (false, vertices_675), (false, vertices_653), (false, vertices_457), (false, vertices_241), (true, vertices_50), (true, vertices_146), (true, vertices_274), (true, vertices_530), (true, vertices_268), (true, vertices_84), (true, vertices_148), (true, vertices_276), (true, vertices_532), (true, vertices_196), (true, vertices_324), (true, vertices_304), (true, vertices_784)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 13 17 19 21 23 24 25 26 27
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_779) then 14 else
  if p.val = (false, vertices_355) then 15 else
  if p.val = (false, vertices_675) then 16 else
  if p.val = (false, vertices_653) then 18 else
  if p.val = (false, vertices_457) then 20 else
  if p.val = (false, vertices_241) then 22 else
  if p.val = (true, vertices_50) then 0 else
  if p.val = (true, vertices_146) then 1 else
  if p.val = (true, vertices_274) then 2 else
  if p.val = (true, vertices_530) then 3 else
  if p.val = (true, vertices_268) then 4 else
  if p.val = (true, vertices_84) then 5 else
  if p.val = (true, vertices_148) then 6 else
  if p.val = (true, vertices_276) then 7 else
  if p.val = (true, vertices_532) then 8 else
  if p.val = (true, vertices_196) then 9 else
  if p.val = (true, vertices_324) then 10 else
  if p.val = (true, vertices_304) then 11 else
  if p.val = (true, vertices_784) then 12 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_50), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_146), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_274), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_530), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_268), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_84), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_148), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_276), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_532), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_196), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_324), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_304), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_784), by decide +kernel⟩
  | 13 => Sum.inl 0
  | 14 => Sum.inr ⟨(false, vertices_779), by decide +kernel⟩
  | 15 => Sum.inr ⟨(false, vertices_355), by decide +kernel⟩
  | 16 => Sum.inr ⟨(false, vertices_675), by decide +kernel⟩
  | 17 => Sum.inl 1
  | 18 => Sum.inr ⟨(false, vertices_653), by decide +kernel⟩
  | 19 => Sum.inl 2
  | 20 => Sum.inr ⟨(false, vertices_457), by decide +kernel⟩
  | 21 => Sum.inl 3
  | 22 => Sum.inr ⟨(false, vertices_241), by decide +kernel⟩
  | 23 => Sum.inl 4
  | 24 => Sum.inl 5
  | 25 => Sum.inl 6
  | 26 => Sum.inl 7
  | 27 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 3 6 8 662 146 1
cert_row_2 1 2 5 6 7 456
cert_row_4 2 1 2 3 7 8 796 268 2
cert_row_4 3 1 3 4 5 7 372 84 2
cert_rows
cert_pivot_2 0 6 2 1
cert_heightProof 4
cert_coverFacet 0 662
cert_cover_5 0 0 0 1 3 6 146 662 1
cert_coverFacet 1 178
cert_cover_2 1 3 0 4 6 50 178 3
cert_coverFacet 2 306
cert_cover_2 2 3 0 4 7 50 306 3
cert_coverFacet 3 786
cert_cover_2 3 3 0 7 8 274 786 3
cert_coverFacet 4 796
cert_cover_5 4 2 1 2 3 7 268 796 2
cert_coverFacet 5 460
cert_cover_5 5 1 1 2 5 6 140 460 2
cert_coverFacet 6 372
cert_cover_5 6 3 1 3 4 5 84 372 2
cert_coverFacet 7 212
cert_cover_2 7 3 1 5 6 84 212 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0569

end
end BundlePart0

section BundlePart1
/- Source: ProjectionCertificates/R_m14e10q1_0570.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0570

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [391, 653, 341, 597, 617, 457, 310, 534, 646, 682, 626, 418, 232, 496, 85, 133, 261, 517, 73, 137, 521, 321, 577, 385, 22, 134, 262, 518, 50, 530, 162, 290, 546, 386, 642, 276, 532, 644, 104, 168, 552, 200, 648, 112, 304, 336, 592, 224, 608, 416, 448]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_391, vertices_653, vertices_341, vertices_597, vertices_617, vertices_457, vertices_310, vertices_534, vertices_646, vertices_682, vertices_626, vertices_418, vertices_232, vertices_496] (by decide +kernel)
  polygons := literalFinset [vertices_85, vertices_133, vertices_261, vertices_517, vertices_73, vertices_137, vertices_521, vertices_321, vertices_577, vertices_385, vertices_22, vertices_134, vertices_262, vertices_518, vertices_50, vertices_530, vertices_162, vertices_290, vertices_546, vertices_386, vertices_642, vertices_276, vertices_532, vertices_644, vertices_104, vertices_168, vertices_552, vertices_200, vertices_648, vertices_112, vertices_304, vertices_336, vertices_592, vertices_224, vertices_608, vertices_416, vertices_448] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_391), (false, vertices_653), (false, vertices_341), (false, vertices_597), (false, vertices_617), (false, vertices_457), (true, vertices_22), (true, vertices_518), (true, vertices_50), (true, vertices_530), (true, vertices_162), (true, vertices_290), (true, vertices_546), (true, vertices_642), (true, vertices_168), (true, vertices_112), (true, vertices_304), (true, vertices_224), (true, vertices_416)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 13 15 19 22 23 24 25 26 27
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_391) then 14 else
  if p.val = (false, vertices_653) then 16 else
  if p.val = (false, vertices_341) then 17 else
  if p.val = (false, vertices_597) then 18 else
  if p.val = (false, vertices_617) then 20 else
  if p.val = (false, vertices_457) then 21 else
  if p.val = (true, vertices_22) then 0 else
  if p.val = (true, vertices_518) then 1 else
  if p.val = (true, vertices_50) then 2 else
  if p.val = (true, vertices_530) then 3 else
  if p.val = (true, vertices_162) then 4 else
  if p.val = (true, vertices_290) then 5 else
  if p.val = (true, vertices_546) then 6 else
  if p.val = (true, vertices_642) then 7 else
  if p.val = (true, vertices_168) then 8 else
  if p.val = (true, vertices_112) then 9 else
  if p.val = (true, vertices_304) then 10 else
  if p.val = (true, vertices_224) then 11 else
  if p.val = (true, vertices_416) then 12 else
  0
cert_priority
cert_nodeAtPriority 0 22 1 518 2 50 530 162 290 546 642 168 112 304 224 416 391 653 341 597 617 457
cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 3 4 7 310 22 3
cert_row_4 1 0 2 4 6 8 682 162 1
cert_row_4 2 0 3 4 5 8 626 50 3
cert_row_4 3 3 4 5 6 7 496 112 3
cert_rows
cert_pivot_2 1 2 0 3
cert_heightProof 4
cert_coverFacet 0 310
cert_cover_5 0 0 0 1 3 4 22 310 3
cert_coverFacet 1 534
cert_cover_2 1 1 0 3 8 22 534 3
cert_coverFacet 2 646
cert_cover_2 2 1 0 6 8 134 646 3
cert_coverFacet 3 682
cert_cover_5 3 1 0 2 4 6 162 682 1
cert_coverFacet 4 626
cert_cover_5 4 2 0 3 4 5 50 626 3
cert_coverFacet 5 418
cert_cover_2 5 4 0 6 7 162 418 3
cert_coverFacet 6 232
cert_cover_2 6 4 2 5 6 104 232 3
cert_coverFacet 7 496
cert_cover_5 7 3 3 4 5 6 112 496 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0570

end
end BundlePart1

section BundlePart2
/- Source: ProjectionCertificates/R_m14e10q1_0571.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0571

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [535, 199, 147, 357, 805, 233, 689, 390, 774, 410, 818, 460, 376, 184, 7, 19, 131, 293, 69, 517, 145, 529, 97, 161, 545, 193, 134, 262, 518, 146, 274, 530, 386, 770, 196, 324, 388, 772, 56, 152, 280, 104, 168, 200, 328, 392, 176, 304, 560, 352, 800]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_535, vertices_199, vertices_147, vertices_357, vertices_805, vertices_233, vertices_689, vertices_390, vertices_774, vertices_410, vertices_818, vertices_460, vertices_376, vertices_184] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_19, vertices_131, vertices_293, vertices_69, vertices_517, vertices_145, vertices_529, vertices_97, vertices_161, vertices_545, vertices_193, vertices_134, vertices_262, vertices_518, vertices_146, vertices_274, vertices_530, vertices_386, vertices_770, vertices_196, vertices_324, vertices_388, vertices_772, vertices_56, vertices_152, vertices_280, vertices_104, vertices_168, vertices_200, vertices_328, vertices_392, vertices_176, vertices_304, vertices_560, vertices_352, vertices_800] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_535), (false, vertices_199), (false, vertices_147), (false, vertices_357), (false, vertices_805), (false, vertices_233), (false, vertices_689), (true, vertices_262), (true, vertices_274), (true, vertices_386), (true, vertices_770), (true, vertices_388), (true, vertices_56), (true, vertices_152), (true, vertices_280), (true, vertices_328), (true, vertices_392), (true, vertices_304)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 12 15 18 20 22 23 24 25 26
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_535) then 13 else
  if p.val = (false, vertices_199) then 14 else
  if p.val = (false, vertices_147) then 0 else
  if p.val = (false, vertices_357) then 16 else
  if p.val = (false, vertices_805) then 17 else
  if p.val = (false, vertices_233) then 19 else
  if p.val = (false, vertices_689) then 21 else
  if p.val = (true, vertices_262) then 1 else
  if p.val = (true, vertices_274) then 2 else
  if p.val = (true, vertices_386) then 3 else
  if p.val = (true, vertices_770) then 4 else
  if p.val = (true, vertices_388) then 5 else
  if p.val = (true, vertices_56) then 6 else
  if p.val = (true, vertices_152) then 7 else
  if p.val = (true, vertices_280) then 8 else
  if p.val = (true, vertices_328) then 9 else
  if p.val = (true, vertices_392) then 10 else
  if p.val = (true, vertices_304) then 11 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_147), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_262), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_274), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_386), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_770), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_388), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_56), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_152), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_280), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_328), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_392), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_304), by decide +kernel⟩
  | 12 => Sum.inl 0
  | 13 => Sum.inr ⟨(false, vertices_535), by decide +kernel⟩
  | 14 => Sum.inr ⟨(false, vertices_199), by decide +kernel⟩
  | 15 => Sum.inl 1
  | 16 => Sum.inr ⟨(false, vertices_357), by decide +kernel⟩
  | 17 => Sum.inr ⟨(false, vertices_805), by decide +kernel⟩
  | 18 => Sum.inl 2
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
cert_row_4 0 0 3 4 7 8 818 274 2
cert_row_4 1 0 2 3 6 7 410 146 1
cert_row_4 2 1 2 5 6 7 460 196 1
cert_row_4 3 2 3 4 5 7 376 56 3
cert_rows
cert_pivot_2 8 0 1 2
cert_heightProof 4
cert_coverFacet 0 390
cert_cover_2 0 1 0 6 7 134 390 3
cert_coverFacet 1 774
cert_cover_2 1 1 0 7 8 262 774 3
cert_coverFacet 2 410
cert_cover_5 2 1 0 2 3 6 146 410 1
cert_coverFacet 3 818
cert_cover_5 3 0 0 3 4 7 274 818 2
cert_coverFacet 4 460
cert_cover_5 4 2 1 2 5 6 196 460 1
cert_coverFacet 5 376
cert_cover_5 5 3 2 3 4 5 56 376 3
cert_coverFacet 6 184
cert_cover_2 6 3 2 4 6 56 184 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0571

end
end BundlePart2

section BundlePart3
/- Source: ProjectionCertificates/R_m14e10q1_0572.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0572

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [203, 397, 789, 709, 361, 865, 406, 122, 298, 394, 818, 210, 660, 752, 133, 261, 517, 73, 137, 265, 353, 193, 577, 769, 42, 74, 138, 266, 50, 82, 146, 274, 290, 194, 386, 148, 276, 532, 388, 644, 104, 296, 392, 112, 560, 208, 656, 784, 608, 800, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_203, vertices_397, vertices_789, vertices_709, vertices_361, vertices_865, vertices_406, vertices_122, vertices_298, vertices_394, vertices_818, vertices_210, vertices_660, vertices_752] (by decide +kernel)
  polygons := literalFinset [vertices_133, vertices_261, vertices_517, vertices_73, vertices_137, vertices_265, vertices_353, vertices_193, vertices_577, vertices_769, vertices_42, vertices_74, vertices_138, vertices_266, vertices_50, vertices_82, vertices_146, vertices_274, vertices_290, vertices_194, vertices_386, vertices_148, vertices_276, vertices_532, vertices_388, vertices_644, vertices_104, vertices_296, vertices_392, vertices_112, vertices_560, vertices_208, vertices_656, vertices_784, vertices_608, vertices_800, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_203), (false, vertices_397), (false, vertices_789), (false, vertices_709), (false, vertices_361), (false, vertices_865), (true, vertices_42), (true, vertices_266), (true, vertices_50), (true, vertices_82), (true, vertices_146), (true, vertices_274), (true, vertices_290), (true, vertices_386), (true, vertices_148), (true, vertices_112), (true, vertices_560), (true, vertices_208), (true, vertices_656)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 13 15 19 20 21 24 25 26 27
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_203) then 14 else
  if p.val = (false, vertices_397) then 16 else
  if p.val = (false, vertices_789) then 17 else
  if p.val = (false, vertices_709) then 18 else
  if p.val = (false, vertices_361) then 22 else
  if p.val = (false, vertices_865) then 23 else
  if p.val = (true, vertices_42) then 0 else
  if p.val = (true, vertices_266) then 1 else
  if p.val = (true, vertices_50) then 2 else
  if p.val = (true, vertices_82) then 3 else
  if p.val = (true, vertices_146) then 4 else
  if p.val = (true, vertices_274) then 5 else
  if p.val = (true, vertices_290) then 6 else
  if p.val = (true, vertices_386) then 7 else
  if p.val = (true, vertices_148) then 8 else
  if p.val = (true, vertices_112) then 9 else
  if p.val = (true, vertices_560) then 10 else
  if p.val = (true, vertices_208) then 11 else
  if p.val = (true, vertices_656) then 12 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_42), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_266), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_50), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_82), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_146), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_274), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_290), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_386), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_148), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_112), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_560), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_208), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_656), by decide +kernel⟩
  | 13 => Sum.inl 0
  | 14 => Sum.inr ⟨(false, vertices_203), by decide +kernel⟩
  | 15 => Sum.inl 1
  | 16 => Sum.inr ⟨(false, vertices_397), by decide +kernel⟩
  | 17 => Sum.inr ⟨(false, vertices_789), by decide +kernel⟩
  | 18 => Sum.inr ⟨(false, vertices_709), by decide +kernel⟩
  | 19 => Sum.inl 2
  | 20 => Sum.inl 3
  | 21 => Sum.inl 4
  | 22 => Sum.inr ⟨(false, vertices_361), by decide +kernel⟩
  | 23 => Sum.inr ⟨(false, vertices_865), by decide +kernel⟩
  | 24 => Sum.inl 5
  | 25 => Sum.inl 6
  | 26 => Sum.inl 7
  | 27 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 3 6 7 406 146 1
cert_row_4 1 0 2 3 4 5 122 42 2
cert_row_4 2 0 3 4 7 8 818 50 3
cert_row_4 3 3 4 5 6 8 752 112 3
cert_rows
cert_pivot_2 1 2 0 3
cert_heightProof 4
cert_coverFacet 0 406
cert_cover_5 0 0 0 1 3 6 146 406 1
cert_coverFacet 1 122
cert_cover_5 1 1 0 2 3 4 42 122 2
cert_coverFacet 2 298
cert_cover_2 2 2 0 4 7 42 298 3
cert_coverFacet 3 394
cert_cover_2 3 2 0 6 7 138 394 3
cert_coverFacet 4 818
cert_cover_5 4 2 0 3 4 7 50 818 3
cert_coverFacet 5 210
cert_cover_2 5 3 0 5 6 82 210 3
cert_coverFacet 6 660
cert_cover_2 6 3 1 6 8 148 660 3
cert_coverFacet 7 752
cert_cover_5 7 3 3 4 5 6 112 752 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0572

end
end BundlePart3

section BundlePart4
/- Source: ProjectionCertificates/R_m14e10q1_0580.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0580

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [551, 227, 835, 789, 421, 457, 682, 714, 316, 604, 556, 344, 424, 848, 35, 67, 515, 37, 261, 517, 161, 193, 321, 385, 769, 650, 162, 546, 194, 578, 28, 44, 524, 276, 532, 292, 548, 88, 280, 168, 296, 552, 200, 328, 584, 392, 336, 592, 784, 416, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_551, vertices_227, vertices_835, vertices_789, vertices_421, vertices_457, vertices_682, vertices_714, vertices_316, vertices_604, vertices_556, vertices_344, vertices_424, vertices_848] (by decide +kernel)
  polygons := literalFinset [vertices_35, vertices_67, vertices_515, vertices_37, vertices_261, vertices_517, vertices_161, vertices_193, vertices_321, vertices_385, vertices_769, vertices_650, vertices_162, vertices_546, vertices_194, vertices_578, vertices_28, vertices_44, vertices_524, vertices_276, vertices_532, vertices_292, vertices_548, vertices_88, vertices_280, vertices_168, vertices_296, vertices_552, vertices_200, vertices_328, vertices_584, vertices_392, vertices_336, vertices_592, vertices_784, vertices_416, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_551), (false, vertices_227), (false, vertices_835), (false, vertices_789), (false, vertices_421), (false, vertices_457), (true, vertices_650), (true, vertices_28), (true, vertices_44), (true, vertices_524), (true, vertices_88), (true, vertices_280), (true, vertices_168), (true, vertices_296), (true, vertices_552), (true, vertices_584), (true, vertices_336), (true, vertices_592)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 11 19 21 22 23 24 25 26
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_551) then 12 else
  if p.val = (false, vertices_227) then 16 else
  if p.val = (false, vertices_835) then 17 else
  if p.val = (false, vertices_789) then 13 else
  if p.val = (false, vertices_421) then 14 else
  if p.val = (false, vertices_457) then 20 else
  if p.val = (true, vertices_650) then 18 else
  if p.val = (true, vertices_28) then 0 else
  if p.val = (true, vertices_44) then 1 else
  if p.val = (true, vertices_524) then 2 else
  if p.val = (true, vertices_88) then 3 else
  if p.val = (true, vertices_280) then 4 else
  if p.val = (true, vertices_168) then 5 else
  if p.val = (true, vertices_296) then 6 else
  if p.val = (true, vertices_552) then 7 else
  if p.val = (true, vertices_584) then 8 else
  if p.val = (true, vertices_336) then 9 else
  if p.val = (true, vertices_592) then 10 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_28), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_44), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_524), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_88), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_280), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_168), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_296), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_552), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_584), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_336), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_592), by decide +kernel⟩
  | 11 => Sum.inl 1
  | 12 => Sum.inr ⟨(false, vertices_551), by decide +kernel⟩
  | 13 => Sum.inr ⟨(false, vertices_789), by decide +kernel⟩
  | 14 => Sum.inr ⟨(false, vertices_421), by decide +kernel⟩
  | 15 => Sum.inl 0
  | 16 => Sum.inr ⟨(false, vertices_227), by decide +kernel⟩
  | 17 => Sum.inr ⟨(false, vertices_835), by decide +kernel⟩
  | 18 => Sum.inr ⟨(true, vertices_650), by decide +kernel⟩
  | 19 => Sum.inl 2
  | 20 => Sum.inr ⟨(false, vertices_457), by decide +kernel⟩
  | 21 => Sum.inl 3
  | 22 => Sum.inl 4
  | 23 => Sum.inl 5
  | 24 => Sum.inl 6
  | 25 => Sum.inl 7
  | 26 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 2 6 8 650
cert_row_4 1 1 2 3 4 7 316 28 3
cert_row_4 2 1 2 3 5 8 604 28 3
cert_rows_3
cert_pivot_3 4 0 1
cert_heightProof 3
cert_coverFacet 0 682
cert_cover_5 0 0 0 2 4 6 650 682 2
cert_coverFacet 1 714
cert_cover_5 1 0 0 2 5 6 650 714 2
cert_coverFacet 2 316
cert_cover_5 2 1 1 2 3 4 28 316 3
cert_coverFacet 3 604
cert_cover_5 3 2 1 2 3 5 28 604 3
cert_coverFacet 4 556
cert_cover_2 4 2 1 4 8 44 556 3
cert_coverFacet 5 344
cert_cover_2 5 3 2 5 7 88 344 3
cert_coverFacet 6 424
cert_cover_2 6 4 2 6 7 168 424 3
cert_coverFacet 7 848
cert_cover_2 7 5 3 7 8 336 848 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 3 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0580

end
end BundlePart4

section BundlePart5
/- Source: ProjectionCertificates/R_m14e10q1_0586.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0586

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [651, 837, 617, 425, 369, 897, 542, 342, 774, 186, 434, 898, 628, 568, 41, 137, 521, 97, 289, 321, 577, 385, 641, 769, 22, 262, 518, 26, 138, 522, 178, 274, 386, 642, 770, 84, 532, 324, 580, 772, 56, 536, 168, 552, 112, 304, 560, 336, 608, 416, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_651, vertices_837, vertices_617, vertices_425, vertices_369, vertices_897, vertices_542, vertices_342, vertices_774, vertices_186, vertices_434, vertices_898, vertices_628, vertices_568] (by decide +kernel)
  polygons := literalFinset [vertices_41, vertices_137, vertices_521, vertices_97, vertices_289, vertices_321, vertices_577, vertices_385, vertices_641, vertices_769, vertices_22, vertices_262, vertices_518, vertices_26, vertices_138, vertices_522, vertices_178, vertices_274, vertices_386, vertices_642, vertices_770, vertices_84, vertices_532, vertices_324, vertices_580, vertices_772, vertices_56, vertices_536, vertices_168, vertices_552, vertices_112, vertices_304, vertices_560, vertices_336, vertices_608, vertices_416, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_651), (false, vertices_837), (false, vertices_617), (false, vertices_425), (false, vertices_369), (false, vertices_897), (true, vertices_22), (true, vertices_262), (true, vertices_518), (true, vertices_26), (true, vertices_178), (true, vertices_274), (true, vertices_386), (true, vertices_770), (true, vertices_84), (true, vertices_532), (true, vertices_56), (true, vertices_536), (true, vertices_560)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 13 16 18 21 23 24 25 26 27
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_651) then 14 else
  if p.val = (false, vertices_837) then 17 else
  if p.val = (false, vertices_617) then 19 else
  if p.val = (false, vertices_425) then 20 else
  if p.val = (false, vertices_369) then 22 else
  if p.val = (false, vertices_897) then 0 else
  if p.val = (true, vertices_22) then 1 else
  if p.val = (true, vertices_262) then 2 else
  if p.val = (true, vertices_518) then 3 else
  if p.val = (true, vertices_26) then 4 else
  if p.val = (true, vertices_178) then 15 else
  if p.val = (true, vertices_274) then 5 else
  if p.val = (true, vertices_386) then 6 else
  if p.val = (true, vertices_770) then 7 else
  if p.val = (true, vertices_84) then 8 else
  if p.val = (true, vertices_532) then 9 else
  if p.val = (true, vertices_56) then 10 else
  if p.val = (true, vertices_536) then 11 else
  if p.val = (true, vertices_560) then 12 else
  0
cert_priority
cert_nodeAtPriority_37 897 22 262 518 26 274 386 770 84 532 56 536 560 651 178 837 617 425 369
cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 3 4 6 178
cert_row_4 1 0 1 2 3 8 542 22 2
cert_row_4 2 0 1 3 5 7 342 22 3
cert_row_4 3 1 3 4 5 8 628 84 2
cert_rows
cert_pivot_2 6 2 0 1
cert_heightProof 4
cert_coverFacet 0 542
cert_cover_5 0 1 0 1 2 3 22 542 2
cert_coverFacet 1 342
cert_cover_5 1 2 0 1 3 5 22 342 3
cert_coverFacet 2 774
cert_cover_2 2 1 0 7 8 262 774 3
cert_coverFacet 3 186
cert_cover_5 3 0 0 2 3 4 26 186 3
cert_coverFacet 4 434
cert_cover_5 4 0 0 3 4 7 178 434 3
cert_coverFacet 5 898
cert_cover_2 5 6 0 7 8 386 898 3
cert_coverFacet 6 628
cert_cover_5 6 3 1 3 4 5 84 628 2
cert_coverFacet 7 568
cert_cover_2 7 3 2 4 8 56 568 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0586

end
end BundlePart5

section BundlePart6
/- Source: ProjectionCertificates/R_m14e10q1_0587.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0587

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [27, 267, 595, 451, 901, 793, 737, 302, 122, 354, 684, 780, 484, 632, 11, 19, 67, 259, 25, 265, 529, 193, 577, 385, 641, 769, 26, 42, 266, 82, 98, 290, 322, 44, 268, 524, 164, 292, 388, 644, 772, 120, 536, 552, 776, 592, 224, 352, 608, 672, 448]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_27, vertices_267, vertices_595, vertices_451, vertices_901, vertices_793, vertices_737, vertices_302, vertices_122, vertices_354, vertices_684, vertices_780, vertices_484, vertices_632] (by decide +kernel)
  polygons := literalFinset [vertices_11, vertices_19, vertices_67, vertices_259, vertices_25, vertices_265, vertices_529, vertices_193, vertices_577, vertices_385, vertices_641, vertices_769, vertices_26, vertices_42, vertices_266, vertices_82, vertices_98, vertices_290, vertices_322, vertices_44, vertices_268, vertices_524, vertices_164, vertices_292, vertices_388, vertices_644, vertices_772, vertices_120, vertices_536, vertices_552, vertices_776, vertices_592, vertices_224, vertices_352, vertices_608, vertices_672, vertices_448] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_27), (false, vertices_267), (false, vertices_595), (false, vertices_451), (false, vertices_901), (false, vertices_793), (false, vertices_737), (true, vertices_42), (true, vertices_98), (true, vertices_290), (true, vertices_44), (true, vertices_268), (true, vertices_524), (true, vertices_164), (true, vertices_292), (true, vertices_120), (true, vertices_552), (true, vertices_352)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 12 15 17 20 21 23 24 25 26
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_27) then 0 else
  if p.val = (false, vertices_267) then 1 else
  if p.val = (false, vertices_595) then 13 else
  if p.val = (false, vertices_451) then 14 else
  if p.val = (false, vertices_901) then 16 else
  if p.val = (false, vertices_793) then 18 else
  if p.val = (false, vertices_737) then 22 else
  if p.val = (true, vertices_42) then 2 else
  if p.val = (true, vertices_98) then 3 else
  if p.val = (true, vertices_290) then 4 else
  if p.val = (true, vertices_44) then 5 else
  if p.val = (true, vertices_268) then 6 else
  if p.val = (true, vertices_524) then 7 else
  if p.val = (true, vertices_164) then 8 else
  if p.val = (true, vertices_292) then 9 else
  if p.val = (true, vertices_120) then 19 else
  if p.val = (true, vertices_552) then 10 else
  if p.val = (true, vertices_352) then 11 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_27), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_267), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_42), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_98), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_290), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_44), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_268), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_524), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_164), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_292), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_552), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_352), by decide +kernel⟩
  | 12 => Sum.inl 0
  | 13 => Sum.inr ⟨(false, vertices_595), by decide +kernel⟩
  | 14 => Sum.inr ⟨(false, vertices_451), by decide +kernel⟩
  | 15 => Sum.inl 1
  | 16 => Sum.inr ⟨(false, vertices_901), by decide +kernel⟩
  | 17 => Sum.inl 2
  | 18 => Sum.inr ⟨(false, vertices_793), by decide +kernel⟩
  | 19 => Sum.inr ⟨(true, vertices_120), by decide +kernel⟩
  | 20 => Sum.inl 3
  | 21 => Sum.inl 4
  | 22 => Sum.inr ⟨(false, vertices_737), by decide +kernel⟩
  | 23 => Sum.inl 5
  | 24 => Sum.inl 6
  | 25 => Sum.inl 7
  | 26 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 2 3 4 5 120
cert_row_4 1 0 1 2 4 7 302 42 1
cert_row_4 2 1 2 4 6 8 684 44 3
cert_row_4 3 1 4 5 6 7 484 164 2
cert_rows
cert_pivot_2 3 0 2 1
cert_heightProof 4
cert_coverFacet 0 302
cert_cover_5 0 1 0 1 2 4 42 302 1
cert_coverFacet 1 122
cert_cover_5 1 0 0 2 3 4 26 122 3
cert_coverFacet 2 354
cert_cover_2 2 4 0 5 7 98 354 3
cert_coverFacet 3 684
cert_cover_5 3 2 1 2 4 6 44 684 3
cert_coverFacet 4 780
cert_cover_2 4 2 1 7 8 268 780 3
cert_coverFacet 5 484
cert_cover_5 5 3 1 4 5 6 164 484 2
cert_coverFacet 6 632
cert_cover_5 6 0 2 3 4 8 120 632 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0587

end
end BundlePart6

section BundlePart7
/- Source: ProjectionCertificates/R_m14e10q1_0588.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0588

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [279, 653, 213, 773, 369, 961, 62, 526, 774, 682, 306, 866, 188, 752, 21, 133, 261, 517, 81, 273, 193, 321, 641, 769, 14, 22, 262, 518, 42, 522, 50, 274, 290, 546, 770, 60, 140, 524, 148, 772, 168, 648, 112, 176, 304, 208, 352, 608, 672, 704, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_279, vertices_653, vertices_213, vertices_773, vertices_369, vertices_961, vertices_62, vertices_526, vertices_774, vertices_682, vertices_306, vertices_866, vertices_188, vertices_752] (by decide +kernel)
  polygons := literalFinset [vertices_21, vertices_133, vertices_261, vertices_517, vertices_81, vertices_273, vertices_193, vertices_321, vertices_641, vertices_769, vertices_14, vertices_22, vertices_262, vertices_518, vertices_42, vertices_522, vertices_50, vertices_274, vertices_290, vertices_546, vertices_770, vertices_60, vertices_140, vertices_524, vertices_148, vertices_772, vertices_168, vertices_648, vertices_112, vertices_176, vertices_304, vertices_208, vertices_352, vertices_608, vertices_672, vertices_704, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_279), (false, vertices_653), (false, vertices_213), (false, vertices_773), (false, vertices_369), (false, vertices_961), (true, vertices_14), (true, vertices_518), (true, vertices_42), (true, vertices_522), (true, vertices_50), (true, vertices_290), (true, vertices_546), (true, vertices_770), (true, vertices_60), (true, vertices_168), (true, vertices_176), (true, vertices_608), (true, vertices_672)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 13 15 19 20 22 23 25 26 27
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_279) then 14 else
  if p.val = (false, vertices_653) then 16 else
  if p.val = (false, vertices_213) then 17 else
  if p.val = (false, vertices_773) then 0 else
  if p.val = (false, vertices_369) then 21 else
  if p.val = (false, vertices_961) then 24 else
  if p.val = (true, vertices_14) then 1 else
  if p.val = (true, vertices_518) then 2 else
  if p.val = (true, vertices_42) then 3 else
  if p.val = (true, vertices_522) then 4 else
  if p.val = (true, vertices_50) then 5 else
  if p.val = (true, vertices_290) then 6 else
  if p.val = (true, vertices_546) then 7 else
  if p.val = (true, vertices_770) then 8 else
  if p.val = (true, vertices_60) then 18 else
  if p.val = (true, vertices_168) then 9 else
  if p.val = (true, vertices_176) then 10 else
  if p.val = (true, vertices_608) then 11 else
  if p.val = (true, vertices_672) then 12 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_773), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_14), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_518), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_42), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_522), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_50), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_290), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_546), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_770), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_168), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_176), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_608), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_672), by decide +kernel⟩
  | 13 => Sum.inl 0
  | 14 => Sum.inr ⟨(false, vertices_279), by decide +kernel⟩
  | 15 => Sum.inl 1
  | 16 => Sum.inr ⟨(false, vertices_653), by decide +kernel⟩
  | 17 => Sum.inr ⟨(false, vertices_213), by decide +kernel⟩
  | 18 => Sum.inr ⟨(true, vertices_60), by decide +kernel⟩
  | 19 => Sum.inl 2
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
cert_row_2 0 1 2 3 4 60
cert_row_4 1 0 2 4 6 8 682 42 3
cert_row_4 2 0 4 5 7 8 866 290 2
cert_row_4 3 3 4 5 6 8 752 112 3
cert_rows
cert_pivot_2 1 2 0 3
cert_heightProof 4
cert_coverFacet 0 62
cert_cover_5 0 0 0 1 2 3 14 62 3
cert_coverFacet 1 526
cert_cover_2 1 1 0 2 8 14 526 3
cert_coverFacet 2 774
cert_cover_2 2 1 0 7 8 262 774 3
cert_coverFacet 3 682
cert_cover_5 3 1 0 2 4 6 42 682 3
cert_coverFacet 4 306
cert_cover_2 4 3 0 4 7 50 306 3
cert_coverFacet 5 866
cert_cover_5 5 2 0 4 5 7 290 866 2
cert_coverFacet 6 188
cert_cover_5 6 0 1 2 3 6 60 188 3
cert_coverFacet 7 752
cert_cover_5 7 3 3 4 5 6 112 752 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0588

end
end BundlePart7

section BundlePart8
/- Source: ProjectionCertificates/R_m14e10q1_0590.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0590

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [279, 167, 803, 661, 681, 849, 342, 198, 458, 418, 716, 596, 872, 424, 7, 35, 259, 21, 133, 273, 529, 161, 545, 641, 769, 278, 70, 134, 162, 290, 194, 322, 386, 84, 532, 196, 580, 644, 168, 296, 552, 200, 328, 584, 392, 648, 336, 592, 416, 800, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_279, vertices_167, vertices_803, vertices_661, vertices_681, vertices_849, vertices_342, vertices_198, vertices_458, vertices_418, vertices_716, vertices_596, vertices_872, vertices_424] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_35, vertices_259, vertices_21, vertices_133, vertices_273, vertices_529, vertices_161, vertices_545, vertices_641, vertices_769, vertices_278, vertices_70, vertices_134, vertices_162, vertices_290, vertices_194, vertices_322, vertices_386, vertices_84, vertices_532, vertices_196, vertices_580, vertices_644, vertices_168, vertices_296, vertices_552, vertices_200, vertices_328, vertices_584, vertices_392, vertices_648, vertices_336, vertices_592, vertices_416, vertices_800, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_279), (false, vertices_167), (false, vertices_803), (false, vertices_661), (false, vertices_681), (false, vertices_849), (true, vertices_70), (true, vertices_194), (true, vertices_322), (true, vertices_386), (true, vertices_84), (true, vertices_196), (true, vertices_580), (true, vertices_296), (true, vertices_200), (true, vertices_328), (true, vertices_584), (true, vertices_392), (true, vertices_416)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 13 17 19 21 23 24 25 26 27
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_279) then 14 else
  if p.val = (false, vertices_167) then 15 else
  if p.val = (false, vertices_803) then 16 else
  if p.val = (false, vertices_661) then 18 else
  if p.val = (false, vertices_681) then 20 else
  if p.val = (false, vertices_849) then 22 else
  if p.val = (true, vertices_70) then 0 else
  if p.val = (true, vertices_194) then 1 else
  if p.val = (true, vertices_322) then 2 else
  if p.val = (true, vertices_386) then 3 else
  if p.val = (true, vertices_84) then 4 else
  if p.val = (true, vertices_196) then 5 else
  if p.val = (true, vertices_580) then 6 else
  if p.val = (true, vertices_296) then 7 else
  if p.val = (true, vertices_200) then 8 else
  if p.val = (true, vertices_328) then 9 else
  if p.val = (true, vertices_584) then 10 else
  if p.val = (true, vertices_392) then 11 else
  if p.val = (true, vertices_416) then 12 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_70), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_194), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_322), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_386), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_84), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_196), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_580), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_296), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_200), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_328), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_584), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_392), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_416), by decide +kernel⟩
  | 13 => Sum.inl 0
  | 14 => Sum.inr ⟨(false, vertices_279), by decide +kernel⟩
  | 15 => Sum.inr ⟨(false, vertices_167), by decide +kernel⟩
  | 16 => Sum.inr ⟨(false, vertices_803), by decide +kernel⟩
  | 17 => Sum.inl 1
  | 18 => Sum.inr ⟨(false, vertices_661), by decide +kernel⟩
  | 19 => Sum.inl 2
  | 20 => Sum.inr ⟨(false, vertices_681), by decide +kernel⟩
  | 21 => Sum.inl 3
  | 22 => Sum.inr ⟨(false, vertices_849), by decide +kernel⟩
  | 23 => Sum.inl 4
  | 24 => Sum.inl 5
  | 25 => Sum.inl 6
  | 26 => Sum.inl 7
  | 27 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 1 3 7 278
cert_row_4 1 0 2 5 6 7 458 194 1
cert_row_4 2 1 2 5 6 8 716 196 1
cert_row_4 3 2 4 5 7 8 872 296 2
cert_rows
cert_pivot_2 3 0 1 2
cert_heightProof 4
cert_coverFacet 0 342
cert_cover_5 0 0 0 1 3 5 278 342 3
cert_coverFacet 1 198
cert_cover_2 1 1 0 5 6 70 198 3
cert_coverFacet 2 458
cert_cover_5 2 1 0 2 5 6 194 458 1
cert_coverFacet 3 418
cert_cover_2 3 4 0 6 7 162 418 3
cert_coverFacet 4 716
cert_cover_5 4 2 1 2 5 6 196 716 1
cert_coverFacet 5 596
cert_cover_2 5 3 1 5 8 84 596 3
cert_coverFacet 6 872
cert_cover_5 6 3 2 4 5 7 296 872 2
cert_coverFacet 7 424
cert_cover_2 7 4 2 6 7 168 424 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0590

end
end BundlePart8

section BundlePart9
/- Source: ProjectionCertificates/R_m14e10q1_0591.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0591

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [583, 331, 803, 565, 229, 481, 714, 778, 668, 436, 708, 472, 792, 816, 67, 259, 515, 37, 69, 517, 225, 289, 545, 321, 74, 266, 522, 578, 770, 52, 148, 532, 164, 196, 580, 644, 152, 280, 536, 200, 328, 648, 776, 304, 560, 400, 784, 416, 800, 448, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_583, vertices_331, vertices_803, vertices_565, vertices_229, vertices_481, vertices_714, vertices_778, vertices_668, vertices_436, vertices_708, vertices_472, vertices_792, vertices_816] (by decide +kernel)
  polygons := literalFinset [vertices_67, vertices_259, vertices_515, vertices_37, vertices_69, vertices_517, vertices_225, vertices_289, vertices_545, vertices_321, vertices_74, vertices_266, vertices_522, vertices_578, vertices_770, vertices_52, vertices_148, vertices_532, vertices_164, vertices_196, vertices_580, vertices_644, vertices_152, vertices_280, vertices_536, vertices_200, vertices_328, vertices_648, vertices_776, vertices_304, vertices_560, vertices_400, vertices_784, vertices_416, vertices_800, vertices_448, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_583), (false, vertices_331), (false, vertices_803), (false, vertices_565), (false, vertices_229), (false, vertices_481), (true, vertices_522), (true, vertices_148), (true, vertices_644), (true, vertices_152), (true, vertices_280), (true, vertices_536), (true, vertices_200), (true, vertices_648), (true, vertices_776), (true, vertices_304), (true, vertices_400), (true, vertices_784), (true, vertices_704)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 13 17 19 20 21 24 25 26 27
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_583) then 14 else
  if p.val = (false, vertices_331) then 15 else
  if p.val = (false, vertices_803) then 16 else
  if p.val = (false, vertices_565) then 18 else
  if p.val = (false, vertices_229) then 22 else
  if p.val = (false, vertices_481) then 23 else
  if p.val = (true, vertices_522) then 0 else
  if p.val = (true, vertices_148) then 1 else
  if p.val = (true, vertices_644) then 2 else
  if p.val = (true, vertices_152) then 3 else
  if p.val = (true, vertices_280) then 4 else
  if p.val = (true, vertices_536) then 5 else
  if p.val = (true, vertices_200) then 6 else
  if p.val = (true, vertices_648) then 7 else
  if p.val = (true, vertices_776) then 8 else
  if p.val = (true, vertices_304) then 9 else
  if p.val = (true, vertices_400) then 10 else
  if p.val = (true, vertices_784) then 11 else
  if p.val = (true, vertices_704) then 12 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_522), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_148), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_644), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_152), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_280), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_536), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_200), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_648), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_776), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_304), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_400), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_784), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_704), by decide +kernel⟩
  | 13 => Sum.inl 0
  | 14 => Sum.inr ⟨(false, vertices_583), by decide +kernel⟩
  | 15 => Sum.inr ⟨(false, vertices_331), by decide +kernel⟩
  | 16 => Sum.inr ⟨(false, vertices_803), by decide +kernel⟩
  | 17 => Sum.inl 1
  | 18 => Sum.inr ⟨(false, vertices_565), by decide +kernel⟩
  | 19 => Sum.inl 2
  | 20 => Sum.inl 3
  | 21 => Sum.inl 4
  | 22 => Sum.inr ⟨(false, vertices_229), by decide +kernel⟩
  | 23 => Sum.inr ⟨(false, vertices_481), by decide +kernel⟩
  | 24 => Sum.inl 5
  | 25 => Sum.inl 6
  | 26 => Sum.inl 7
  | 27 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 2 5 6 8 714 74 3
cert_row_4 1 1 2 3 6 8 668 148 1
cert_row_4 2 1 3 4 6 7 436 52 3
cert_row_4 3 2 3 5 6 7 472 152 2
cert_rows
cert_pivot_2 0 8 1 2
cert_heightProof 4
cert_coverFacet 0 714
cert_cover_5 0 0 0 2 5 6 74 714 3
cert_coverFacet 1 778
cert_cover_2 1 2 0 7 8 266 778 3
cert_coverFacet 2 668
cert_cover_5 2 1 1 2 3 6 148 668 1
cert_coverFacet 3 436
cert_cover_5 3 2 1 3 4 6 52 436 3
cert_coverFacet 4 708
cert_cover_2 4 5 1 6 8 196 708 3
cert_coverFacet 5 472
cert_cover_5 5 3 2 3 5 6 152 472 2
cert_coverFacet 6 792
cert_cover_2 6 3 2 7 8 280 792 3
cert_coverFacet 7 816
cert_cover_2 7 4 3 7 8 304 816 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0591

end
end BundlePart9

section BundlePart10
/- Source: ProjectionCertificates/R_m14e10q1_0600.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0600

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [203, 267, 899, 709, 601, 281, 817, 358, 454, 314, 106, 620, 932, 568, 11, 131, 259, 25, 73, 265, 273, 529, 193, 577, 641, 769, 326, 42, 74, 266, 98, 290, 194, 386, 100, 292, 548, 196, 580, 388, 644, 56, 280, 536, 104, 552, 584, 304, 560, 800, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_203, vertices_267, vertices_899, vertices_709, vertices_601, vertices_281, vertices_817, vertices_358, vertices_454, vertices_314, vertices_106, vertices_620, vertices_932, vertices_568] (by decide +kernel)
  polygons := literalFinset [vertices_11, vertices_131, vertices_259, vertices_25, vertices_73, vertices_265, vertices_273, vertices_529, vertices_193, vertices_577, vertices_641, vertices_769, vertices_326, vertices_42, vertices_74, vertices_266, vertices_98, vertices_290, vertices_194, vertices_386, vertices_100, vertices_292, vertices_548, vertices_196, vertices_580, vertices_388, vertices_644, vertices_56, vertices_280, vertices_536, vertices_104, vertices_552, vertices_584, vertices_304, vertices_560, vertices_800, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_203), (false, vertices_267), (false, vertices_899), (false, vertices_709), (false, vertices_601), (false, vertices_281), (false, vertices_817), (true, vertices_326), (true, vertices_42), (true, vertices_98), (true, vertices_290), (true, vertices_100), (true, vertices_292), (true, vertices_548), (true, vertices_388), (true, vertices_56), (true, vertices_104), (true, vertices_552)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 12 16 18 20 22 23 24 25 26
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_203) then 13 else
  if p.val = (false, vertices_267) then 0 else
  if p.val = (false, vertices_899) then 14 else
  if p.val = (false, vertices_709) then 17 else
  if p.val = (false, vertices_601) then 19 else
  if p.val = (false, vertices_281) then 1 else
  if p.val = (false, vertices_817) then 21 else
  if p.val = (true, vertices_326) then 15 else
  if p.val = (true, vertices_42) then 2 else
  if p.val = (true, vertices_98) then 3 else
  if p.val = (true, vertices_290) then 4 else
  if p.val = (true, vertices_100) then 5 else
  if p.val = (true, vertices_292) then 6 else
  if p.val = (true, vertices_548) then 7 else
  if p.val = (true, vertices_388) then 8 else
  if p.val = (true, vertices_56) then 9 else
  if p.val = (true, vertices_104) then 10 else
  if p.val = (true, vertices_552) then 11 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_267), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_281), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_42), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_98), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_290), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_100), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_292), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_548), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_388), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_56), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_104), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_552), by decide +kernel⟩
  | 12 => Sum.inl 0
  | 13 => Sum.inr ⟨(false, vertices_203), by decide +kernel⟩
  | 14 => Sum.inr ⟨(false, vertices_899), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_326), by decide +kernel⟩
  | 16 => Sum.inl 1
  | 17 => Sum.inr ⟨(false, vertices_709), by decide +kernel⟩
  | 18 => Sum.inl 2
  | 19 => Sum.inr ⟨(false, vertices_601), by decide +kernel⟩
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
cert_row_4 0 0 2 3 4 7 314 42 2
cert_row_2 1 0 1 5 7 326
cert_row_4 2 1 2 4 5 8 620 100 1
cert_row_4 3 1 4 6 7 8 932 292 2
cert_rows
cert_pivot_2 3 0 2 1
cert_heightProof 4
cert_coverFacet 0 358
cert_cover_5 0 1 0 1 4 5 326 358 2
cert_coverFacet 1 454
cert_cover_5 1 1 0 1 5 6 326 454 3
cert_coverFacet 2 314
cert_cover_5 2 0 0 2 3 4 42 314 2
cert_coverFacet 3 106
cert_cover_2 3 2 0 4 5 42 106 3
cert_coverFacet 4 620
cert_cover_5 4 2 1 2 4 5 100 620 1
cert_coverFacet 5 932
cert_cover_5 5 3 1 4 6 7 292 932 2
cert_coverFacet 6 568
cert_cover_2 6 3 2 4 8 56 568 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0600

end
end BundlePart10

section BundlePart11
/- Source: ProjectionCertificates/R_m14e10q1_0609.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0609

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [675, 661, 345, 625, 401, 481, 302, 558, 406, 646, 418, 604, 284, 872, 81, 145, 273, 529, 97, 161, 545, 321, 385, 641, 46, 134, 262, 518, 162, 290, 546, 386, 642, 28, 268, 524, 148, 276, 532, 644, 88, 280, 296, 552, 328, 584, 592, 400, 352, 608, 416]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_675, vertices_661, vertices_345, vertices_625, vertices_401, vertices_481, vertices_302, vertices_558, vertices_406, vertices_646, vertices_418, vertices_604, vertices_284, vertices_872] (by decide +kernel)
  polygons := literalFinset [vertices_81, vertices_145, vertices_273, vertices_529, vertices_97, vertices_161, vertices_545, vertices_321, vertices_385, vertices_641, vertices_46, vertices_134, vertices_262, vertices_518, vertices_162, vertices_290, vertices_546, vertices_386, vertices_642, vertices_28, vertices_268, vertices_524, vertices_148, vertices_276, vertices_532, vertices_644, vertices_88, vertices_280, vertices_296, vertices_552, vertices_328, vertices_584, vertices_592, vertices_400, vertices_352, vertices_608, vertices_416] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_675), (false, vertices_661), (false, vertices_345), (false, vertices_625), (false, vertices_401), (false, vertices_481), (true, vertices_46), (true, vertices_134), (true, vertices_262), (true, vertices_518), (true, vertices_290), (true, vertices_386), (true, vertices_28), (true, vertices_268), (true, vertices_524), (true, vertices_276), (true, vertices_296), (true, vertices_552), (true, vertices_584)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 13 16 18 20 22 24 25 26 27
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_675) then 14 else
  if p.val = (false, vertices_661) then 17 else
  if p.val = (false, vertices_345) then 19 else
  if p.val = (false, vertices_625) then 21 else
  if p.val = (false, vertices_401) then 0 else
  if p.val = (false, vertices_481) then 23 else
  if p.val = (true, vertices_46) then 15 else
  if p.val = (true, vertices_134) then 1 else
  if p.val = (true, vertices_262) then 2 else
  if p.val = (true, vertices_518) then 3 else
  if p.val = (true, vertices_290) then 4 else
  if p.val = (true, vertices_386) then 5 else
  if p.val = (true, vertices_28) then 6 else
  if p.val = (true, vertices_268) then 7 else
  if p.val = (true, vertices_524) then 8 else
  if p.val = (true, vertices_276) then 9 else
  if p.val = (true, vertices_296) then 10 else
  if p.val = (true, vertices_552) then 11 else
  if p.val = (true, vertices_584) then 12 else
  0
cert_priority
cert_nodeAtPriority_49 401 134 262 518 290 386 28 268 524 276 296 552 584 675 46 661 345 625 481
cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 3 6 7 406 134 2
cert_row_2 1 0 1 2 4 46
cert_row_4 2 1 2 3 5 8 604 28 3
cert_row_4 3 2 4 5 7 8 872 296 2
cert_rows
cert_pivot_2 6 0 1 2
cert_heightProof 4
cert_coverFacet 0 302
cert_cover_5 0 1 0 1 2 7 46 302 3
cert_coverFacet 1 558
cert_cover_5 1 1 0 1 2 8 46 558 3
cert_coverFacet 2 406
cert_cover_5 2 0 0 1 3 6 134 406 2
cert_coverFacet 3 646
cert_cover_2 3 1 0 6 8 134 646 3
cert_coverFacet 4 418
cert_cover_2 4 4 0 6 7 162 418 3
cert_coverFacet 5 604
cert_cover_5 5 2 1 2 3 5 28 604 3
cert_coverFacet 6 284
cert_cover_2 6 2 1 3 7 28 284 3
cert_coverFacet 7 872
cert_cover_5 7 3 2 4 5 7 296 872 2
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0609

end
end BundlePart11

section BundlePart12
/- Source: ProjectionCertificates/R_m14e10q1_0623.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0623

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [279, 539, 355, 611, 597, 453, 282, 682, 298, 668, 404, 708, 440, 992, 19, 99, 259, 515, 21, 69, 261, 529, 321, 577, 26, 42, 266, 522, 274, 290, 546, 148, 276, 532, 196, 580, 388, 644, 152, 280, 536, 168, 296, 648, 400, 352, 608, 416, 672, 448, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_279, vertices_539, vertices_355, vertices_611, vertices_597, vertices_453, vertices_282, vertices_682, vertices_298, vertices_668, vertices_404, vertices_708, vertices_440, vertices_992] (by decide +kernel)
  polygons := literalFinset [vertices_19, vertices_99, vertices_259, vertices_515, vertices_21, vertices_69, vertices_261, vertices_529, vertices_321, vertices_577, vertices_26, vertices_42, vertices_266, vertices_522, vertices_274, vertices_290, vertices_546, vertices_148, vertices_276, vertices_532, vertices_196, vertices_580, vertices_388, vertices_644, vertices_152, vertices_280, vertices_536, vertices_168, vertices_296, vertices_648, vertices_400, vertices_352, vertices_608, vertices_416, vertices_672, vertices_448, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_279), (false, vertices_539), (false, vertices_355), (false, vertices_611), (false, vertices_597), (false, vertices_453), (true, vertices_42), (true, vertices_266), (true, vertices_148), (true, vertices_644), (true, vertices_152), (true, vertices_280), (true, vertices_168), (true, vertices_296), (true, vertices_648), (true, vertices_400), (true, vertices_416), (true, vertices_672), (true, vertices_704)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 17 13 21 22 23 24 25 26 27
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_279) then 14 else
  if p.val = (false, vertices_539) then 18 else
  if p.val = (false, vertices_355) then 19 else
  if p.val = (false, vertices_611) then 20 else
  if p.val = (false, vertices_597) then 15 else
  if p.val = (false, vertices_453) then 16 else
  if p.val = (true, vertices_42) then 0 else
  if p.val = (true, vertices_266) then 1 else
  if p.val = (true, vertices_148) then 2 else
  if p.val = (true, vertices_644) then 3 else
  if p.val = (true, vertices_152) then 4 else
  if p.val = (true, vertices_280) then 5 else
  if p.val = (true, vertices_168) then 6 else
  if p.val = (true, vertices_296) then 7 else
  if p.val = (true, vertices_648) then 8 else
  if p.val = (true, vertices_400) then 9 else
  if p.val = (true, vertices_416) then 10 else
  if p.val = (true, vertices_672) then 11 else
  if p.val = (true, vertices_704) then 12 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_42), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_266), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_148), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_644), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_152), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_280), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_168), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_296), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_648), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_400), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_416), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_672), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_704), by decide +kernel⟩
  | 13 => Sum.inl 1
  | 14 => Sum.inr ⟨(false, vertices_279), by decide +kernel⟩
  | 15 => Sum.inr ⟨(false, vertices_597), by decide +kernel⟩
  | 16 => Sum.inr ⟨(false, vertices_453), by decide +kernel⟩
  | 17 => Sum.inl 0
  | 18 => Sum.inr ⟨(false, vertices_539), by decide +kernel⟩
  | 19 => Sum.inr ⟨(false, vertices_355), by decide +kernel⟩
  | 20 => Sum.inr ⟨(false, vertices_611), by decide +kernel⟩
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
cert_row_4 0 0 2 4 6 8 682 42 3
cert_row_4 1 1 2 3 6 8 668 148 1
cert_row_4 2 2 3 4 6 7 440 152 2
cert_row_4 3 4 5 6 7 8 992 352 2
cert_rows
cert_pivot_2 0 1 2 4
cert_heightProof 4
cert_coverFacet 0 282
cert_cover_2 0 2 0 3 7 26 282 3
cert_coverFacet 1 682
cert_cover_5 1 0 0 2 4 6 42 682 3
cert_coverFacet 2 298
cert_cover_2 2 2 0 4 7 42 298 3
cert_coverFacet 3 668
cert_cover_5 3 1 1 2 3 6 148 668 1
cert_coverFacet 4 404
cert_cover_2 4 3 1 6 7 148 404 3
cert_coverFacet 5 708
cert_cover_2 5 5 1 6 8 196 708 3
cert_coverFacet 6 440
cert_cover_5 6 2 2 3 4 6 152 440 2
cert_coverFacet 7 992
cert_cover_5 7 3 4 5 6 7 352 992 2
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0623

end
end BundlePart12

section BundlePart13
/- Source: ProjectionCertificates/R_m14e10q1_0624.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0624

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [647, 181, 357, 837, 121, 721, 782, 422, 666, 394, 184, 600, 872, 424, 37, 325, 133, 517, 49, 81, 145, 97, 577, 641, 134, 262, 518, 138, 266, 522, 386, 642, 164, 292, 772, 56, 88, 152, 536, 104, 168, 296, 584, 392, 776, 176, 592, 656, 352, 416, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_647, vertices_181, vertices_357, vertices_837, vertices_121, vertices_721, vertices_782, vertices_422, vertices_666, vertices_394, vertices_184, vertices_600, vertices_872, vertices_424] (by decide +kernel)
  polygons := literalFinset [vertices_37, vertices_325, vertices_133, vertices_517, vertices_49, vertices_81, vertices_145, vertices_97, vertices_577, vertices_641, vertices_134, vertices_262, vertices_518, vertices_138, vertices_266, vertices_522, vertices_386, vertices_642, vertices_164, vertices_292, vertices_772, vertices_56, vertices_88, vertices_152, vertices_536, vertices_104, vertices_168, vertices_296, vertices_584, vertices_392, vertices_776, vertices_176, vertices_592, vertices_656, vertices_352, vertices_416, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_647), (false, vertices_181), (false, vertices_357), (false, vertices_837), (false, vertices_121), (false, vertices_721), (true, vertices_262), (true, vertices_138), (true, vertices_266), (true, vertices_522), (true, vertices_386), (true, vertices_152), (true, vertices_536), (true, vertices_168), (true, vertices_296), (true, vertices_584), (true, vertices_392), (true, vertices_776), (true, vertices_416)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 13 15 19 21 23 24 25 26 27
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_647) then 14 else
  if p.val = (false, vertices_181) then 16 else
  if p.val = (false, vertices_357) then 17 else
  if p.val = (false, vertices_837) then 18 else
  if p.val = (false, vertices_121) then 20 else
  if p.val = (false, vertices_721) then 22 else
  if p.val = (true, vertices_262) then 0 else
  if p.val = (true, vertices_138) then 1 else
  if p.val = (true, vertices_266) then 2 else
  if p.val = (true, vertices_522) then 3 else
  if p.val = (true, vertices_386) then 4 else
  if p.val = (true, vertices_152) then 5 else
  if p.val = (true, vertices_536) then 6 else
  if p.val = (true, vertices_168) then 7 else
  if p.val = (true, vertices_296) then 8 else
  if p.val = (true, vertices_584) then 9 else
  if p.val = (true, vertices_392) then 10 else
  if p.val = (true, vertices_776) then 11 else
  if p.val = (true, vertices_416) then 12 else
  0
cert_priority
cert_nodeAtPriority_11 262 138 266 522 386 152 536 168 296 584 392 776 416 647 181 357 837 121 721
cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 2 3 6 8 666 138 2
cert_row_4 1 0 1 4 6 7 422 134 2
cert_row_4 2 0 1 2 7 8 782 262 2
cert_row_4 3 2 4 5 7 8 872 104 3
cert_rows
cert_pivot_2 3 6 0 2
cert_heightProof 4
cert_coverFacet 0 782
cert_cover_5 0 2 0 1 2 7 262 782 2
cert_coverFacet 1 422
cert_cover_5 1 1 0 1 4 6 134 422 2
cert_coverFacet 2 666
cert_cover_5 2 0 0 2 3 6 138 666 2
cert_coverFacet 3 394
cert_cover_2 3 2 0 6 7 138 394 3
cert_coverFacet 4 184
cert_cover_2 4 3 2 4 6 56 184 3
cert_coverFacet 5 600
cert_cover_2 5 3 2 5 8 88 600 3
cert_coverFacet 6 872
cert_cover_5 6 3 2 4 5 7 104 872 3
cert_coverFacet 7 424
cert_cover_2 7 4 2 6 7 168 424 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0624

end
end BundlePart13

section BundlePart14
/- Source: ProjectionCertificates/R_m14e10q1_0625.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0625

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [403, 565, 617, 305, 721, 481, 558, 270, 662, 278, 842, 962, 316, 360, 49, 145, 273, 529, 97, 289, 545, 193, 577, 385, 14, 22, 262, 518, 266, 522, 146, 274, 834, 386, 642, 44, 268, 52, 276, 532, 548, 104, 296, 552, 328, 584, 304, 656, 352, 448, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_403, vertices_565, vertices_617, vertices_305, vertices_721, vertices_481, vertices_558, vertices_270, vertices_662, vertices_278, vertices_842, vertices_962, vertices_316, vertices_360] (by decide +kernel)
  polygons := literalFinset [vertices_49, vertices_145, vertices_273, vertices_529, vertices_97, vertices_289, vertices_545, vertices_193, vertices_577, vertices_385, vertices_14, vertices_22, vertices_262, vertices_518, vertices_266, vertices_522, vertices_146, vertices_274, vertices_834, vertices_386, vertices_642, vertices_44, vertices_268, vertices_52, vertices_276, vertices_532, vertices_548, vertices_104, vertices_296, vertices_552, vertices_328, vertices_584, vertices_304, vertices_656, vertices_352, vertices_448, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_403), (false, vertices_565), (false, vertices_617), (false, vertices_305), (false, vertices_721), (false, vertices_481), (true, vertices_14), (true, vertices_22), (true, vertices_262), (true, vertices_518), (true, vertices_266), (true, vertices_522), (true, vertices_834), (true, vertices_642), (true, vertices_44), (true, vertices_268), (true, vertices_276), (true, vertices_296), (true, vertices_328)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 13 16 18 20 22 24 25 26 27
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_403) then 14 else
  if p.val = (false, vertices_565) then 17 else
  if p.val = (false, vertices_617) then 19 else
  if p.val = (false, vertices_305) then 0 else
  if p.val = (false, vertices_721) then 21 else
  if p.val = (false, vertices_481) then 23 else
  if p.val = (true, vertices_14) then 1 else
  if p.val = (true, vertices_22) then 2 else
  if p.val = (true, vertices_262) then 3 else
  if p.val = (true, vertices_518) then 4 else
  if p.val = (true, vertices_266) then 5 else
  if p.val = (true, vertices_522) then 6 else
  if p.val = (true, vertices_834) then 15 else
  if p.val = (true, vertices_642) then 7 else
  if p.val = (true, vertices_44) then 8 else
  if p.val = (true, vertices_268) then 9 else
  if p.val = (true, vertices_276) then 10 else
  if p.val = (true, vertices_296) then 11 else
  if p.val = (true, vertices_328) then 12 else
  0
cert_priority
cert_nodeAtPriority_49 305 14 22 262 518 266 522 642 44 268 276 296 328 403 834 565 617 721 481
cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 5 7 8 834
cert_row_4 1 0 1 3 6 8 662 22 3
cert_row_4 2 0 1 2 4 8 558 14 3
cert_row_4 3 1 2 3 4 7 316 44 2
cert_rows
cert_pivot_2 5 6 0 1
cert_heightProof 4
cert_coverFacet 0 558
cert_cover_5 0 2 0 1 2 4 14 558 3
cert_coverFacet 1 270
cert_cover_2 1 1 0 2 7 14 270 3
cert_coverFacet 2 662
cert_cover_5 2 1 0 1 3 6 22 662 3
cert_coverFacet 3 278
cert_cover_2 3 1 0 3 7 22 278 3
cert_coverFacet 4 842
cert_cover_5 4 0 0 2 5 7 266 842 2
cert_coverFacet 5 962
cert_cover_5 5 0 0 5 6 7 834 962 2
cert_coverFacet 6 316
cert_cover_5 6 3 1 2 3 4 44 316 2
cert_coverFacet 7 360
cert_cover_2 7 4 2 5 7 104 360 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0625

end
end BundlePart14

section BundlePart15
/- Source: ProjectionCertificates/R_m14e10q1_0626.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0626

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [779, 341, 121, 281, 681, 865, 654, 406, 838, 394, 628, 692, 184, 408, 25, 41, 265, 521, 81, 273, 97, 545, 321, 769, 134, 262, 518, 138, 266, 522, 386, 770, 564, 84, 148, 276, 324, 580, 644, 56, 152, 280, 168, 392, 648, 112, 176, 400, 608, 672, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_779, vertices_341, vertices_121, vertices_281, vertices_681, vertices_865, vertices_654, vertices_406, vertices_838, vertices_394, vertices_628, vertices_692, vertices_184, vertices_408] (by decide +kernel)
  polygons := literalFinset [vertices_25, vertices_41, vertices_265, vertices_521, vertices_81, vertices_273, vertices_97, vertices_545, vertices_321, vertices_769, vertices_134, vertices_262, vertices_518, vertices_138, vertices_266, vertices_522, vertices_386, vertices_770, vertices_564, vertices_84, vertices_148, vertices_276, vertices_324, vertices_580, vertices_644, vertices_56, vertices_152, vertices_280, vertices_168, vertices_392, vertices_648, vertices_112, vertices_176, vertices_400, vertices_608, vertices_672, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_779), (false, vertices_341), (false, vertices_121), (false, vertices_281), (false, vertices_681), (false, vertices_865), (true, vertices_134), (true, vertices_262), (true, vertices_518), (true, vertices_138), (true, vertices_386), (true, vertices_564), (true, vertices_148), (true, vertices_580), (true, vertices_644), (true, vertices_152), (true, vertices_392), (true, vertices_176), (true, vertices_400)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 13 15 18 21 22 24 25 26 27
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_779) then 14 else
  if p.val = (false, vertices_341) then 16 else
  if p.val = (false, vertices_121) then 19 else
  if p.val = (false, vertices_281) then 0 else
  if p.val = (false, vertices_681) then 20 else
  if p.val = (false, vertices_865) then 23 else
  if p.val = (true, vertices_134) then 1 else
  if p.val = (true, vertices_262) then 2 else
  if p.val = (true, vertices_518) then 3 else
  if p.val = (true, vertices_138) then 4 else
  if p.val = (true, vertices_386) then 5 else
  if p.val = (true, vertices_564) then 17 else
  if p.val = (true, vertices_148) then 6 else
  if p.val = (true, vertices_580) then 7 else
  if p.val = (true, vertices_644) then 8 else
  if p.val = (true, vertices_152) then 9 else
  if p.val = (true, vertices_392) then 10 else
  if p.val = (true, vertices_176) then 11 else
  if p.val = (true, vertices_400) then 12 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_281), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_134), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_262), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_518), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_138), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_386), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_148), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_580), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_644), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_152), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_392), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_176), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_400), by decide +kernel⟩
  | 13 => Sum.inl 0
  | 14 => Sum.inr ⟨(false, vertices_779), by decide +kernel⟩
  | 15 => Sum.inl 1
  | 16 => Sum.inr ⟨(false, vertices_341), by decide +kernel⟩
  | 17 => Sum.inr ⟨(true, vertices_564), by decide +kernel⟩
  | 18 => Sum.inl 2
  | 19 => Sum.inr ⟨(false, vertices_121), by decide +kernel⟩
  | 20 => Sum.inr ⟨(false, vertices_681), by decide +kernel⟩
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
cert_row_2 0 1 3 4 8 564
cert_row_4 1 0 1 2 6 8 654 134 2
cert_row_4 2 0 1 3 6 7 406 134 2
cert_row_4 3 0 1 5 7 8 838 262 2
cert_rows
cert_pivot_2 4 2 3 0
cert_heightProof 4
cert_coverFacet 0 654
cert_cover_5 0 1 0 1 2 6 134 654 2
cert_coverFacet 1 406
cert_cover_5 1 2 0 1 3 6 134 406 2
cert_coverFacet 2 838
cert_cover_5 2 3 0 1 5 7 262 838 2
cert_coverFacet 3 394
cert_cover_2 3 2 0 6 7 138 394 3
cert_coverFacet 4 628
cert_cover_5 4 0 1 3 4 5 564 628 3
cert_coverFacet 5 692
cert_cover_5 5 0 1 3 4 6 564 692 3
cert_coverFacet 6 184
cert_cover_2 6 3 2 4 6 56 184 3
cert_coverFacet 7 408
cert_cover_2 7 3 2 6 7 152 408 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0626

end
end BundlePart15

section BundlePart16
/- Source: ProjectionCertificates/R_m14e10q1_0627.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0627

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [651, 899, 205, 421, 837, 601, 806, 570, 154, 242, 418, 628, 228, 216, 643, 69, 133, 261, 73, 137, 521, 577, 385, 769, 26, 138, 522, 50, 146, 162, 290, 546, 386, 770, 100, 164, 292, 548, 196, 580, 772, 88, 152, 536, 200, 112, 560, 208, 592, 224, 416]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_651, vertices_899, vertices_205, vertices_421, vertices_837, vertices_601, vertices_806, vertices_570, vertices_154, vertices_242, vertices_418, vertices_628, vertices_228, vertices_216] (by decide +kernel)
  polygons := literalFinset [vertices_643, vertices_69, vertices_133, vertices_261, vertices_73, vertices_137, vertices_521, vertices_577, vertices_385, vertices_769, vertices_26, vertices_138, vertices_522, vertices_50, vertices_146, vertices_162, vertices_290, vertices_546, vertices_386, vertices_770, vertices_100, vertices_164, vertices_292, vertices_548, vertices_196, vertices_580, vertices_772, vertices_88, vertices_152, vertices_536, vertices_200, vertices_112, vertices_560, vertices_208, vertices_592, vertices_224, vertices_416] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_651), (false, vertices_899), (false, vertices_205), (false, vertices_421), (false, vertices_837), (false, vertices_601), (true, vertices_26), (true, vertices_50), (true, vertices_146), (true, vertices_162), (true, vertices_290), (true, vertices_546), (true, vertices_100), (true, vertices_548), (true, vertices_152), (true, vertices_112), (true, vertices_560), (true, vertices_208), (true, vertices_224)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 13 16 20 22 23 24 25 26 27
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_651) then 14 else
  if p.val = (false, vertices_899) then 15 else
  if p.val = (false, vertices_205) then 17 else
  if p.val = (false, vertices_421) then 18 else
  if p.val = (false, vertices_837) then 19 else
  if p.val = (false, vertices_601) then 21 else
  if p.val = (true, vertices_26) then 0 else
  if p.val = (true, vertices_50) then 1 else
  if p.val = (true, vertices_146) then 2 else
  if p.val = (true, vertices_162) then 3 else
  if p.val = (true, vertices_290) then 4 else
  if p.val = (true, vertices_546) then 5 else
  if p.val = (true, vertices_100) then 6 else
  if p.val = (true, vertices_548) then 7 else
  if p.val = (true, vertices_152) then 8 else
  if p.val = (true, vertices_112) then 9 else
  if p.val = (true, vertices_560) then 10 else
  if p.val = (true, vertices_208) then 11 else
  if p.val = (true, vertices_224) then 12 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_26), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_50), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_146), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_162), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_290), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_546), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_100), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_548), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_152), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_112), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_560), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_208), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_224), by decide +kernel⟩
  | 13 => Sum.inl 0
  | 14 => Sum.inr ⟨(false, vertices_651), by decide +kernel⟩
  | 15 => Sum.inr ⟨(false, vertices_899), by decide +kernel⟩
  | 16 => Sum.inl 1
  | 17 => Sum.inr ⟨(false, vertices_205), by decide +kernel⟩
  | 18 => Sum.inr ⟨(false, vertices_421), by decide +kernel⟩
  | 19 => Sum.inr ⟨(false, vertices_837), by decide +kernel⟩
  | 20 => Sum.inl 2
  | 21 => Sum.inr ⟨(false, vertices_601), by decide +kernel⟩
  | 22 => Sum.inl 3
  | 23 => Sum.inl 4
  | 24 => Sum.inl 5
  | 25 => Sum.inl 6
  | 26 => Sum.inl 7
  | 27 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 4 7 8 806 290 1
cert_row_4 1 0 2 3 4 8 570 26 3
cert_row_4 2 0 3 4 5 6 242 50 3
cert_row_4 3 1 3 4 5 8 628 100 1
cert_rows
cert_pivot_2 7 2 0 1
cert_heightProof 4
cert_coverFacet 0 806
cert_cover_5 0 0 0 1 4 7 290 806 1
cert_coverFacet 1 570
cert_cover_5 1 1 0 2 3 4 26 570 3
cert_coverFacet 2 154
cert_cover_2 2 2 0 3 6 26 154 3
cert_coverFacet 3 242
cert_cover_5 3 2 0 3 4 5 50 242 3
cert_coverFacet 4 418
cert_cover_2 4 4 0 6 7 162 418 3
cert_coverFacet 5 628
cert_cover_5 5 3 1 3 4 5 100 628 1
cert_coverFacet 6 228
cert_cover_2 6 4 1 5 6 100 228 3
cert_coverFacet 7 216
cert_cover_2 7 3 2 5 6 88 216 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0627

end
end BundlePart16

section BundlePart17
/- Source: ProjectionCertificates/R_m14e10q1_0628.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0628

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [707, 301, 229, 901, 625, 817, 654, 602, 154, 242, 796, 172, 184, 312, 37, 133, 261, 561, 97, 289, 193, 577, 641, 769, 26, 138, 522, 82, 146, 194, 578, 642, 44, 140, 268, 524, 164, 644, 772, 56, 152, 280, 536, 168, 296, 112, 176, 304, 592, 784, 224]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_707, vertices_301, vertices_229, vertices_901, vertices_625, vertices_817, vertices_654, vertices_602, vertices_154, vertices_242, vertices_796, vertices_172, vertices_184, vertices_312] (by decide +kernel)
  polygons := literalFinset [vertices_37, vertices_133, vertices_261, vertices_561, vertices_97, vertices_289, vertices_193, vertices_577, vertices_641, vertices_769, vertices_26, vertices_138, vertices_522, vertices_82, vertices_146, vertices_194, vertices_578, vertices_642, vertices_44, vertices_140, vertices_268, vertices_524, vertices_164, vertices_644, vertices_772, vertices_56, vertices_152, vertices_280, vertices_536, vertices_168, vertices_296, vertices_112, vertices_176, vertices_304, vertices_592, vertices_784, vertices_224] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_707), (false, vertices_301), (false, vertices_229), (false, vertices_901), (false, vertices_625), (false, vertices_817), (true, vertices_26), (true, vertices_138), (true, vertices_522), (true, vertices_82), (true, vertices_146), (true, vertices_140), (true, vertices_524), (true, vertices_56), (true, vertices_152), (true, vertices_280), (true, vertices_536), (true, vertices_168), (true, vertices_176)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 13 15 19 20 23 24 25 26 27
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_707) then 14 else
  if p.val = (false, vertices_301) then 16 else
  if p.val = (false, vertices_229) then 17 else
  if p.val = (false, vertices_901) then 18 else
  if p.val = (false, vertices_625) then 21 else
  if p.val = (false, vertices_817) then 22 else
  if p.val = (true, vertices_26) then 0 else
  if p.val = (true, vertices_138) then 1 else
  if p.val = (true, vertices_522) then 2 else
  if p.val = (true, vertices_82) then 3 else
  if p.val = (true, vertices_146) then 4 else
  if p.val = (true, vertices_140) then 5 else
  if p.val = (true, vertices_524) then 6 else
  if p.val = (true, vertices_56) then 7 else
  if p.val = (true, vertices_152) then 8 else
  if p.val = (true, vertices_280) then 9 else
  if p.val = (true, vertices_536) then 10 else
  if p.val = (true, vertices_168) then 11 else
  if p.val = (true, vertices_176) then 12 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_26), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_138), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_522), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_82), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_146), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_140), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_524), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_56), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_152), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_280), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_536), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_168), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_176), by decide +kernel⟩
  | 13 => Sum.inl 0
  | 14 => Sum.inr ⟨(false, vertices_707), by decide +kernel⟩
  | 15 => Sum.inl 1
  | 16 => Sum.inr ⟨(false, vertices_301), by decide +kernel⟩
  | 17 => Sum.inr ⟨(false, vertices_229), by decide +kernel⟩
  | 18 => Sum.inr ⟨(false, vertices_901), by decide +kernel⟩
  | 19 => Sum.inl 2
  | 20 => Sum.inl 3
  | 21 => Sum.inr ⟨(false, vertices_625), by decide +kernel⟩
  | 22 => Sum.inr ⟨(false, vertices_817), by decide +kernel⟩
  | 23 => Sum.inl 4
  | 24 => Sum.inl 5
  | 25 => Sum.inl 6
  | 26 => Sum.inl 7
  | 27 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 3 4 5 6 242 82 2
cert_row_4 1 0 1 2 6 8 654 138 1
cert_row_4 2 0 2 3 5 8 602 26 3
cert_row_4 3 1 2 3 7 8 796 268 2
cert_rows
cert_pivot_2 4 6 0 1
cert_heightProof 4
cert_coverFacet 0 654
cert_cover_5 0 1 0 1 2 6 138 654 1
cert_coverFacet 1 602
cert_cover_5 1 2 0 2 3 5 26 602 3
cert_coverFacet 2 154
cert_cover_2 2 2 0 3 6 26 154 3
cert_coverFacet 3 242
cert_cover_5 3 0 0 3 4 5 82 242 2
cert_coverFacet 4 796
cert_cover_5 4 3 1 2 3 7 268 796 2
cert_coverFacet 5 172
cert_cover_2 5 2 1 4 6 44 172 3
cert_coverFacet 6 184
cert_cover_2 6 3 2 4 6 56 184 3
cert_coverFacet 7 312
cert_cover_2 7 3 2 4 7 56 312 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0628

end
end BundlePart17

section BundlePart18
/- Source: ProjectionCertificates/R_m14e10q1_0629.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0629

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [395, 613, 361, 681, 721, 449, 302, 558, 598, 278, 666, 402, 468, 356, 41, 137, 265, 97, 545, 193, 321, 577, 385, 641, 46, 22, 262, 518, 138, 266, 522, 146, 274, 530, 386, 84, 276, 100, 292, 548, 324, 580, 296, 552, 648, 208, 592, 400, 656, 352, 448]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_395, vertices_613, vertices_361, vertices_681, vertices_721, vertices_449, vertices_302, vertices_558, vertices_598, vertices_278, vertices_666, vertices_402, vertices_468, vertices_356] (by decide +kernel)
  polygons := literalFinset [vertices_41, vertices_137, vertices_265, vertices_97, vertices_545, vertices_193, vertices_321, vertices_577, vertices_385, vertices_641, vertices_46, vertices_22, vertices_262, vertices_518, vertices_138, vertices_266, vertices_522, vertices_146, vertices_274, vertices_530, vertices_386, vertices_84, vertices_276, vertices_100, vertices_292, vertices_548, vertices_324, vertices_580, vertices_296, vertices_552, vertices_648, vertices_208, vertices_592, vertices_400, vertices_656, vertices_352, vertices_448] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_395), (false, vertices_613), (false, vertices_361), (false, vertices_681), (false, vertices_721), (false, vertices_449), (true, vertices_46), (true, vertices_22), (true, vertices_262), (true, vertices_518), (true, vertices_522), (true, vertices_146), (true, vertices_274), (true, vertices_530), (true, vertices_84), (true, vertices_276), (true, vertices_292), (true, vertices_324), (true, vertices_400)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 13 16 18 21 23 24 25 26 27
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_395) then 14 else
  if p.val = (false, vertices_613) then 17 else
  if p.val = (false, vertices_361) then 19 else
  if p.val = (false, vertices_681) then 20 else
  if p.val = (false, vertices_721) then 22 else
  if p.val = (false, vertices_449) then 0 else
  if p.val = (true, vertices_46) then 15 else
  if p.val = (true, vertices_22) then 1 else
  if p.val = (true, vertices_262) then 2 else
  if p.val = (true, vertices_518) then 3 else
  if p.val = (true, vertices_522) then 4 else
  if p.val = (true, vertices_146) then 5 else
  if p.val = (true, vertices_274) then 6 else
  if p.val = (true, vertices_530) then 7 else
  if p.val = (true, vertices_84) then 8 else
  if p.val = (true, vertices_276) then 9 else
  if p.val = (true, vertices_292) then 10 else
  if p.val = (true, vertices_324) then 11 else
  if p.val = (true, vertices_400) then 12 else
  0
cert_priority
cert_nodeAtPriority_37 449 22 262 518 522 146 274 530 84 276 292 324 400 395 46 613 361 681 721
cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 1 2 4 46
cert_row_4 1 0 2 3 6 8 666 138 2
cert_row_4 2 0 1 3 5 8 598 22 3
cert_row_4 3 1 3 5 6 7 468 84 3
cert_rows
cert_pivot_2 4 2 0 1
cert_heightProof 4
cert_coverFacet 0 302
cert_cover_5 0 0 0 1 2 7 46 302 3
cert_coverFacet 1 558
cert_cover_5 1 0 0 1 2 8 46 558 3
cert_coverFacet 2 598
cert_cover_5 2 2 0 1 3 5 22 598 3
cert_coverFacet 3 278
cert_cover_2 3 1 0 3 7 22 278 3
cert_coverFacet 4 666
cert_cover_5 4 1 0 2 3 6 138 666 2
cert_coverFacet 5 402
cert_cover_2 5 3 0 6 7 146 402 3
cert_coverFacet 6 468
cert_cover_5 6 3 1 3 5 6 84 468 3
cert_coverFacet 7 356
cert_cover_2 7 4 1 5 7 100 356 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0629

end
end BundlePart18

section BundlePart19
/- Source: ProjectionCertificates/R_m14e10q1_0630.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0630

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [787, 397, 213, 837, 625, 401, 782, 570, 426, 306, 236, 620, 240, 432, 69, 133, 261, 81, 145, 273, 529, 577, 385, 769, 42, 266, 522, 50, 274, 530, 290, 770, 108, 140, 268, 524, 196, 580, 772, 168, 552, 392, 112, 176, 304, 560, 208, 400, 224, 608, 416]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_787, vertices_397, vertices_213, vertices_837, vertices_625, vertices_401, vertices_782, vertices_570, vertices_426, vertices_306, vertices_236, vertices_620, vertices_240, vertices_432] (by decide +kernel)
  polygons := literalFinset [vertices_69, vertices_133, vertices_261, vertices_81, vertices_145, vertices_273, vertices_529, vertices_577, vertices_385, vertices_769, vertices_42, vertices_266, vertices_522, vertices_50, vertices_274, vertices_530, vertices_290, vertices_770, vertices_108, vertices_140, vertices_268, vertices_524, vertices_196, vertices_580, vertices_772, vertices_168, vertices_552, vertices_392, vertices_112, vertices_176, vertices_304, vertices_560, vertices_208, vertices_400, vertices_224, vertices_608, vertices_416] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_787), (false, vertices_397), (false, vertices_213), (false, vertices_837), (false, vertices_625), (false, vertices_401), (true, vertices_42), (true, vertices_266), (true, vertices_522), (true, vertices_50), (true, vertices_290), (true, vertices_108), (true, vertices_524), (true, vertices_168), (true, vertices_552), (true, vertices_176), (true, vertices_304), (true, vertices_224), (true, vertices_416)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 13 18 15 21 23 24 25 26 27
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_787) then 14 else
  if p.val = (false, vertices_397) then 16 else
  if p.val = (false, vertices_213) then 19 else
  if p.val = (false, vertices_837) then 20 else
  if p.val = (false, vertices_625) then 22 else
  if p.val = (false, vertices_401) then 0 else
  if p.val = (true, vertices_42) then 1 else
  if p.val = (true, vertices_266) then 2 else
  if p.val = (true, vertices_522) then 3 else
  if p.val = (true, vertices_50) then 4 else
  if p.val = (true, vertices_290) then 5 else
  if p.val = (true, vertices_108) then 17 else
  if p.val = (true, vertices_524) then 6 else
  if p.val = (true, vertices_168) then 7 else
  if p.val = (true, vertices_552) then 8 else
  if p.val = (true, vertices_176) then 9 else
  if p.val = (true, vertices_304) then 10 else
  if p.val = (true, vertices_224) then 11 else
  if p.val = (true, vertices_416) then 12 else
  0
cert_priority
cert_nodeAtPriority_2 0 401 2 42 1 266 3 522 50 290 524 168 552 176 304 224 416 787 397 108 213 837 625
cert_priority_injective
cert_incidenceProof
cert_row_2 0 1 2 4 5 108
cert_row_4 1 0 1 2 7 8 782 266 1
cert_row_4 2 0 2 3 4 8 570 42 2
cert_row_4 3 0 2 4 6 7 426 42 3
cert_rows
cert_pivot_2 5 1 3 0
cert_heightProof 4
cert_coverFacet 0 782
cert_cover_5 0 1 0 1 2 7 266 782 1
cert_coverFacet 1 570
cert_cover_5 1 2 0 2 3 4 42 570 2
cert_coverFacet 2 426
cert_cover_5 2 3 0 2 4 6 42 426 3
cert_coverFacet 3 306
cert_cover_2 3 3 0 4 7 50 306 3
cert_coverFacet 4 236
cert_cover_5 4 0 1 2 4 6 108 236 3
cert_coverFacet 5 620
cert_cover_5 5 0 1 2 4 8 108 620 3
cert_coverFacet 6 240
cert_cover_2 6 4 3 5 6 112 240 3
cert_coverFacet 7 432
cert_cover_2 7 4 3 6 7 176 432 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0630

end
end BundlePart19

section BundlePart20
/- Source: ProjectionCertificates/R_m14e10q1_0631.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0631

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [115, 339, 661, 409, 361, 681, 561, 406, 534, 838, 618, 562, 908, 840, 83, 41, 137, 265, 49, 145, 273, 529, 97, 545, 321, 641, 22, 262, 518, 50, 274, 530, 98, 546, 322, 578, 148, 532, 388, 644, 772, 104, 552, 328, 584, 392, 648, 776, 560, 400, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_115, vertices_339, vertices_661, vertices_409, vertices_361, vertices_681, vertices_561, vertices_406, vertices_534, vertices_838, vertices_618, vertices_562, vertices_908, vertices_840] (by decide +kernel)
  polygons := literalFinset [vertices_83, vertices_41, vertices_137, vertices_265, vertices_49, vertices_145, vertices_273, vertices_529, vertices_97, vertices_545, vertices_321, vertices_641, vertices_22, vertices_262, vertices_518, vertices_50, vertices_274, vertices_530, vertices_98, vertices_546, vertices_322, vertices_578, vertices_148, vertices_532, vertices_388, vertices_644, vertices_772, vertices_104, vertices_552, vertices_328, vertices_584, vertices_392, vertices_648, vertices_776, vertices_560, vertices_400, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_115), (false, vertices_339), (false, vertices_661), (false, vertices_409), (false, vertices_361), (false, vertices_681), (false, vertices_561), (true, vertices_22), (true, vertices_262), (true, vertices_518), (true, vertices_530), (true, vertices_546), (true, vertices_578), (true, vertices_388), (true, vertices_772), (true, vertices_584), (true, vertices_776), (true, vertices_832)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 12 15 17 21 22 23 24 25 26
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_115) then 13 else
  if p.val = (false, vertices_339) then 14 else
  if p.val = (false, vertices_661) then 16 else
  if p.val = (false, vertices_409) then 18 else
  if p.val = (false, vertices_361) then 19 else
  if p.val = (false, vertices_681) then 20 else
  if p.val = (false, vertices_561) then 0 else
  if p.val = (true, vertices_22) then 1 else
  if p.val = (true, vertices_262) then 2 else
  if p.val = (true, vertices_518) then 3 else
  if p.val = (true, vertices_530) then 4 else
  if p.val = (true, vertices_546) then 5 else
  if p.val = (true, vertices_578) then 6 else
  if p.val = (true, vertices_388) then 7 else
  if p.val = (true, vertices_772) then 8 else
  if p.val = (true, vertices_584) then 9 else
  if p.val = (true, vertices_776) then 10 else
  if p.val = (true, vertices_832) then 11 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_561), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_22), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_262), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_518), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_530), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_546), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_578), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_388), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_772), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_584), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_776), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_832), by decide +kernel⟩
  | 12 => Sum.inl 0
  | 13 => Sum.inr ⟨(false, vertices_115), by decide +kernel⟩
  | 14 => Sum.inr ⟨(false, vertices_339), by decide +kernel⟩
  | 15 => Sum.inl 1
  | 16 => Sum.inr ⟨(false, vertices_661), by decide +kernel⟩
  | 17 => Sum.inl 2
  | 18 => Sum.inr ⟨(false, vertices_409), by decide +kernel⟩
  | 19 => Sum.inr ⟨(false, vertices_361), by decide +kernel⟩
  | 20 => Sum.inr ⟨(false, vertices_681), by decide +kernel⟩
  | 21 => Sum.inl 3
  | 22 => Sum.inl 4
  | 23 => Sum.inl 5
  | 24 => Sum.inl 6
  | 25 => Sum.inl 7
  | 26 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 3 6 7 406 22 3
cert_row_4 1 0 2 4 5 8 618 98 1
cert_row_4 2 0 1 5 7 8 838 262 2
cert_row_4 3 1 2 6 7 8 908 388 1
cert_rows
cert_pivot_2 3 4 0 1
cert_heightProof 4
cert_coverFacet 0 406
cert_cover_5 0 0 0 1 3 6 22 406 3
cert_coverFacet 1 534
cert_cover_2 1 1 0 3 8 22 534 3
cert_coverFacet 2 838
cert_cover_5 2 2 0 1 5 7 262 838 2
cert_coverFacet 3 618
cert_cover_5 3 1 0 2 4 5 98 618 1
cert_coverFacet 4 562
cert_cover_2 4 3 0 4 8 50 562 3
cert_coverFacet 5 908
cert_cover_5 5 3 1 2 6 7 388 908 1
cert_coverFacet 6 840
cert_cover_2 6 5 2 7 8 328 840 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0631

end
end BundlePart20

section BundlePart21
/- Source: ProjectionCertificates/R_m14e10q1_0639.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0639

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [779, 205, 525, 661, 345, 241, 785, 558, 362, 370, 690, 786, 108, 740, 13, 133, 517, 73, 265, 521, 81, 145, 273, 529, 193, 769, 42, 266, 522, 50, 274, 530, 354, 546, 770, 44, 76, 524, 100, 548, 196, 644, 104, 328, 112, 176, 336, 656, 784, 224, 672]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_779, vertices_205, vertices_525, vertices_661, vertices_345, vertices_241, vertices_785, vertices_558, vertices_362, vertices_370, vertices_690, vertices_786, vertices_108, vertices_740] (by decide +kernel)
  polygons := literalFinset [vertices_13, vertices_133, vertices_517, vertices_73, vertices_265, vertices_521, vertices_81, vertices_145, vertices_273, vertices_529, vertices_193, vertices_769, vertices_42, vertices_266, vertices_522, vertices_50, vertices_274, vertices_530, vertices_354, vertices_546, vertices_770, vertices_44, vertices_76, vertices_524, vertices_100, vertices_548, vertices_196, vertices_644, vertices_104, vertices_328, vertices_112, vertices_176, vertices_336, vertices_656, vertices_784, vertices_224, vertices_672] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_779), (false, vertices_205), (false, vertices_525), (false, vertices_661), (false, vertices_345), (false, vertices_241), (false, vertices_785), (true, vertices_42), (true, vertices_50), (true, vertices_274), (true, vertices_530), (true, vertices_354), (true, vertices_546), (true, vertices_44), (true, vertices_100), (true, vertices_548), (true, vertices_104), (true, vertices_672)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 12 15 18 20 22 23 24 25 26
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_779) then 13 else
  if p.val = (false, vertices_205) then 16 else
  if p.val = (false, vertices_525) then 0 else
  if p.val = (false, vertices_661) then 17 else
  if p.val = (false, vertices_345) then 19 else
  if p.val = (false, vertices_241) then 21 else
  if p.val = (false, vertices_785) then 1 else
  if p.val = (true, vertices_42) then 2 else
  if p.val = (true, vertices_50) then 3 else
  if p.val = (true, vertices_274) then 4 else
  if p.val = (true, vertices_530) then 5 else
  if p.val = (true, vertices_354) then 14 else
  if p.val = (true, vertices_546) then 6 else
  if p.val = (true, vertices_44) then 7 else
  if p.val = (true, vertices_100) then 8 else
  if p.val = (true, vertices_548) then 9 else
  if p.val = (true, vertices_104) then 10 else
  if p.val = (true, vertices_672) then 11 else
  0
cert_priority
cert_nodeAtPriority_67 0 525 1 785 42 50 274 530 546 44 100 548 104 672 779 354 205 661 345 241
cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 4 5 7 354
cert_row_4 1 0 1 2 4 8 558 42 1
cert_row_4 2 0 3 4 6 8 690 50 3
cert_row_4 3 1 4 5 6 8 740 100 3
cert_rows
cert_pivot_2 7 2 0 1
cert_heightProof 4
cert_coverFacet 0 558
cert_cover_5 0 1 0 1 2 4 42 558 1
cert_coverFacet 1 362
cert_cover_5 1 0 0 2 4 5 42 362 3
cert_coverFacet 2 370
cert_cover_5 2 0 0 3 4 5 50 370 3
cert_coverFacet 3 690
cert_cover_5 3 2 0 3 4 6 50 690 3
cert_coverFacet 4 786
cert_cover_2 4 3 0 7 8 274 786 3
cert_coverFacet 5 108
cert_cover_2 5 2 1 4 5 44 108 3
cert_coverFacet 6 740
cert_cover_5 6 3 1 4 5 6 100 740 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0639

end
end BundlePart21

section BundlePart22
/- Source: ProjectionCertificates/R_m14e10q1_0641.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0641

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [775, 205, 269, 661, 361, 961, 62, 270, 534, 298, 690, 866, 188, 744, 13, 133, 261, 517, 73, 265, 193, 321, 641, 769, 14, 22, 262, 518, 42, 266, 50, 530, 290, 546, 770, 60, 140, 268, 148, 532, 104, 168, 296, 200, 176, 656, 352, 608, 672, 704, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_775, vertices_205, vertices_269, vertices_661, vertices_361, vertices_961, vertices_62, vertices_270, vertices_534, vertices_298, vertices_690, vertices_866, vertices_188, vertices_744] (by decide +kernel)
  polygons := literalFinset [vertices_13, vertices_133, vertices_261, vertices_517, vertices_73, vertices_265, vertices_193, vertices_321, vertices_641, vertices_769, vertices_14, vertices_22, vertices_262, vertices_518, vertices_42, vertices_266, vertices_50, vertices_530, vertices_290, vertices_546, vertices_770, vertices_60, vertices_140, vertices_268, vertices_148, vertices_532, vertices_104, vertices_168, vertices_296, vertices_200, vertices_176, vertices_656, vertices_352, vertices_608, vertices_672, vertices_704, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_775), (false, vertices_205), (false, vertices_269), (false, vertices_661), (false, vertices_361), (false, vertices_961), (true, vertices_14), (true, vertices_22), (true, vertices_42), (true, vertices_266), (true, vertices_50), (true, vertices_530), (true, vertices_290), (true, vertices_546), (true, vertices_60), (true, vertices_168), (true, vertices_176), (true, vertices_608), (true, vertices_672)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 13 15 19 21 22 23 25 26 27
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_775) then 14 else
  if p.val = (false, vertices_205) then 16 else
  if p.val = (false, vertices_269) then 0 else
  if p.val = (false, vertices_661) then 17 else
  if p.val = (false, vertices_361) then 20 else
  if p.val = (false, vertices_961) then 24 else
  if p.val = (true, vertices_14) then 1 else
  if p.val = (true, vertices_22) then 2 else
  if p.val = (true, vertices_42) then 3 else
  if p.val = (true, vertices_266) then 4 else
  if p.val = (true, vertices_50) then 5 else
  if p.val = (true, vertices_530) then 6 else
  if p.val = (true, vertices_290) then 7 else
  if p.val = (true, vertices_546) then 8 else
  if p.val = (true, vertices_60) then 18 else
  if p.val = (true, vertices_168) then 9 else
  if p.val = (true, vertices_176) then 10 else
  if p.val = (true, vertices_608) then 11 else
  if p.val = (true, vertices_672) then 12 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_269), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_14), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_22), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_42), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_266), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_50), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_530), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_290), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_546), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_168), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_176), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_608), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_672), by decide +kernel⟩
  | 13 => Sum.inl 0
  | 14 => Sum.inr ⟨(false, vertices_775), by decide +kernel⟩
  | 15 => Sum.inl 1
  | 16 => Sum.inr ⟨(false, vertices_205), by decide +kernel⟩
  | 17 => Sum.inr ⟨(false, vertices_661), by decide +kernel⟩
  | 18 => Sum.inr ⟨(true, vertices_60), by decide +kernel⟩
  | 19 => Sum.inl 2
  | 20 => Sum.inr ⟨(false, vertices_361), by decide +kernel⟩
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
cert_row_2 0 1 2 3 4 60
cert_row_4 1 0 3 4 6 8 690 50 3
cert_row_4 2 0 4 5 7 8 866 290 2
cert_row_4 3 2 4 5 6 8 744 104 3
cert_rows
cert_pivot_2 1 3 0 2
cert_heightProof 4
cert_coverFacet 0 62
cert_cover_5 0 0 0 1 2 3 14 62 3
cert_coverFacet 1 270
cert_cover_2 1 1 0 2 7 14 270 3
cert_coverFacet 2 534
cert_cover_2 2 1 0 3 8 22 534 3
cert_coverFacet 3 298
cert_cover_2 3 2 0 4 7 42 298 3
cert_coverFacet 4 690
cert_cover_5 4 1 0 3 4 6 50 690 3
cert_coverFacet 5 866
cert_cover_5 5 2 0 4 5 7 290 866 2
cert_coverFacet 6 188
cert_cover_5 6 0 1 2 3 6 60 188 3
cert_coverFacet 7 744
cert_cover_5 7 3 2 4 5 6 104 744 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0641

end
end BundlePart22

section BundlePart23
/- Source: ProjectionCertificates/R_m14e10q1_0645.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0645

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [775, 557, 165, 453, 185, 201, 841, 182, 566, 390, 218, 594, 962, 632, 37, 133, 261, 517, 41, 73, 137, 521, 161, 193, 321, 769, 54, 134, 262, 518, 82, 146, 530, 194, 578, 386, 770, 164, 548, 388, 56, 88, 152, 552, 200, 584, 176, 560, 592, 448, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_775, vertices_557, vertices_165, vertices_453, vertices_185, vertices_201, vertices_841, vertices_182, vertices_566, vertices_390, vertices_218, vertices_594, vertices_962, vertices_632] (by decide +kernel)
  polygons := literalFinset [vertices_37, vertices_133, vertices_261, vertices_517, vertices_41, vertices_73, vertices_137, vertices_521, vertices_161, vertices_193, vertices_321, vertices_769, vertices_54, vertices_134, vertices_262, vertices_518, vertices_82, vertices_146, vertices_530, vertices_194, vertices_578, vertices_386, vertices_770, vertices_164, vertices_548, vertices_388, vertices_56, vertices_88, vertices_152, vertices_552, vertices_200, vertices_584, vertices_176, vertices_560, vertices_592, vertices_448, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_775), (false, vertices_557), (false, vertices_165), (false, vertices_453), (false, vertices_185), (false, vertices_201), (false, vertices_841), (true, vertices_54), (true, vertices_134), (true, vertices_82), (true, vertices_146), (true, vertices_530), (true, vertices_194), (true, vertices_578), (true, vertices_386), (true, vertices_88), (true, vertices_560), (true, vertices_592)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 12 15 18 21 22 23 24 25 26
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_775) then 13 else
  if p.val = (false, vertices_557) then 16 else
  if p.val = (false, vertices_165) then 0 else
  if p.val = (false, vertices_453) then 17 else
  if p.val = (false, vertices_185) then 19 else
  if p.val = (false, vertices_201) then 1 else
  if p.val = (false, vertices_841) then 20 else
  if p.val = (true, vertices_54) then 14 else
  if p.val = (true, vertices_134) then 2 else
  if p.val = (true, vertices_82) then 3 else
  if p.val = (true, vertices_146) then 4 else
  if p.val = (true, vertices_530) then 5 else
  if p.val = (true, vertices_194) then 6 else
  if p.val = (true, vertices_578) then 7 else
  if p.val = (true, vertices_386) then 8 else
  if p.val = (true, vertices_88) then 9 else
  if p.val = (true, vertices_560) then 10 else
  if p.val = (true, vertices_592) then 11 else
  0
cert_priority
cert_nodeAtPriority_10 0 165 1 201 134 82 146 530 194 578 386 88 560 592 775 54 557 453 185 841
cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 1 3 4 54
cert_row_4 1 0 5 6 7 8 962 194 3
cert_row_4 2 0 2 3 5 6 218 82 1
cert_row_4 3 2 3 4 5 8 632 56 3
cert_rows
cert_pivot_2 1 7 0 2
cert_heightProof 4
cert_coverFacet 0 182
cert_cover_5 0 0 0 1 3 6 54 182 3
cert_coverFacet 1 566
cert_cover_5 1 0 0 1 3 8 54 566 3
cert_coverFacet 2 390
cert_cover_2 2 1 0 6 7 134 390 3
cert_coverFacet 3 218
cert_cover_5 3 2 0 2 3 5 82 218 1
cert_coverFacet 4 594
cert_cover_2 4 3 0 5 8 82 594 3
cert_coverFacet 5 962
cert_cover_5 5 1 0 5 6 7 194 962 3
cert_coverFacet 6 632
cert_cover_5 6 3 2 3 4 5 56 632 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0645

end
end BundlePart23

section BundlePart24
/- Source: ProjectionCertificates/R_m14e10q1_0648.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0648

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [647, 171, 787, 291, 121, 665, 369, 838, 390, 418, 716, 484, 856, 232, 35, 131, 259, 515, 25, 41, 137, 113, 273, 529, 289, 641, 134, 262, 518, 162, 290, 386, 770, 196, 324, 580, 388, 644, 88, 536, 104, 168, 200, 584, 648, 336, 784, 224, 352, 416, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_647, vertices_171, vertices_787, vertices_291, vertices_121, vertices_665, vertices_369, vertices_838, vertices_390, vertices_418, vertices_716, vertices_484, vertices_856, vertices_232] (by decide +kernel)
  polygons := literalFinset [vertices_35, vertices_131, vertices_259, vertices_515, vertices_25, vertices_41, vertices_137, vertices_113, vertices_273, vertices_529, vertices_289, vertices_641, vertices_134, vertices_262, vertices_518, vertices_162, vertices_290, vertices_386, vertices_770, vertices_196, vertices_324, vertices_580, vertices_388, vertices_644, vertices_88, vertices_536, vertices_104, vertices_168, vertices_200, vertices_584, vertices_648, vertices_336, vertices_784, vertices_224, vertices_352, vertices_416, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_647), (false, vertices_171), (false, vertices_787), (false, vertices_291), (false, vertices_121), (false, vertices_665), (false, vertices_369), (true, vertices_262), (true, vertices_386), (true, vertices_196), (true, vertices_324), (true, vertices_580), (true, vertices_388), (true, vertices_200), (true, vertices_584), (true, vertices_224), (true, vertices_416), (true, vertices_832)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 12 16 17 19 22 23 24 25 26
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_647) then 13 else
  if p.val = (false, vertices_171) then 14 else
  if p.val = (false, vertices_787) then 15 else
  if p.val = (false, vertices_291) then 0 else
  if p.val = (false, vertices_121) then 20 else
  if p.val = (false, vertices_665) then 18 else
  if p.val = (false, vertices_369) then 21 else
  if p.val = (true, vertices_262) then 1 else
  if p.val = (true, vertices_386) then 2 else
  if p.val = (true, vertices_196) then 3 else
  if p.val = (true, vertices_324) then 4 else
  if p.val = (true, vertices_580) then 5 else
  if p.val = (true, vertices_388) then 6 else
  if p.val = (true, vertices_200) then 7 else
  if p.val = (true, vertices_584) then 8 else
  if p.val = (true, vertices_224) then 9 else
  if p.val = (true, vertices_416) then 10 else
  if p.val = (true, vertices_832) then 11 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_291), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_262), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_386), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_196), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_324), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_580), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_388), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_200), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_584), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_224), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_416), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_832), by decide +kernel⟩
  | 12 => Sum.inl 0
  | 13 => Sum.inr ⟨(false, vertices_647), by decide +kernel⟩
  | 14 => Sum.inr ⟨(false, vertices_171), by decide +kernel⟩
  | 15 => Sum.inr ⟨(false, vertices_787), by decide +kernel⟩
  | 16 => Sum.inl 1
  | 17 => Sum.inl 2
  | 18 => Sum.inr ⟨(false, vertices_665), by decide +kernel⟩
  | 19 => Sum.inl 3
  | 20 => Sum.inr ⟨(false, vertices_121), by decide +kernel⟩
  | 21 => Sum.inr ⟨(false, vertices_369), by decide +kernel⟩
  | 22 => Sum.inl 4
  | 23 => Sum.inl 5
  | 24 => Sum.inl 6
  | 25 => Sum.inl 7
  | 26 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 5 7 8 838 262 2
cert_row_4 1 1 4 5 6 7 484 196 1
cert_row_4 2 1 2 5 6 8 716 196 1
cert_row_4 3 2 3 5 7 8 856 88 3
cert_rows
cert_pivot_2 0 4 1 2
cert_heightProof 4
cert_coverFacet 0 838
cert_cover_5 0 0 0 1 5 7 262 838 2
cert_coverFacet 1 390
cert_cover_2 1 1 0 6 7 134 390 3
cert_coverFacet 2 418
cert_cover_2 2 4 0 6 7 162 418 3
cert_coverFacet 3 716
cert_cover_5 3 2 1 2 5 6 196 716 1
cert_coverFacet 4 484
cert_cover_5 4 1 1 4 5 6 196 484 1
cert_coverFacet 5 856
cert_cover_5 5 3 2 3 5 7 88 856 3
cert_coverFacet 6 232
cert_cover_2 6 4 2 5 6 104 232 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0648

end
end BundlePart24

section BundlePart25
/- Source: ProjectionCertificates/R_m14e10q1_0650.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0650

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [707, 405, 229, 805, 617, 897, 790, 186, 602, 234, 402, 898, 572, 180, 37, 133, 261, 97, 545, 193, 577, 385, 641, 769, 26, 170, 74, 146, 274, 530, 194, 578, 386, 642, 770, 52, 148, 276, 532, 164, 548, 772, 56, 536, 104, 552, 584, 176, 400, 224, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_707, vertices_405, vertices_229, vertices_805, vertices_617, vertices_897, vertices_790, vertices_186, vertices_602, vertices_234, vertices_402, vertices_898, vertices_572, vertices_180] (by decide +kernel)
  polygons := literalFinset [vertices_37, vertices_133, vertices_261, vertices_97, vertices_545, vertices_193, vertices_577, vertices_385, vertices_641, vertices_769, vertices_26, vertices_170, vertices_74, vertices_146, vertices_274, vertices_530, vertices_194, vertices_578, vertices_386, vertices_642, vertices_770, vertices_52, vertices_148, vertices_276, vertices_532, vertices_164, vertices_548, vertices_772, vertices_56, vertices_536, vertices_104, vertices_552, vertices_584, vertices_176, vertices_400, vertices_224, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_707), (false, vertices_405), (false, vertices_229), (false, vertices_805), (false, vertices_617), (false, vertices_897), (true, vertices_26), (true, vertices_170), (true, vertices_74), (true, vertices_146), (true, vertices_274), (true, vertices_530), (true, vertices_386), (true, vertices_770), (true, vertices_52), (true, vertices_532), (true, vertices_56), (true, vertices_536), (true, vertices_176)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 13 16 20 22 23 24 25 26 27
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_707) then 14 else
  if p.val = (false, vertices_405) then 17 else
  if p.val = (false, vertices_229) then 18 else
  if p.val = (false, vertices_805) then 19 else
  if p.val = (false, vertices_617) then 21 else
  if p.val = (false, vertices_897) then 0 else
  if p.val = (true, vertices_26) then 1 else
  if p.val = (true, vertices_170) then 15 else
  if p.val = (true, vertices_74) then 2 else
  if p.val = (true, vertices_146) then 3 else
  if p.val = (true, vertices_274) then 4 else
  if p.val = (true, vertices_530) then 5 else
  if p.val = (true, vertices_386) then 6 else
  if p.val = (true, vertices_770) then 7 else
  if p.val = (true, vertices_52) then 8 else
  if p.val = (true, vertices_532) then 9 else
  if p.val = (true, vertices_56) then 10 else
  if p.val = (true, vertices_536) then 11 else
  if p.val = (true, vertices_176) then 12 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_897), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_26), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_74), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_146), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_274), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_530), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_386), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_770), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_52), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_532), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_56), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_536), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_176), by decide +kernel⟩
  | 13 => Sum.inl 0
  | 14 => Sum.inr ⟨(false, vertices_707), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_170), by decide +kernel⟩
  | 16 => Sum.inl 1
  | 17 => Sum.inr ⟨(false, vertices_405), by decide +kernel⟩
  | 18 => Sum.inr ⟨(false, vertices_229), by decide +kernel⟩
  | 19 => Sum.inr ⟨(false, vertices_805), by decide +kernel⟩
  | 20 => Sum.inl 2
  | 21 => Sum.inr ⟨(false, vertices_617), by decide +kernel⟩
  | 22 => Sum.inl 3
  | 23 => Sum.inl 4
  | 24 => Sum.inl 5
  | 25 => Sum.inl 6
  | 26 => Sum.inl 7
  | 27 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 2 4 6 170
cert_row_4 1 0 1 3 7 8 790 274 1
cert_row_4 2 0 2 3 5 8 602 26 3
cert_row_4 3 1 2 3 4 8 572 52 1
cert_rows
cert_pivot_2 6 7 0 1
cert_heightProof 4
cert_coverFacet 0 790
cert_cover_5 0 1 0 1 3 7 274 790 1
cert_coverFacet 1 186
cert_cover_5 1 0 0 2 3 4 26 186 3
cert_coverFacet 2 602
cert_cover_5 2 2 0 2 3 5 26 602 3
cert_coverFacet 3 234
cert_cover_5 3 0 0 2 4 5 170 234 3
cert_coverFacet 4 402
cert_cover_2 4 3 0 6 7 146 402 3
cert_coverFacet 5 898
cert_cover_2 5 6 0 7 8 386 898 3
cert_coverFacet 6 572
cert_cover_5 6 3 1 2 3 4 52 572 1
cert_coverFacet 7 180
cert_cover_2 7 3 1 4 6 52 180 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0650

end
end BundlePart25

section BundlePart26
/- Source: ProjectionCertificates/R_m14e10q1_0652.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0652

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [395, 709, 345, 665, 625, 449, 654, 614, 422, 778, 818, 484, 792, 368, 25, 137, 265, 81, 529, 193, 321, 577, 385, 641, 38, 134, 518, 138, 266, 522, 290, 546, 386, 770, 100, 420, 196, 580, 644, 280, 536, 648, 776, 112, 304, 560, 336, 784, 352, 608, 448]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_395, vertices_709, vertices_345, vertices_665, vertices_625, vertices_449, vertices_654, vertices_614, vertices_422, vertices_778, vertices_818, vertices_484, vertices_792, vertices_368] (by decide +kernel)
  polygons := literalFinset [vertices_25, vertices_137, vertices_265, vertices_81, vertices_529, vertices_193, vertices_321, vertices_577, vertices_385, vertices_641, vertices_38, vertices_134, vertices_518, vertices_138, vertices_266, vertices_522, vertices_290, vertices_546, vertices_386, vertices_770, vertices_100, vertices_420, vertices_196, vertices_580, vertices_644, vertices_280, vertices_536, vertices_648, vertices_776, vertices_112, vertices_304, vertices_560, vertices_336, vertices_784, vertices_352, vertices_608, vertices_448] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_395), (false, vertices_709), (false, vertices_345), (false, vertices_665), (false, vertices_625), (false, vertices_449), (true, vertices_38), (true, vertices_134), (true, vertices_518), (true, vertices_522), (true, vertices_290), (true, vertices_546), (true, vertices_770), (true, vertices_100), (true, vertices_420), (true, vertices_776), (true, vertices_304), (true, vertices_784), (true, vertices_352)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 13 15 18 21 23 24 25 26 27
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_395) then 14 else
  if p.val = (false, vertices_709) then 16 else
  if p.val = (false, vertices_345) then 19 else
  if p.val = (false, vertices_665) then 20 else
  if p.val = (false, vertices_625) then 22 else
  if p.val = (false, vertices_449) then 0 else
  if p.val = (true, vertices_38) then 1 else
  if p.val = (true, vertices_134) then 2 else
  if p.val = (true, vertices_518) then 3 else
  if p.val = (true, vertices_522) then 4 else
  if p.val = (true, vertices_290) then 5 else
  if p.val = (true, vertices_546) then 6 else
  if p.val = (true, vertices_770) then 7 else
  if p.val = (true, vertices_100) then 8 else
  if p.val = (true, vertices_420) then 17 else
  if p.val = (true, vertices_776) then 9 else
  if p.val = (true, vertices_304) then 10 else
  if p.val = (true, vertices_784) then 11 else
  if p.val = (true, vertices_352) then 12 else
  0
cert_priority
cert_nodeAtPriority_2 0 449 1 38 2 134 3 518 522 290 546 770 100 776 304 784 352 395 709 420 345 665 625
cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 2 6 8 654 134 2
cert_row_2 1 1 4 6 7 420
cert_row_4 2 0 1 4 5 8 614 38 3
cert_row_4 3 0 3 4 7 8 818 290 1
cert_rows
cert_pivot_2 2 6 1 0
cert_heightProof 4
cert_coverFacet 0 654
cert_cover_5 0 0 0 1 2 6 134 654 2
cert_coverFacet 1 614
cert_cover_5 1 2 0 1 4 5 38 614 3
cert_coverFacet 2 422
cert_cover_5 2 1 0 1 4 6 38 422 3
cert_coverFacet 3 778
cert_cover_2 3 2 0 7 8 266 778 3
cert_coverFacet 4 818
cert_cover_5 4 3 0 3 4 7 290 818 1
cert_coverFacet 5 484
cert_cover_5 5 1 1 4 5 6 100 484 3
cert_coverFacet 6 792
cert_cover_2 6 3 2 7 8 280 792 3
cert_coverFacet 7 368
cert_cover_2 7 4 3 5 7 112 368 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0652

end
end BundlePart26

section BundlePart27
/- Source: ProjectionCertificates/R_m14e10q1_0654.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0654

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [803, 213, 421, 837, 617, 225, 790, 570, 218, 234, 402, 418, 604, 404, 69, 133, 261, 97, 161, 289, 545, 193, 577, 769, 26, 42, 202, 146, 274, 530, 162, 290, 546, 386, 770, 84, 148, 276, 532, 580, 388, 772, 88, 536, 104, 552, 584, 208, 400, 224, 416]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_803, vertices_213, vertices_421, vertices_837, vertices_617, vertices_225, vertices_790, vertices_570, vertices_218, vertices_234, vertices_402, vertices_418, vertices_604, vertices_404] (by decide +kernel)
  polygons := literalFinset [vertices_69, vertices_133, vertices_261, vertices_97, vertices_161, vertices_289, vertices_545, vertices_193, vertices_577, vertices_769, vertices_26, vertices_42, vertices_202, vertices_146, vertices_274, vertices_530, vertices_162, vertices_290, vertices_546, vertices_386, vertices_770, vertices_84, vertices_148, vertices_276, vertices_532, vertices_580, vertices_388, vertices_772, vertices_88, vertices_536, vertices_104, vertices_552, vertices_584, vertices_208, vertices_400, vertices_224, vertices_416] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_803), (false, vertices_213), (false, vertices_421), (false, vertices_837), (false, vertices_617), (false, vertices_225), (true, vertices_26), (true, vertices_42), (true, vertices_202), (true, vertices_146), (true, vertices_274), (true, vertices_530), (true, vertices_162), (true, vertices_386), (true, vertices_276), (true, vertices_532), (true, vertices_88), (true, vertices_536), (true, vertices_400)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 13 16 20 22 23 24 25 26 27
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_803) then 14 else
  if p.val = (false, vertices_213) then 17 else
  if p.val = (false, vertices_421) then 18 else
  if p.val = (false, vertices_837) then 19 else
  if p.val = (false, vertices_617) then 21 else
  if p.val = (false, vertices_225) then 0 else
  if p.val = (true, vertices_26) then 1 else
  if p.val = (true, vertices_42) then 2 else
  if p.val = (true, vertices_202) then 15 else
  if p.val = (true, vertices_146) then 3 else
  if p.val = (true, vertices_274) then 4 else
  if p.val = (true, vertices_530) then 5 else
  if p.val = (true, vertices_162) then 6 else
  if p.val = (true, vertices_386) then 7 else
  if p.val = (true, vertices_276) then 8 else
  if p.val = (true, vertices_532) then 9 else
  if p.val = (true, vertices_88) then 10 else
  if p.val = (true, vertices_536) then 11 else
  if p.val = (true, vertices_400) then 12 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_225), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_26), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_42), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_146), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_274), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_530), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_162), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_386), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_276), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_532), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_88), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_536), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_400), by decide +kernel⟩
  | 13 => Sum.inl 0
  | 14 => Sum.inr ⟨(false, vertices_803), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_202), by decide +kernel⟩
  | 16 => Sum.inl 1
  | 17 => Sum.inr ⟨(false, vertices_213), by decide +kernel⟩
  | 18 => Sum.inr ⟨(false, vertices_421), by decide +kernel⟩
  | 19 => Sum.inr ⟨(false, vertices_837), by decide +kernel⟩
  | 20 => Sum.inl 2
  | 21 => Sum.inr ⟨(false, vertices_617), by decide +kernel⟩
  | 22 => Sum.inl 3
  | 23 => Sum.inl 4
  | 24 => Sum.inl 5
  | 25 => Sum.inl 6
  | 26 => Sum.inl 7
  | 27 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 2 5 6 202
cert_row_4 1 0 1 3 7 8 790 274 1
cert_row_4 2 0 2 3 4 8 570 26 3
cert_row_4 3 1 2 3 5 8 604 84 1
cert_rows
cert_pivot_2 6 7 0 1
cert_heightProof 4
cert_coverFacet 0 790
cert_cover_5 0 1 0 1 3 7 274 790 1
cert_coverFacet 1 570
cert_cover_5 1 2 0 2 3 4 26 570 3
cert_coverFacet 2 218
cert_cover_5 2 0 0 2 3 5 26 218 3
cert_coverFacet 3 234
cert_cover_5 3 0 0 2 4 5 42 234 3
cert_coverFacet 4 402
cert_cover_2 4 3 0 6 7 146 402 3
cert_coverFacet 5 418
cert_cover_2 5 4 0 6 7 162 418 3
cert_coverFacet 6 604
cert_cover_5 6 3 1 2 3 5 84 604 1
cert_coverFacet 7 404
cert_cover_2 7 3 1 6 7 148 404 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0654

end
end BundlePart27

section BundlePart28
/- Source: ProjectionCertificates/R_m14e10q1_0656.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0656

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [659, 285, 173, 149, 905, 849, 214, 230, 682, 626, 300, 340, 868, 808, 13, 21, 133, 137, 265, 145, 273, 529, 641, 769, 198, 82, 146, 530, 98, 162, 546, 642, 44, 268, 84, 148, 276, 100, 164, 292, 324, 168, 296, 552, 648, 776, 336, 592, 608, 800, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_659, vertices_285, vertices_173, vertices_149, vertices_905, vertices_849, vertices_214, vertices_230, vertices_682, vertices_626, vertices_300, vertices_340, vertices_868, vertices_808] (by decide +kernel)
  polygons := literalFinset [vertices_13, vertices_21, vertices_133, vertices_137, vertices_265, vertices_145, vertices_273, vertices_529, vertices_641, vertices_769, vertices_198, vertices_82, vertices_146, vertices_530, vertices_98, vertices_162, vertices_546, vertices_642, vertices_44, vertices_268, vertices_84, vertices_148, vertices_276, vertices_100, vertices_164, vertices_292, vertices_324, vertices_168, vertices_296, vertices_552, vertices_648, vertices_776, vertices_336, vertices_592, vertices_608, vertices_800, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_659), (false, vertices_285), (false, vertices_173), (false, vertices_149), (false, vertices_905), (false, vertices_849), (true, vertices_198), (true, vertices_82), (true, vertices_98), (true, vertices_162), (true, vertices_546), (true, vertices_84), (true, vertices_100), (true, vertices_292), (true, vertices_324), (true, vertices_296), (true, vertices_552), (true, vertices_608), (true, vertices_800)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 13 16 19 21 23 24 25 26 27
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_659) then 14 else
  if p.val = (false, vertices_285) then 17 else
  if p.val = (false, vertices_173) then 18 else
  if p.val = (false, vertices_149) then 0 else
  if p.val = (false, vertices_905) then 20 else
  if p.val = (false, vertices_849) then 22 else
  if p.val = (true, vertices_198) then 15 else
  if p.val = (true, vertices_82) then 1 else
  if p.val = (true, vertices_98) then 2 else
  if p.val = (true, vertices_162) then 3 else
  if p.val = (true, vertices_546) then 4 else
  if p.val = (true, vertices_84) then 5 else
  if p.val = (true, vertices_100) then 6 else
  if p.val = (true, vertices_292) then 7 else
  if p.val = (true, vertices_324) then 8 else
  if p.val = (true, vertices_296) then 9 else
  if p.val = (true, vertices_552) then 10 else
  if p.val = (true, vertices_608) then 11 else
  if p.val = (true, vertices_800) then 12 else
  0
cert_priority
cert_nodeAtPriority_17 149 82 98 162 546 84 100 292 324 296 552 608 800 659 198 285 173 905 849
cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 2 4 6 8 682 162 1
cert_row_2 1 0 1 5 6 198
cert_row_4 2 0 3 4 5 8 626 82 2
cert_row_4 3 1 4 5 7 8 868 100 3
cert_rows
cert_pivot_2 2 6 0 1
cert_heightProof 4
cert_coverFacet 0 214
cert_cover_5 0 1 0 1 3 5 198 214 2
cert_coverFacet 1 230
cert_cover_5 1 1 0 1 4 5 198 230 2
cert_coverFacet 2 682
cert_cover_5 2 0 0 2 4 6 162 682 1
cert_coverFacet 3 626
cert_cover_5 3 2 0 3 4 5 82 626 2
cert_coverFacet 4 300
cert_cover_2 4 2 1 4 7 44 300 3
cert_coverFacet 5 340
cert_cover_2 5 3 1 5 7 84 340 3
cert_coverFacet 6 868
cert_cover_5 6 3 1 4 5 7 100 868 3
cert_coverFacet 7 808
cert_cover_2 7 4 2 7 8 296 808 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0656

end
end BundlePart28

section BundlePart29
/- Source: ProjectionCertificates/R_m14e10q1_0670.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0670

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [327, 779, 579, 61, 285, 229, 617, 914, 738, 450, 692, 404, 452, 824, 67, 259, 515, 29, 37, 69, 261, 41, 265, 521, 97, 577, 194, 322, 578, 386, 642, 770, 52, 148, 276, 164, 196, 324, 388, 56, 280, 552, 776, 560, 400, 656, 784, 224, 608, 672, 448]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_327, vertices_779, vertices_579, vertices_61, vertices_285, vertices_229, vertices_617, vertices_914, vertices_738, vertices_450, vertices_692, vertices_404, vertices_452, vertices_824] (by decide +kernel)
  polygons := literalFinset [vertices_67, vertices_259, vertices_515, vertices_29, vertices_37, vertices_69, vertices_261, vertices_41, vertices_265, vertices_521, vertices_97, vertices_577, vertices_194, vertices_322, vertices_578, vertices_386, vertices_642, vertices_770, vertices_52, vertices_148, vertices_276, vertices_164, vertices_196, vertices_324, vertices_388, vertices_56, vertices_280, vertices_552, vertices_776, vertices_560, vertices_400, vertices_656, vertices_784, vertices_224, vertices_608, vertices_672, vertices_448] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_327), (false, vertices_779), (false, vertices_579), (false, vertices_61), (false, vertices_285), (false, vertices_229), (false, vertices_617), (true, vertices_194), (true, vertices_386), (true, vertices_642), (true, vertices_148), (true, vertices_388), (true, vertices_560), (true, vertices_400), (true, vertices_656), (true, vertices_784), (true, vertices_672), (true, vertices_448)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 12 15 19 21 22 23 24 25 26
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_327) then 13 else
  if p.val = (false, vertices_779) then 14 else
  if p.val = (false, vertices_579) then 0 else
  if p.val = (false, vertices_61) then 16 else
  if p.val = (false, vertices_285) then 17 else
  if p.val = (false, vertices_229) then 18 else
  if p.val = (false, vertices_617) then 20 else
  if p.val = (true, vertices_194) then 1 else
  if p.val = (true, vertices_386) then 2 else
  if p.val = (true, vertices_642) then 3 else
  if p.val = (true, vertices_148) then 4 else
  if p.val = (true, vertices_388) then 5 else
  if p.val = (true, vertices_560) then 6 else
  if p.val = (true, vertices_400) then 7 else
  if p.val = (true, vertices_656) then 8 else
  if p.val = (true, vertices_784) then 9 else
  if p.val = (true, vertices_672) then 10 else
  if p.val = (true, vertices_448) then 11 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_579), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_194), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_386), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_642), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_148), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_388), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_560), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_400), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_656), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_784), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_672), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_448), by decide +kernel⟩
  | 12 => Sum.inl 0
  | 13 => Sum.inr ⟨(false, vertices_327), by decide +kernel⟩
  | 14 => Sum.inr ⟨(false, vertices_779), by decide +kernel⟩
  | 15 => Sum.inl 1
  | 16 => Sum.inr ⟨(false, vertices_61), by decide +kernel⟩
  | 17 => Sum.inr ⟨(false, vertices_285), by decide +kernel⟩
  | 18 => Sum.inr ⟨(false, vertices_229), by decide +kernel⟩
  | 19 => Sum.inl 2
  | 20 => Sum.inr ⟨(false, vertices_617), by decide +kernel⟩
  | 21 => Sum.inl 3
  | 22 => Sum.inl 4
  | 23 => Sum.inl 5
  | 24 => Sum.inl 6
  | 25 => Sum.inl 7
  | 26 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 4 5 6 8 738 194 1
cert_row_4 1 0 3 6 7 8 914 386 1
cert_row_4 2 1 3 4 6 8 692 52 3
cert_row_4 3 2 3 4 7 8 824 56 3
cert_rows
cert_pivot_2 5 0 1 2
cert_heightProof 4
cert_coverFacet 0 914
cert_cover_5 0 1 0 3 6 7 386 914 1
cert_coverFacet 1 738
cert_cover_5 1 0 0 4 5 6 194 738 1
cert_coverFacet 2 450
cert_cover_2 2 5 0 6 7 194 450 3
cert_coverFacet 3 692
cert_cover_5 3 2 1 3 4 6 52 692 3
cert_coverFacet 4 404
cert_cover_2 4 3 1 6 7 148 404 3
cert_coverFacet 5 452
cert_cover_2 5 5 1 6 7 196 452 3
cert_coverFacet 6 824
cert_cover_5 6 3 2 3 4 7 56 824 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0670

end
end BundlePart29
-- Explicit facial frame witnesses.

-- Public target certificates; internal witness data stays private.
namespace Nonrational.TerminalVerification
open Papers.RationalityTen.ChirotopeDensity.FiniteProjection
open Nonrational.TerminalData
set_option maxRecDepth 100000
set_option maxHeartbeats 0

public theorem projection_0330 : Certifies 330 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0569.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0331 : Certifies 331 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0570.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0332 : Certifies 332 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0571.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0333 : Certifies 333 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0572.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0334 : Certifies 334 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0580.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0335 : Certifies 335 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0586.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0336 : Certifies 336 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0587.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0337 : Certifies 337 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0588.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0338 : Certifies 338 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0590.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0339 : Certifies 339 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0591.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0340 : Certifies 340 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0600.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0341 : Certifies 341 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0609.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0342 : Certifies 342 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0623.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0343 : Certifies 343 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0624.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0344 : Certifies 344 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0625.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0345 : Certifies 345 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0626.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0346 : Certifies 346 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0627.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0347 : Certifies 347 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0628.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0348 : Certifies 348 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0629.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0349 : Certifies 349 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0630.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0350 : Certifies 350 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0631.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0351 : Certifies 351 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0639.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0352 : Certifies 352 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0641.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0353 : Certifies 353 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0645.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0354 : Certifies 354 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0648.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0355 : Certifies 355 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0650.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0356 : Certifies 356 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0652.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0357 : Certifies 357 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0654.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0358 : Certifies 358 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0656.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0359 : Certifies 359 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0670.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem certified_B011 (j : Fin 30) :
    Certifies (330 + j.val) := by
  fin_cases j
  · exact projection_0330
  · exact projection_0331
  · exact projection_0332
  · exact projection_0333
  · exact projection_0334
  · exact projection_0335
  · exact projection_0336
  · exact projection_0337
  · exact projection_0338
  · exact projection_0339
  · exact projection_0340
  · exact projection_0341
  · exact projection_0342
  · exact projection_0343
  · exact projection_0344
  · exact projection_0345
  · exact projection_0346
  · exact projection_0347
  · exact projection_0348
  · exact projection_0349
  · exact projection_0350
  · exact projection_0351
  · exact projection_0352
  · exact projection_0353
  · exact projection_0354
  · exact projection_0355
  · exact projection_0356
  · exact projection_0357
  · exact projection_0358
  · exact projection_0359

end Nonrational.TerminalVerification
