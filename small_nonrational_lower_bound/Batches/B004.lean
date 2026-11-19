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
/- Source: ProjectionCertificates/P0_242.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_242

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [659, 405, 677, 837, 793, 614, 186, 538, 106, 842, 674, 236, 460, 408, 133, 261, 517, 145, 273, 529, 641, 769, 26, 42, 74, 522, 146, 530, 98, 162, 546, 578, 642, 204, 100, 164, 548, 324, 580, 388, 152, 280, 536, 104, 168, 328, 392, 776, 400, 672, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_659, vertices_405, vertices_677, vertices_837, vertices_793, vertices_614, vertices_186, vertices_538, vertices_106, vertices_842, vertices_674, vertices_236, vertices_460, vertices_408] (by decide +kernel)
  polygons := literalFinset [vertices_133, vertices_261, vertices_517, vertices_145, vertices_273, vertices_529, vertices_641, vertices_769, vertices_26, vertices_42, vertices_74, vertices_522, vertices_146, vertices_530, vertices_98, vertices_162, vertices_546, vertices_578, vertices_642, vertices_204, vertices_100, vertices_164, vertices_548, vertices_324, vertices_580, vertices_388, vertices_152, vertices_280, vertices_536, vertices_104, vertices_168, vertices_328, vertices_392, vertices_776, vertices_400, vertices_672, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_659), (false, vertices_405), (false, vertices_677), (false, vertices_837), (false, vertices_793), (true, vertices_26), (true, vertices_42), (true, vertices_74), (true, vertices_522), (true, vertices_98), (true, vertices_162), (true, vertices_546), (true, vertices_578), (true, vertices_204), (true, vertices_100), (true, vertices_152), (true, vertices_104), (true, vertices_168), (true, vertices_328), (true, vertices_392)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 14 19 16 23 24 25 26 27 28
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_659) then 15 else
  if p.val = (false, vertices_405) then 20 else
  if p.val = (false, vertices_677) then 21 else
  if p.val = (false, vertices_837) then 22 else
  if p.val = (false, vertices_793) then 17 else
  if p.val = (true, vertices_26) then 0 else
  if p.val = (true, vertices_42) then 1 else
  if p.val = (true, vertices_74) then 2 else
  if p.val = (true, vertices_522) then 3 else
  if p.val = (true, vertices_98) then 4 else
  if p.val = (true, vertices_162) then 5 else
  if p.val = (true, vertices_546) then 6 else
  if p.val = (true, vertices_578) then 7 else
  if p.val = (true, vertices_204) then 18 else
  if p.val = (true, vertices_100) then 8 else
  if p.val = (true, vertices_152) then 9 else
  if p.val = (true, vertices_104) then 10 else
  if p.val = (true, vertices_168) then 11 else
  if p.val = (true, vertices_328) then 12 else
  if p.val = (true, vertices_392) then 13 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_26), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_42), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_74), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_522), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_98), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_162), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_546), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_578), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_100), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_152), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_104), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_168), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_328), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_392), by decide +kernel⟩
  | 14 => Sum.inl 0
  | 15 => Sum.inr ⟨(false, vertices_659), by decide +kernel⟩
  | 16 => Sum.inl 2
  | 17 => Sum.inr ⟨(false, vertices_793), by decide +kernel⟩
  | 18 => Sum.inr ⟨(true, vertices_204), by decide +kernel⟩
  | 19 => Sum.inl 1
  | 20 => Sum.inr ⟨(false, vertices_405), by decide +kernel⟩
  | 21 => Sum.inr ⟨(false, vertices_677), by decide +kernel⟩
  | 22 => Sum.inr ⟨(false, vertices_837), by decide +kernel⟩
  | 23 => Sum.inl 3
  | 24 => Sum.inl 4
  | 25 => Sum.inl 5
  | 26 => Sum.inl 6
  | 27 => Sum.inl 7
  | 28 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 2 4 6 3 186 42 3
cert_row_4 1 0 1 5 8 4 614 578 1
cert_row_4 2 2 5 7 8 0 842 328 3
cert_row_2 3 2 5 6 1 204
cert_rows
cert_pivot_2 3 4 0 1
cert_heightProof 4
cert_coverFacet 0 614
cert_cover_5 0 1 0 1 4 5 98 614 1
cert_coverFacet 1 186
cert_cover_5 1 0 0 2 3 4 26 186 3
cert_coverFacet 2 538
cert_cover_2 2 2 0 3 8 26 538 3
cert_coverFacet 3 106
cert_cover_2 3 2 0 4 5 42 106 3
cert_coverFacet 4 842
cert_cover_5 4 2 0 2 5 7 74 842 3
cert_coverFacet 5 674
cert_cover_2 5 4 0 6 8 162 674 3
cert_coverFacet 6 236
cert_cover_5 6 3 1 2 4 5 204 236 2
cert_coverFacet 7 460
cert_cover_5 7 3 1 2 5 7 204 460 3
cert_coverFacet 8 408
cert_cover_2 8 3 2 6 7 152 408 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_242

end
end BundlePart0

section BundlePart1
/- Source: ProjectionCertificates/P0_243.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_243

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [779, 355, 707, 653, 217, 345, 806, 626, 316, 156, 780, 564, 724, 368, 67, 259, 515, 89, 137, 265, 521, 193, 321, 641, 98, 290, 546, 578, 770, 28, 140, 268, 524, 52, 148, 532, 292, 548, 644, 772, 152, 280, 776, 112, 304, 560, 208, 336, 592, 352, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_779, vertices_355, vertices_707, vertices_653, vertices_217, vertices_345, vertices_806, vertices_626, vertices_316, vertices_156, vertices_780, vertices_564, vertices_724, vertices_368] (by decide +kernel)
  polygons := literalFinset [vertices_67, vertices_259, vertices_515, vertices_89, vertices_137, vertices_265, vertices_521, vertices_193, vertices_321, vertices_641, vertices_98, vertices_290, vertices_546, vertices_578, vertices_770, vertices_28, vertices_140, vertices_268, vertices_524, vertices_52, vertices_148, vertices_532, vertices_292, vertices_548, vertices_644, vertices_772, vertices_152, vertices_280, vertices_776, vertices_112, vertices_304, vertices_560, vertices_208, vertices_336, vertices_592, vertices_352, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_779), (false, vertices_355), (false, vertices_707), (false, vertices_653), (false, vertices_217), (false, vertices_345), (true, vertices_546), (true, vertices_28), (true, vertices_268), (true, vertices_52), (true, vertices_148), (true, vertices_532), (true, vertices_292), (true, vertices_548), (true, vertices_772), (true, vertices_112), (true, vertices_304), (true, vertices_560), (true, vertices_592)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 13 17 19 22 23 24 25 26 27
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_779) then 14 else
  if p.val = (false, vertices_355) then 15 else
  if p.val = (false, vertices_707) then 16 else
  if p.val = (false, vertices_653) then 18 else
  if p.val = (false, vertices_217) then 20 else
  if p.val = (false, vertices_345) then 21 else
  if p.val = (true, vertices_546) then 0 else
  if p.val = (true, vertices_28) then 1 else
  if p.val = (true, vertices_268) then 2 else
  if p.val = (true, vertices_52) then 3 else
  if p.val = (true, vertices_148) then 4 else
  if p.val = (true, vertices_532) then 5 else
  if p.val = (true, vertices_292) then 6 else
  if p.val = (true, vertices_548) then 7 else
  if p.val = (true, vertices_772) then 8 else
  if p.val = (true, vertices_112) then 9 else
  if p.val = (true, vertices_304) then 10 else
  if p.val = (true, vertices_560) then 11 else
  if p.val = (true, vertices_592) then 12 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_546), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_28), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_268), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_52), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_148), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_532), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_292), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_548), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_772), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_112), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_304), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_560), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_592), by decide +kernel⟩
  | 13 => Sum.inl 0
  | 14 => Sum.inr ⟨(false, vertices_779), by decide +kernel⟩
  | 15 => Sum.inr ⟨(false, vertices_355), by decide +kernel⟩
  | 16 => Sum.inr ⟨(false, vertices_707), by decide +kernel⟩
  | 17 => Sum.inl 1
  | 18 => Sum.inr ⟨(false, vertices_653), by decide +kernel⟩
  | 19 => Sum.inl 2
  | 20 => Sum.inr ⟨(false, vertices_217), by decide +kernel⟩
  | 21 => Sum.inr ⟨(false, vertices_345), by decide +kernel⟩
  | 22 => Sum.inl 3
  | 23 => Sum.inl 4
  | 24 => Sum.inl 5
  | 25 => Sum.inl 6
  | 26 => Sum.inl 7
  | 27 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 1 3 4 7 2 316 52 3
cert_row_4 1 0 1 4 8 7 806 546 1
cert_row_4 2 3 4 5 8 0 626 112 3
cert_row_4 3 3 5 6 8 1 724 208 3
cert_rows
cert_pivot_2 2 7 0 1
cert_heightProof 4
cert_coverFacet 0 806
cert_cover_5 0 1 0 1 4 7 290 806 1
cert_coverFacet 1 626
cert_cover_5 1 2 0 3 4 5 98 626 1
cert_coverFacet 2 316
cert_cover_5 2 0 1 2 3 4 28 316 3
cert_coverFacet 3 156
cert_cover_2 3 2 1 3 6 28 156 3
cert_coverFacet 4 780
cert_cover_2 4 2 1 7 8 268 780 3
cert_coverFacet 5 564
cert_cover_2 5 3 1 4 8 52 564 3
cert_coverFacet 6 724
cert_cover_5 6 3 1 3 5 6 148 724 2
cert_coverFacet 7 368
cert_cover_2 7 4 3 5 7 112 368 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_243

end
end BundlePart1

section BundlePart2
/- Source: ProjectionCertificates/P0_244.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_244

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [779, 837, 361, 681, 625, 398, 598, 150, 774, 650, 690, 372, 436, 424, 41, 265, 521, 97, 545, 321, 577, 769, 22, 134, 262, 518, 138, 266, 522, 146, 530, 642, 770, 308, 84, 148, 324, 580, 388, 772, 168, 296, 392, 648, 112, 176, 560, 592, 352, 416, 672]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_779, vertices_837, vertices_361, vertices_681, vertices_625, vertices_398, vertices_598, vertices_150, vertices_774, vertices_650, vertices_690, vertices_372, vertices_436, vertices_424] (by decide +kernel)
  polygons := literalFinset [vertices_41, vertices_265, vertices_521, vertices_97, vertices_545, vertices_321, vertices_577, vertices_769, vertices_22, vertices_134, vertices_262, vertices_518, vertices_138, vertices_266, vertices_522, vertices_146, vertices_530, vertices_642, vertices_770, vertices_308, vertices_84, vertices_148, vertices_324, vertices_580, vertices_388, vertices_772, vertices_168, vertices_296, vertices_392, vertices_648, vertices_112, vertices_176, vertices_560, vertices_592, vertices_352, vertices_416, vertices_672] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_779), (false, vertices_837), (false, vertices_361), (false, vertices_681), (false, vertices_625), (true, vertices_22), (true, vertices_134), (true, vertices_262), (true, vertices_518), (true, vertices_138), (true, vertices_146), (true, vertices_530), (true, vertices_642), (true, vertices_308), (true, vertices_84), (true, vertices_148), (true, vertices_388), (true, vertices_392), (true, vertices_176), (true, vertices_416)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 14 16 19 22 24 25 26 27 28
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_779) then 15 else
  if p.val = (false, vertices_837) then 17 else
  if p.val = (false, vertices_361) then 20 else
  if p.val = (false, vertices_681) then 21 else
  if p.val = (false, vertices_625) then 23 else
  if p.val = (true, vertices_22) then 0 else
  if p.val = (true, vertices_134) then 1 else
  if p.val = (true, vertices_262) then 2 else
  if p.val = (true, vertices_518) then 3 else
  if p.val = (true, vertices_138) then 4 else
  if p.val = (true, vertices_146) then 5 else
  if p.val = (true, vertices_530) then 6 else
  if p.val = (true, vertices_642) then 7 else
  if p.val = (true, vertices_308) then 18 else
  if p.val = (true, vertices_84) then 8 else
  if p.val = (true, vertices_148) then 9 else
  if p.val = (true, vertices_388) then 10 else
  if p.val = (true, vertices_392) then 11 else
  if p.val = (true, vertices_176) then 12 else
  if p.val = (true, vertices_416) then 13 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_22), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_134), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_262), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_518), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_138), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_146), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_530), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_642), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_84), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_148), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_388), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_392), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_176), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_416), by decide +kernel⟩
  | 14 => Sum.inl 0
  | 15 => Sum.inr ⟨(false, vertices_779), by decide +kernel⟩
  | 16 => Sum.inl 1
  | 17 => Sum.inr ⟨(false, vertices_837), by decide +kernel⟩
  | 18 => Sum.inr ⟨(true, vertices_308), by decide +kernel⟩
  | 19 => Sum.inl 2
  | 20 => Sum.inr ⟨(false, vertices_361), by decide +kernel⟩
  | 21 => Sum.inr ⟨(false, vertices_681), by decide +kernel⟩
  | 22 => Sum.inl 3
  | 23 => Sum.inr ⟨(false, vertices_625), by decide +kernel⟩
  | 24 => Sum.inl 4
  | 25 => Sum.inl 5
  | 26 => Sum.inl 6
  | 27 => Sum.inl 7
  | 28 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 6 7 2 398 134 3
cert_row_4 1 0 1 3 8 5 598 22 3
cert_row_4 2 3 4 6 8 0 690 176 3
cert_row_2 3 3 4 7 1 308
cert_rows
cert_pivot_2 2 5 0 1
cert_heightProof 4
cert_coverFacet 0 398
cert_cover_5 0 0 0 1 2 6 134 398 2
cert_coverFacet 1 598
cert_cover_5 1 1 0 1 3 5 22 598 3
cert_coverFacet 2 150
cert_cover_2 2 1 0 3 6 22 150 3
cert_coverFacet 3 774
cert_cover_2 3 1 0 7 8 262 774 3
cert_coverFacet 4 650
cert_cover_2 4 2 0 6 8 138 650 3
cert_coverFacet 5 690
cert_cover_5 5 2 0 3 4 6 146 690 2
cert_coverFacet 6 372
cert_cover_5 6 3 1 3 4 5 308 372 3
cert_coverFacet 7 436
cert_cover_5 7 3 1 3 4 6 308 436 3
cert_coverFacet 8 424
cert_cover_2 8 4 2 6 7 168 424 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_244

end
end BundlePart2

section BundlePart3
/- Source: ProjectionCertificates/P0_245.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_245

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [899, 709, 793, 625, 465, 302, 614, 390, 646, 570, 778, 244, 436, 312, 81, 273, 529, 193, 577, 385, 641, 769, 38, 134, 262, 518, 42, 266, 522, 546, 386, 642, 770, 180, 100, 292, 196, 580, 388, 644, 56, 280, 536, 296, 776, 112, 304, 560, 208, 400, 608]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_899, vertices_709, vertices_793, vertices_625, vertices_465, vertices_302, vertices_614, vertices_390, vertices_646, vertices_570, vertices_778, vertices_244, vertices_436, vertices_312] (by decide +kernel)
  polygons := literalFinset [vertices_81, vertices_273, vertices_529, vertices_193, vertices_577, vertices_385, vertices_641, vertices_769, vertices_38, vertices_134, vertices_262, vertices_518, vertices_42, vertices_266, vertices_522, vertices_546, vertices_386, vertices_642, vertices_770, vertices_180, vertices_100, vertices_292, vertices_196, vertices_580, vertices_388, vertices_644, vertices_56, vertices_280, vertices_536, vertices_296, vertices_776, vertices_112, vertices_304, vertices_560, vertices_208, vertices_400, vertices_608] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_899), (false, vertices_709), (false, vertices_793), (false, vertices_625), (false, vertices_465), (true, vertices_38), (true, vertices_134), (true, vertices_262), (true, vertices_518), (true, vertices_42), (true, vertices_266), (true, vertices_522), (true, vertices_546), (true, vertices_180), (true, vertices_100), (true, vertices_292), (true, vertices_388), (true, vertices_56), (true, vertices_296), (true, vertices_304)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 14 16 19 21 24 25 26 27 28
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_899) then 15 else
  if p.val = (false, vertices_709) then 17 else
  if p.val = (false, vertices_793) then 20 else
  if p.val = (false, vertices_625) then 22 else
  if p.val = (false, vertices_465) then 23 else
  if p.val = (true, vertices_38) then 0 else
  if p.val = (true, vertices_134) then 1 else
  if p.val = (true, vertices_262) then 2 else
  if p.val = (true, vertices_518) then 3 else
  if p.val = (true, vertices_42) then 4 else
  if p.val = (true, vertices_266) then 5 else
  if p.val = (true, vertices_522) then 6 else
  if p.val = (true, vertices_546) then 7 else
  if p.val = (true, vertices_180) then 18 else
  if p.val = (true, vertices_100) then 8 else
  if p.val = (true, vertices_292) then 9 else
  if p.val = (true, vertices_388) then 10 else
  if p.val = (true, vertices_56) then 11 else
  if p.val = (true, vertices_296) then 12 else
  if p.val = (true, vertices_304) then 13 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_38), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_134), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_262), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_518), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_42), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_266), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_522), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_546), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_100), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_292), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_388), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_56), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_296), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_304), by decide +kernel⟩
  | 14 => Sum.inl 0
  | 15 => Sum.inr ⟨(false, vertices_899), by decide +kernel⟩
  | 16 => Sum.inl 1
  | 17 => Sum.inr ⟨(false, vertices_709), by decide +kernel⟩
  | 18 => Sum.inr ⟨(true, vertices_180), by decide +kernel⟩
  | 19 => Sum.inl 2
  | 20 => Sum.inr ⟨(false, vertices_793), by decide +kernel⟩
  | 21 => Sum.inl 3
  | 22 => Sum.inr ⟨(false, vertices_625), by decide +kernel⟩
  | 23 => Sum.inr ⟨(false, vertices_465), by decide +kernel⟩
  | 24 => Sum.inl 4
  | 25 => Sum.inl 5
  | 26 => Sum.inl 6
  | 27 => Sum.inl 7
  | 28 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 2 4 7 302 38 2
cert_row_4 1 0 1 4 8 5 614 38 3
cert_row_4 2 2 3 4 8 0 570 56 3
cert_row_2 3 3 4 6 1 180
cert_rows
cert_pivot_2 7 5 0 1
cert_heightProof 4
cert_coverFacet 0 302
cert_cover_5 0 0 0 1 2 4 38 302 2
cert_coverFacet 1 614
cert_cover_5 1 1 0 1 4 5 38 614 3
cert_coverFacet 2 390
cert_cover_2 2 1 0 6 7 134 390 3
cert_coverFacet 3 646
cert_cover_2 3 1 0 6 8 134 646 3
cert_coverFacet 4 570
cert_cover_5 4 2 0 2 3 4 42 570 2
cert_coverFacet 5 778
cert_cover_2 5 2 0 7 8 266 778 3
cert_coverFacet 6 244
cert_cover_5 6 3 1 3 4 5 180 244 3
cert_coverFacet 7 436
cert_cover_5 7 3 1 3 4 7 180 436 3
cert_coverFacet 8 312
cert_cover_2 8 3 2 4 7 56 312 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_245

end
end BundlePart3

section BundlePart4
/- Source: ProjectionCertificates/P0_253.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_253

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [659, 309, 597, 229, 713, 433, 790, 426, 842, 650, 402, 364, 836, 232, 21, 37, 69, 305, 145, 529, 161, 193, 577, 641, 138, 266, 522, 146, 274, 530, 386, 642, 770, 276, 532, 100, 292, 324, 580, 772, 104, 168, 296, 200, 328, 584, 648, 400, 224, 416, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_659, vertices_309, vertices_597, vertices_229, vertices_713, vertices_433, vertices_790, vertices_426, vertices_842, vertices_650, vertices_402, vertices_364, vertices_836, vertices_232] (by decide +kernel)
  polygons := literalFinset [vertices_21, vertices_37, vertices_69, vertices_305, vertices_145, vertices_529, vertices_161, vertices_193, vertices_577, vertices_641, vertices_138, vertices_266, vertices_522, vertices_146, vertices_274, vertices_530, vertices_386, vertices_642, vertices_770, vertices_276, vertices_532, vertices_100, vertices_292, vertices_324, vertices_580, vertices_772, vertices_104, vertices_168, vertices_296, vertices_200, vertices_328, vertices_584, vertices_648, vertices_400, vertices_224, vertices_416, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_659), (false, vertices_309), (false, vertices_597), (false, vertices_229), (false, vertices_713), (false, vertices_433), (true, vertices_138), (true, vertices_266), (true, vertices_522), (true, vertices_274), (true, vertices_386), (true, vertices_770), (true, vertices_324), (true, vertices_772), (true, vertices_104), (true, vertices_168), (true, vertices_296), (true, vertices_328), (true, vertices_832)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 13 15 18 20 23 24 25 26 27
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_659) then 14 else
  if p.val = (false, vertices_309) then 21 else
  if p.val = (false, vertices_597) then 16 else
  if p.val = (false, vertices_229) then 17 else
  if p.val = (false, vertices_713) then 19 else
  if p.val = (false, vertices_433) then 22 else
  if p.val = (true, vertices_138) then 0 else
  if p.val = (true, vertices_266) then 1 else
  if p.val = (true, vertices_522) then 2 else
  if p.val = (true, vertices_274) then 3 else
  if p.val = (true, vertices_386) then 4 else
  if p.val = (true, vertices_770) then 5 else
  if p.val = (true, vertices_324) then 6 else
  if p.val = (true, vertices_772) then 7 else
  if p.val = (true, vertices_104) then 8 else
  if p.val = (true, vertices_168) then 9 else
  if p.val = (true, vertices_296) then 10 else
  if p.val = (true, vertices_328) then 11 else
  if p.val = (true, vertices_832) then 12 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_138), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_266), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_522), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_274), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_386), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_770), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_324), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_772), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_104), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_168), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_296), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_328), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_832), by decide +kernel⟩
  | 13 => Sum.inl 0
  | 14 => Sum.inr ⟨(false, vertices_659), by decide +kernel⟩
  | 15 => Sum.inl 1
  | 16 => Sum.inr ⟨(false, vertices_597), by decide +kernel⟩
  | 17 => Sum.inr ⟨(false, vertices_229), by decide +kernel⟩
  | 18 => Sum.inl 2
  | 19 => Sum.inr ⟨(false, vertices_713), by decide +kernel⟩
  | 20 => Sum.inl 3
  | 21 => Sum.inr ⟨(false, vertices_309), by decide +kernel⟩
  | 22 => Sum.inr ⟨(false, vertices_433), by decide +kernel⟩
  | 23 => Sum.inl 4
  | 24 => Sum.inl 5
  | 25 => Sum.inl 6
  | 26 => Sum.inl 7
  | 27 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 7 8 3 790 770 1
cert_row_4 1 0 2 4 7 6 426 266 2
cert_row_4 2 2 5 7 8 0 842 328 3
cert_row_4 3 2 4 5 7 1 364 104 3
cert_rows
cert_pivot_2 3 6 0 1
cert_heightProof 4
cert_coverFacet 0 790
cert_cover_5 0 0 0 1 3 7 274 790 1
cert_coverFacet 1 426
cert_cover_5 1 1 0 2 4 6 138 426 2
cert_coverFacet 2 842
cert_cover_5 2 2 0 2 5 7 266 842 2
cert_coverFacet 3 650
cert_cover_2 3 2 0 6 8 138 650 3
cert_coverFacet 4 402
cert_cover_2 4 3 0 6 7 146 402 3
cert_coverFacet 5 364
cert_cover_5 5 3 1 2 4 5 100 364 1
cert_coverFacet 6 836
cert_cover_2 6 5 1 7 8 324 836 3
cert_coverFacet 7 232
cert_cover_2 7 4 2 5 6 104 232 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_253

end
end BundlePart4

section BundlePart5
/- Source: ProjectionCertificates/P0_254.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_254

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [675, 653, 793, 425, 625, 305, 206, 614, 646, 458, 370, 418, 844, 848, 137, 265, 521, 49, 273, 529, 161, 289, 545, 641, 70, 134, 518, 202, 98, 162, 290, 546, 322, 386, 642, 76, 140, 524, 580, 644, 328, 392, 776, 112, 304, 336, 592, 784, 608, 416, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_675, vertices_653, vertices_793, vertices_425, vertices_625, vertices_305, vertices_206, vertices_614, vertices_646, vertices_458, vertices_370, vertices_418, vertices_844, vertices_848] (by decide +kernel)
  polygons := literalFinset [vertices_137, vertices_265, vertices_521, vertices_49, vertices_273, vertices_529, vertices_161, vertices_289, vertices_545, vertices_641, vertices_70, vertices_134, vertices_518, vertices_202, vertices_98, vertices_162, vertices_290, vertices_546, vertices_322, vertices_386, vertices_642, vertices_76, vertices_140, vertices_524, vertices_580, vertices_644, vertices_328, vertices_392, vertices_776, vertices_112, vertices_304, vertices_336, vertices_592, vertices_784, vertices_608, vertices_416, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_675), (false, vertices_653), (false, vertices_793), (false, vertices_425), (false, vertices_625), (false, vertices_305), (true, vertices_70), (true, vertices_134), (true, vertices_518), (true, vertices_202), (true, vertices_98), (true, vertices_290), (true, vertices_322), (true, vertices_386), (true, vertices_76), (true, vertices_580), (true, vertices_328), (true, vertices_336), (true, vertices_832)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 13 16 18 21 23 24 25 26 27
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_675) then 14 else
  if p.val = (false, vertices_653) then 17 else
  if p.val = (false, vertices_793) then 19 else
  if p.val = (false, vertices_425) then 20 else
  if p.val = (false, vertices_625) then 22 else
  if p.val = (false, vertices_305) then 12 else
  if p.val = (true, vertices_70) then 0 else
  if p.val = (true, vertices_134) then 1 else
  if p.val = (true, vertices_518) then 2 else
  if p.val = (true, vertices_202) then 15 else
  if p.val = (true, vertices_98) then 3 else
  if p.val = (true, vertices_290) then 4 else
  if p.val = (true, vertices_322) then 5 else
  if p.val = (true, vertices_386) then 6 else
  if p.val = (true, vertices_76) then 7 else
  if p.val = (true, vertices_580) then 8 else
  if p.val = (true, vertices_328) then 9 else
  if p.val = (true, vertices_336) then 10 else
  if p.val = (true, vertices_832) then 11 else
  0
cert_priority
cert_nodeAtPriority_56 70 134 518 98 290 322 386 76 580 328 336 832 305 675 202 653 793 425 625
cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 4 5 7 3 370 98 3
cert_row_4 1 0 1 5 8 4 614 70 3
cert_row_4 2 2 5 7 8 1 844 328 3
cert_row_2 3 2 5 6 0 202
cert_rows
cert_pivot_2 3 4 1 0
cert_heightProof 4
cert_coverFacet 0 206
cert_cover_5 0 3 0 1 2 5 70 206 2
cert_coverFacet 1 614
cert_cover_5 1 1 0 1 4 5 70 614 2
cert_coverFacet 2 646
cert_cover_2 2 1 0 6 8 134 646 3
cert_coverFacet 3 458
cert_cover_5 3 3 0 2 5 7 202 458 3
cert_coverFacet 4 370
cert_cover_5 4 0 0 3 4 5 98 370 1
cert_coverFacet 5 418
cert_cover_2 5 4 0 6 7 162 418 3
cert_coverFacet 6 844
cert_cover_5 6 2 1 2 5 7 76 844 3
cert_coverFacet 7 848
cert_cover_2 7 5 3 7 8 336 848 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_254

end
end BundlePart5

section BundlePart6
/- Source: ProjectionCertificates/P0_259.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_259

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [651, 227, 803, 397, 793, 481, 710, 626, 604, 284, 652, 372, 452, 816, 35, 131, 515, 137, 265, 521, 225, 289, 385, 769, 98, 546, 194, 578, 642, 28, 140, 268, 524, 84, 276, 196, 324, 580, 388, 644, 280, 536, 648, 112, 304, 560, 592, 784, 352, 800, 448]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_651, vertices_227, vertices_803, vertices_397, vertices_793, vertices_481, vertices_710, vertices_626, vertices_604, vertices_284, vertices_652, vertices_372, vertices_452, vertices_816] (by decide +kernel)
  polygons := literalFinset [vertices_35, vertices_131, vertices_515, vertices_137, vertices_265, vertices_521, vertices_225, vertices_289, vertices_385, vertices_769, vertices_98, vertices_546, vertices_194, vertices_578, vertices_642, vertices_28, vertices_140, vertices_268, vertices_524, vertices_84, vertices_276, vertices_196, vertices_324, vertices_580, vertices_388, vertices_644, vertices_280, vertices_536, vertices_648, vertices_112, vertices_304, vertices_560, vertices_592, vertices_784, vertices_352, vertices_800, vertices_448] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_651), (false, vertices_227), (false, vertices_803), (false, vertices_397), (false, vertices_793), (false, vertices_481), (true, vertices_578), (true, vertices_28), (true, vertices_524), (true, vertices_84), (true, vertices_276), (true, vertices_196), (true, vertices_324), (true, vertices_580), (true, vertices_644), (true, vertices_112), (true, vertices_304), (true, vertices_560), (true, vertices_592)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 13 16 18 20 21 24 25 26 27
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_651) then 14 else
  if p.val = (false, vertices_227) then 22 else
  if p.val = (false, vertices_803) then 15 else
  if p.val = (false, vertices_397) then 17 else
  if p.val = (false, vertices_793) then 19 else
  if p.val = (false, vertices_481) then 23 else
  if p.val = (true, vertices_578) then 0 else
  if p.val = (true, vertices_28) then 1 else
  if p.val = (true, vertices_524) then 2 else
  if p.val = (true, vertices_84) then 3 else
  if p.val = (true, vertices_276) then 4 else
  if p.val = (true, vertices_196) then 5 else
  if p.val = (true, vertices_324) then 6 else
  if p.val = (true, vertices_580) then 7 else
  if p.val = (true, vertices_644) then 8 else
  if p.val = (true, vertices_112) then 9 else
  if p.val = (true, vertices_304) then 10 else
  if p.val = (true, vertices_560) then 11 else
  if p.val = (true, vertices_592) then 12 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_578), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_28), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_524), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_84), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_276), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_196), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_324), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_580), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_644), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_112), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_304), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_560), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_592), by decide +kernel⟩
  | 13 => Sum.inl 0
  | 14 => Sum.inr ⟨(false, vertices_651), by decide +kernel⟩
  | 15 => Sum.inr ⟨(false, vertices_803), by decide +kernel⟩
  | 16 => Sum.inl 1
  | 17 => Sum.inr ⟨(false, vertices_397), by decide +kernel⟩
  | 18 => Sum.inl 2
  | 19 => Sum.inr ⟨(false, vertices_793), by decide +kernel⟩
  | 20 => Sum.inl 3
  | 21 => Sum.inl 4
  | 22 => Sum.inr ⟨(false, vertices_227), by decide +kernel⟩
  | 23 => Sum.inr ⟨(false, vertices_481), by decide +kernel⟩
  | 24 => Sum.inl 5
  | 25 => Sum.inl 6
  | 26 => Sum.inl 7
  | 27 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 5 8 6 710 578 1
cert_row_4 1 3 4 5 8 0 626 112 3
cert_row_4 2 1 3 5 8 2 604 84 3
cert_row_4 3 3 4 5 7 1 372 112 3
cert_rows
cert_pivot_2 6 0 2 1
cert_heightProof 4
cert_coverFacet 0 710
cert_cover_5 0 0 0 1 5 6 194 710 1
cert_coverFacet 1 626
cert_cover_5 1 1 0 3 4 5 98 626 1
cert_coverFacet 2 604
cert_cover_5 2 2 1 2 3 5 28 604 3
cert_coverFacet 3 284
cert_cover_2 3 2 1 3 7 28 284 3
cert_coverFacet 4 652
cert_cover_2 4 2 1 6 8 140 652 3
cert_coverFacet 5 372
cert_cover_5 5 3 1 3 4 5 84 372 2
cert_coverFacet 6 452
cert_cover_2 6 5 1 6 7 196 452 3
cert_coverFacet 7 816
cert_cover_2 7 4 3 7 8 304 816 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_259

end
end BundlePart6

section BundlePart7
/- Source: ProjectionCertificates/P0_269.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_269

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [775, 677, 453, 233, 625, 833, 398, 654, 570, 282, 850, 120, 472, 680, 133, 261, 517, 97, 161, 545, 193, 321, 577, 769, 142, 262, 518, 26, 266, 522, 274, 530, 770, 388, 644, 56, 88, 280, 104, 168, 552, 200, 392, 648, 112, 560, 336, 592, 672, 448, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_775, vertices_677, vertices_453, vertices_233, vertices_625, vertices_833, vertices_398, vertices_654, vertices_570, vertices_282, vertices_850, vertices_120, vertices_472, vertices_680] (by decide +kernel)
  polygons := literalFinset [vertices_133, vertices_261, vertices_517, vertices_97, vertices_161, vertices_545, vertices_193, vertices_321, vertices_577, vertices_769, vertices_142, vertices_262, vertices_518, vertices_26, vertices_266, vertices_522, vertices_274, vertices_530, vertices_770, vertices_388, vertices_644, vertices_56, vertices_88, vertices_280, vertices_104, vertices_168, vertices_552, vertices_200, vertices_392, vertices_648, vertices_112, vertices_560, vertices_336, vertices_592, vertices_672, vertices_448, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_775), (false, vertices_677), (false, vertices_453), (false, vertices_233), (false, vertices_625), (false, vertices_833), (true, vertices_142), (true, vertices_26), (true, vertices_266), (true, vertices_522), (true, vertices_274), (true, vertices_530), (true, vertices_56), (true, vertices_88), (true, vertices_280), (true, vertices_552), (true, vertices_392), (true, vertices_648), (true, vertices_336)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 13 16 19 21 23 24 25 26 27
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_775) then 14 else
  if p.val = (false, vertices_677) then 17 else
  if p.val = (false, vertices_453) then 18 else
  if p.val = (false, vertices_233) then 20 else
  if p.val = (false, vertices_625) then 22 else
  if p.val = (false, vertices_833) then 12 else
  if p.val = (true, vertices_142) then 15 else
  if p.val = (true, vertices_26) then 0 else
  if p.val = (true, vertices_266) then 1 else
  if p.val = (true, vertices_522) then 2 else
  if p.val = (true, vertices_274) then 3 else
  if p.val = (true, vertices_530) then 4 else
  if p.val = (true, vertices_56) then 5 else
  if p.val = (true, vertices_88) then 6 else
  if p.val = (true, vertices_280) then 7 else
  if p.val = (true, vertices_552) then 8 else
  if p.val = (true, vertices_392) then 9 else
  if p.val = (true, vertices_648) then 10 else
  if p.val = (true, vertices_336) then 11 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_26), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_266), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_522), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_274), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_530), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_56), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_88), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_280), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_552), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_392), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_648), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_336), by decide +kernel⟩
  | 12 => Sum.inr ⟨(false, vertices_833), by decide +kernel⟩
  | 13 => Sum.inl 0
  | 14 => Sum.inr ⟨(false, vertices_775), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_142), by decide +kernel⟩
  | 16 => Sum.inl 1
  | 17 => Sum.inr ⟨(false, vertices_677), by decide +kernel⟩
  | 18 => Sum.inr ⟨(false, vertices_453), by decide +kernel⟩
  | 19 => Sum.inl 2
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
cert_row_4 0 0 2 3 8 4 570 26 3
cert_row_4 1 0 3 5 7 8 850 274 2
cert_row_4 2 2 5 6 7 3 472 200 3
cert_row_2 3 1 2 6 0 142
cert_rows
cert_pivot_2 4 8 3 0
cert_heightProof 4
cert_coverFacet 0 398
cert_cover_5 0 3 0 1 2 7 142 398 3
cert_coverFacet 1 654
cert_cover_5 1 3 0 1 2 8 142 654 3
cert_coverFacet 2 570
cert_cover_5 2 0 0 2 3 4 26 570 3
cert_coverFacet 3 282
cert_cover_2 3 2 0 3 7 26 282 3
cert_coverFacet 4 850
cert_cover_5 4 1 0 3 5 7 274 850 2
cert_coverFacet 5 120
cert_cover_2 5 3 2 4 5 56 120 3
cert_coverFacet 6 472
cert_cover_5 6 2 2 3 5 6 88 472 3
cert_coverFacet 7 680
cert_cover_2 7 4 2 6 8 168 680 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_269

end
end BundlePart7

section BundlePart8
/- Source: ProjectionCertificates/P0_272.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_272

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [787, 653, 341, 533, 197, 233, 841, 406, 662, 682, 866, 418, 484, 616, 21, 69, 133, 517, 73, 137, 521, 273, 529, 193, 321, 769, 150, 274, 530, 162, 290, 546, 386, 642, 770, 276, 532, 196, 324, 388, 644, 104, 168, 552, 584, 648, 224, 352, 608, 416, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_787, vertices_653, vertices_341, vertices_533, vertices_197, vertices_233, vertices_841, vertices_406, vertices_662, vertices_682, vertices_866, vertices_418, vertices_484, vertices_616] (by decide +kernel)
  polygons := literalFinset [vertices_21, vertices_69, vertices_133, vertices_517, vertices_73, vertices_137, vertices_521, vertices_273, vertices_529, vertices_193, vertices_321, vertices_769, vertices_150, vertices_274, vertices_530, vertices_162, vertices_290, vertices_546, vertices_386, vertices_642, vertices_770, vertices_276, vertices_532, vertices_196, vertices_324, vertices_388, vertices_644, vertices_104, vertices_168, vertices_552, vertices_584, vertices_648, vertices_224, vertices_352, vertices_608, vertices_416, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_787), (false, vertices_653), (false, vertices_341), (false, vertices_533), (false, vertices_197), (false, vertices_233), (false, vertices_841), (true, vertices_150), (true, vertices_162), (true, vertices_290), (true, vertices_546), (true, vertices_386), (true, vertices_642), (true, vertices_388), (true, vertices_552), (true, vertices_352), (true, vertices_608), (true, vertices_416)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 12 15 18 21 22 23 24 25 26
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_787) then 13 else
  if p.val = (false, vertices_653) then 16 else
  if p.val = (false, vertices_341) then 17 else
  if p.val = (false, vertices_533) then 10 else
  if p.val = (false, vertices_197) then 11 else
  if p.val = (false, vertices_233) then 19 else
  if p.val = (false, vertices_841) then 20 else
  if p.val = (true, vertices_150) then 14 else
  if p.val = (true, vertices_162) then 0 else
  if p.val = (true, vertices_290) then 1 else
  if p.val = (true, vertices_546) then 2 else
  if p.val = (true, vertices_386) then 3 else
  if p.val = (true, vertices_642) then 4 else
  if p.val = (true, vertices_388) then 5 else
  if p.val = (true, vertices_552) then 6 else
  if p.val = (true, vertices_352) then 7 else
  if p.val = (true, vertices_608) then 8 else
  if p.val = (true, vertices_416) then 9 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_162), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_290), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_546), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_386), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_642), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_388), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_552), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_352), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_608), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_416), by decide +kernel⟩
  | 10 => Sum.inr ⟨(false, vertices_533), by decide +kernel⟩
  | 11 => Sum.inr ⟨(false, vertices_197), by decide +kernel⟩
  | 12 => Sum.inl 0
  | 13 => Sum.inr ⟨(false, vertices_787), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_150), by decide +kernel⟩
  | 15 => Sum.inl 1
  | 16 => Sum.inr ⟨(false, vertices_653), by decide +kernel⟩
  | 17 => Sum.inr ⟨(false, vertices_341), by decide +kernel⟩
  | 18 => Sum.inl 2
  | 19 => Sum.inr ⟨(false, vertices_233), by decide +kernel⟩
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
cert_row_4 0 0 4 6 8 2 682 162 3
cert_row_4 1 0 4 5 7 8 866 290 2
cert_row_4 2 1 5 6 7 4 484 196 3
cert_row_2 3 1 3 6 0 150
cert_rows
cert_pivot_2 2 8 4 0
cert_heightProof 4
cert_coverFacet 0 406
cert_cover_5 0 3 0 1 3 7 150 406 3
cert_coverFacet 1 662
cert_cover_5 1 3 0 1 3 8 150 662 3
cert_coverFacet 2 682
cert_cover_5 2 0 0 2 4 6 162 682 1
cert_coverFacet 3 866
cert_cover_5 3 1 0 4 5 7 290 866 2
cert_coverFacet 4 418
cert_cover_2 4 4 0 6 7 162 418 3
cert_coverFacet 5 484
cert_cover_5 5 2 1 4 5 6 196 484 1
cert_coverFacet 6 616
cert_cover_2 6 4 2 5 8 104 616 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_272

end
end BundlePart8

section BundlePart9
/- Source: ProjectionCertificates/P0_285.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_285

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [675, 781, 345, 713, 241, 817, 590, 422, 806, 198, 706, 332, 468, 432, 73, 265, 521, 49, 81, 273, 161, 545, 193, 641, 769, 294, 70, 134, 518, 162, 546, 194, 578, 642, 76, 268, 524, 196, 324, 388, 772, 328, 584, 176, 304, 208, 336, 400, 416, 800, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_675, vertices_781, vertices_345, vertices_713, vertices_241, vertices_817, vertices_590, vertices_422, vertices_806, vertices_198, vertices_706, vertices_332, vertices_468, vertices_432] (by decide +kernel)
  polygons := literalFinset [vertices_73, vertices_265, vertices_521, vertices_49, vertices_81, vertices_273, vertices_161, vertices_545, vertices_193, vertices_641, vertices_769, vertices_294, vertices_70, vertices_134, vertices_518, vertices_162, vertices_546, vertices_194, vertices_578, vertices_642, vertices_76, vertices_268, vertices_524, vertices_196, vertices_324, vertices_388, vertices_772, vertices_328, vertices_584, vertices_176, vertices_304, vertices_208, vertices_336, vertices_400, vertices_416, vertices_800, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_675), (false, vertices_781), (false, vertices_345), (false, vertices_713), (false, vertices_241), (false, vertices_817), (true, vertices_294), (true, vertices_70), (true, vertices_134), (true, vertices_518), (true, vertices_194), (true, vertices_578), (true, vertices_76), (true, vertices_196), (true, vertices_324), (true, vertices_388), (true, vertices_400), (true, vertices_416)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 11 14 16 19 22 23 24 25 26
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_675) then 12 else
  if p.val = (false, vertices_781) then 15 else
  if p.val = (false, vertices_345) then 17 else
  if p.val = (false, vertices_713) then 18 else
  if p.val = (false, vertices_241) then 20 else
  if p.val = (false, vertices_817) then 21 else
  if p.val = (true, vertices_294) then 13 else
  if p.val = (true, vertices_70) then 0 else
  if p.val = (true, vertices_134) then 1 else
  if p.val = (true, vertices_518) then 2 else
  if p.val = (true, vertices_194) then 3 else
  if p.val = (true, vertices_578) then 4 else
  if p.val = (true, vertices_76) then 5 else
  if p.val = (true, vertices_196) then 6 else
  if p.val = (true, vertices_324) then 7 else
  if p.val = (true, vertices_388) then 8 else
  if p.val = (true, vertices_400) then 9 else
  if p.val = (true, vertices_416) then 10 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_70), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_134), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_518), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_194), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_578), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_76), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_196), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_324), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_388), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_400), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_416), by decide +kernel⟩
  | 11 => Sum.inl 0
  | 12 => Sum.inr ⟨(false, vertices_675), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_294), by decide +kernel⟩
  | 14 => Sum.inl 1
  | 15 => Sum.inr ⟨(false, vertices_781), by decide +kernel⟩
  | 16 => Sum.inl 2
  | 17 => Sum.inr ⟨(false, vertices_345), by decide +kernel⟩
  | 18 => Sum.inr ⟨(false, vertices_713), by decide +kernel⟩
  | 19 => Sum.inl 3
  | 20 => Sum.inr ⟨(false, vertices_241), by decide +kernel⟩
  | 21 => Sum.inr ⟨(false, vertices_817), by decide +kernel⟩
  | 22 => Sum.inl 4
  | 23 => Sum.inl 5
  | 24 => Sum.inl 6
  | 25 => Sum.inl 7
  | 26 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 5 8 2 590 70 3
cert_row_4 1 1 5 6 7 3 468 196 3
cert_row_2 2 1 4 7 0 294
cert_rows_3
cert_pivot_3 3 2 0
cert_heightProof 3
cert_coverFacet 0 590
cert_cover_5 0 0 0 1 2 5 70 590 2
cert_coverFacet 1 422
cert_cover_5 1 2 0 1 4 6 294 422 3
cert_coverFacet 2 806
cert_cover_5 2 2 0 1 4 8 294 806 3
cert_coverFacet 3 198
cert_cover_2 3 1 0 5 6 70 198 3
cert_coverFacet 4 706
cert_cover_2 4 5 0 6 8 194 706 3
cert_coverFacet 5 332
cert_cover_2 5 2 1 5 7 76 332 3
cert_coverFacet 6 468
cert_cover_5 6 1 1 3 5 6 196 468 1
cert_coverFacet 7 432
cert_cover_2 7 4 3 6 7 176 432 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 3 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_285

end
end BundlePart9

section BundlePart10
/- Source: ProjectionCertificates/P0_296.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_296

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [295, 395, 163, 653, 269, 613, 721, 225, 242, 850, 402, 866, 812, 920, 35, 131, 259, 13, 37, 261, 517, 137, 265, 97, 161, 193, 577, 641, 82, 146, 274, 98, 162, 290, 834, 386, 268, 524, 292, 548, 392, 648, 776, 208, 592, 400, 656, 784, 224, 608, 800]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_295, vertices_395, vertices_163, vertices_653, vertices_269, vertices_613, vertices_721, vertices_225, vertices_242, vertices_850, vertices_402, vertices_866, vertices_812, vertices_920] (by decide +kernel)
  polygons := literalFinset [vertices_35, vertices_131, vertices_259, vertices_13, vertices_37, vertices_261, vertices_517, vertices_137, vertices_265, vertices_97, vertices_161, vertices_193, vertices_577, vertices_641, vertices_82, vertices_146, vertices_274, vertices_98, vertices_162, vertices_290, vertices_834, vertices_386, vertices_268, vertices_524, vertices_292, vertices_548, vertices_392, vertices_648, vertices_776, vertices_208, vertices_592, vertices_400, vertices_656, vertices_784, vertices_224, vertices_608, vertices_800] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_295), (false, vertices_395), (false, vertices_163), (false, vertices_653), (false, vertices_269), (false, vertices_613), (false, vertices_721), (false, vertices_225), (true, vertices_82), (true, vertices_146), (true, vertices_274), (true, vertices_98), (true, vertices_834), (true, vertices_776), (true, vertices_400), (true, vertices_784), (true, vertices_800)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 11 18 19 21 22 23 24 25
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_295) then 12 else
  if p.val = (false, vertices_395) then 16 else
  if p.val = (false, vertices_163) then 8 else
  if p.val = (false, vertices_653) then 13 else
  if p.val = (false, vertices_269) then 9 else
  if p.val = (false, vertices_613) then 14 else
  if p.val = (false, vertices_721) then 20 else
  if p.val = (false, vertices_225) then 10 else
  if p.val = (true, vertices_82) then 0 else
  if p.val = (true, vertices_146) then 1 else
  if p.val = (true, vertices_274) then 2 else
  if p.val = (true, vertices_98) then 3 else
  if p.val = (true, vertices_834) then 17 else
  if p.val = (true, vertices_776) then 4 else
  if p.val = (true, vertices_400) then 5 else
  if p.val = (true, vertices_784) then 6 else
  if p.val = (true, vertices_800) then 7 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_82), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_146), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_274), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_98), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_776), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_400), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_784), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_800), by decide +kernel⟩
  | 8 => Sum.inr ⟨(false, vertices_163), by decide +kernel⟩
  | 9 => Sum.inr ⟨(false, vertices_269), by decide +kernel⟩
  | 10 => Sum.inr ⟨(false, vertices_225), by decide +kernel⟩
  | 11 => Sum.inl 1
  | 12 => Sum.inr ⟨(false, vertices_295), by decide +kernel⟩
  | 13 => Sum.inr ⟨(false, vertices_653), by decide +kernel⟩
  | 14 => Sum.inr ⟨(false, vertices_613), by decide +kernel⟩
  | 15 => Sum.inl 0
  | 16 => Sum.inr ⟨(false, vertices_395), by decide +kernel⟩
  | 17 => Sum.inr ⟨(true, vertices_834), by decide +kernel⟩
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
cert_row_4 0 2 4 7 8 1 812 776 1
cert_row_4 1 0 3 5 6 4 242 82 3
cert_row_4 2 3 6 7 8 2 920 400 3
cert_row_2 3 5 7 8 0 834
cert_rows
cert_pivot_2 1 4 2 0
cert_heightProof 4
cert_coverFacet 0 242
cert_cover_5 0 1 0 3 4 5 82 242 2
cert_coverFacet 1 850
cert_cover_5 1 3 0 3 5 7 82 850 3
cert_coverFacet 2 402
cert_cover_2 2 3 0 6 7 146 402 3
cert_coverFacet 3 866
cert_cover_5 3 3 0 4 5 7 98 866 3
cert_coverFacet 4 812
cert_cover_5 4 0 1 2 4 7 268 812 2
cert_coverFacet 5 920
cert_cover_5 5 2 2 3 6 7 392 920 1
cert_coveringFacets
cert_coveringProof_6
cert_certificate 4 6
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_296

end
end BundlePart10

section BundlePart11
/- Source: ProjectionCertificates/P0_299.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_299

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [647, 157, 269, 805, 57, 361, 689, 398, 838, 458, 722, 632, 216, 864, 13, 133, 261, 517, 25, 41, 265, 49, 145, 289, 545, 641, 134, 262, 518, 394, 194, 322, 578, 642, 140, 268, 772, 56, 88, 152, 104, 200, 328, 560, 208, 592, 656, 352, 608, 800, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_647, vertices_157, vertices_269, vertices_805, vertices_57, vertices_361, vertices_689, vertices_398, vertices_838, vertices_458, vertices_722, vertices_632, vertices_216, vertices_864] (by decide +kernel)
  polygons := literalFinset [vertices_13, vertices_133, vertices_261, vertices_517, vertices_25, vertices_41, vertices_265, vertices_49, vertices_145, vertices_289, vertices_545, vertices_641, vertices_134, vertices_262, vertices_518, vertices_394, vertices_194, vertices_322, vertices_578, vertices_642, vertices_140, vertices_268, vertices_772, vertices_56, vertices_88, vertices_152, vertices_104, vertices_200, vertices_328, vertices_560, vertices_208, vertices_592, vertices_656, vertices_352, vertices_608, vertices_800, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_647), (false, vertices_157), (false, vertices_269), (false, vertices_805), (false, vertices_57), (false, vertices_361), (false, vertices_689), (true, vertices_262), (true, vertices_394), (true, vertices_194), (true, vertices_322), (true, vertices_578), (true, vertices_88), (true, vertices_200), (true, vertices_208), (true, vertices_592), (true, vertices_608), (true, vertices_832)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 12 15 18 20 22 23 24 25 26
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_647) then 13 else
  if p.val = (false, vertices_157) then 16 else
  if p.val = (false, vertices_269) then 10 else
  if p.val = (false, vertices_805) then 17 else
  if p.val = (false, vertices_57) then 11 else
  if p.val = (false, vertices_361) then 19 else
  if p.val = (false, vertices_689) then 21 else
  if p.val = (true, vertices_262) then 0 else
  if p.val = (true, vertices_394) then 14 else
  if p.val = (true, vertices_194) then 1 else
  if p.val = (true, vertices_322) then 2 else
  if p.val = (true, vertices_578) then 3 else
  if p.val = (true, vertices_88) then 4 else
  if p.val = (true, vertices_200) then 5 else
  if p.val = (true, vertices_208) then 6 else
  if p.val = (true, vertices_592) then 7 else
  if p.val = (true, vertices_608) then 8 else
  if p.val = (true, vertices_832) then 9 else
  0
cert_priority
cert_nodeAtPriority_7 0 262 1 194 2 322 578 88 200 208 592 608 832 269 57 647 394 157 805 361 689
cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 5 7 8 1 838 322 3
cert_row_4 1 2 3 5 8 4 632 88 3
cert_row_4 2 0 5 6 8 3 722 194 3
cert_row_2 3 2 6 7 0 394
cert_rows
cert_pivot_2 1 4 3 0
cert_heightProof 4
cert_coverFacet 0 398
cert_cover_5 0 3 0 1 2 6 134 398 2
cert_coverFacet 1 838
cert_cover_5 1 0 0 1 5 7 262 838 2
cert_coverFacet 2 458
cert_cover_5 2 3 0 2 5 6 394 458 2
cert_coverFacet 3 722
cert_cover_5 3 2 0 3 5 6 194 722 1
cert_coverFacet 4 632
cert_cover_5 4 1 2 3 4 5 56 632 3
cert_coverFacet 5 216
cert_cover_2 5 3 2 5 6 88 216 3
cert_coverFacet 6 864
cert_cover_2 6 5 4 7 8 352 864 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_299

end
end BundlePart11

section BundlePart12
/- Source: ProjectionCertificates/P0_300.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_300

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [659, 597, 405, 357, 713, 449, 310, 566, 810, 458, 650, 402, 620, 360, 21, 69, 261, 145, 529, 193, 321, 577, 385, 641, 54, 138, 266, 522, 146, 274, 530, 290, 546, 386, 642, 276, 532, 100, 292, 548, 580, 104, 296, 552, 200, 328, 584, 648, 400, 352, 448]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_659, vertices_597, vertices_405, vertices_357, vertices_713, vertices_449, vertices_310, vertices_566, vertices_810, vertices_458, vertices_650, vertices_402, vertices_620, vertices_360] (by decide +kernel)
  polygons := literalFinset [vertices_21, vertices_69, vertices_261, vertices_145, vertices_529, vertices_193, vertices_321, vertices_577, vertices_385, vertices_641, vertices_54, vertices_138, vertices_266, vertices_522, vertices_146, vertices_274, vertices_530, vertices_290, vertices_546, vertices_386, vertices_642, vertices_276, vertices_532, vertices_100, vertices_292, vertices_548, vertices_580, vertices_104, vertices_296, vertices_552, vertices_200, vertices_328, vertices_584, vertices_648, vertices_400, vertices_352, vertices_448] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_659), (false, vertices_597), (false, vertices_405), (false, vertices_357), (false, vertices_713), (false, vertices_449), (true, vertices_54), (true, vertices_138), (true, vertices_266), (true, vertices_522), (true, vertices_274), (true, vertices_290), (true, vertices_546), (true, vertices_386), (true, vertices_548), (true, vertices_104), (true, vertices_296), (true, vertices_552), (true, vertices_328)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 13 16 20 22 23 24 25 26 27
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_659) then 14 else
  if p.val = (false, vertices_597) then 17 else
  if p.val = (false, vertices_405) then 18 else
  if p.val = (false, vertices_357) then 19 else
  if p.val = (false, vertices_713) then 21 else
  if p.val = (false, vertices_449) then 12 else
  if p.val = (true, vertices_54) then 15 else
  if p.val = (true, vertices_138) then 0 else
  if p.val = (true, vertices_266) then 1 else
  if p.val = (true, vertices_522) then 2 else
  if p.val = (true, vertices_274) then 3 else
  if p.val = (true, vertices_290) then 4 else
  if p.val = (true, vertices_546) then 5 else
  if p.val = (true, vertices_386) then 6 else
  if p.val = (true, vertices_548) then 7 else
  if p.val = (true, vertices_104) then 8 else
  if p.val = (true, vertices_296) then 9 else
  if p.val = (true, vertices_552) then 10 else
  if p.val = (true, vertices_328) then 11 else
  0
cert_priority
cert_nodeAtPriority_57 138 266 522 274 290 546 386 548 104 296 552 328 449 659 54 597 405 357 713
cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 2 5 7 6 458 266 2
cert_row_4 1 0 2 4 8 7 810 522 2
cert_row_4 2 1 4 5 8 2 620 100 3
cert_row_2 3 1 3 4 0 54
cert_rows
cert_pivot_2 6 7 2 0
cert_heightProof 4
cert_coverFacet 0 310
cert_cover_5 0 3 0 1 3 7 54 310 3
cert_coverFacet 1 566
cert_cover_5 1 3 0 1 3 8 54 566 3
cert_coverFacet 2 810
cert_cover_5 2 1 0 2 4 7 266 810 2
cert_coverFacet 3 458
cert_cover_5 3 0 0 2 5 6 138 458 2
cert_coverFacet 4 650
cert_cover_2 4 2 0 6 8 138 650 3
cert_coverFacet 5 402
cert_cover_2 5 3 0 6 7 146 402 3
cert_coverFacet 6 620
cert_cover_5 6 2 1 2 4 5 100 620 1
cert_coverFacet 7 360
cert_cover_2 7 4 2 5 7 104 360 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_300

end
end BundlePart12

section BundlePart13
/- Source: ProjectionCertificates/P0_315.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_315

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [339, 661, 277, 453, 681, 625, 225, 790, 618, 426, 778, 594, 482, 908, 21, 133, 261, 81, 273, 529, 97, 161, 545, 193, 321, 641, 42, 266, 522, 82, 274, 530, 98, 418, 322, 578, 770, 276, 532, 388, 644, 772, 168, 552, 392, 648, 776, 592, 224, 608, 448]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_339, vertices_661, vertices_277, vertices_453, vertices_681, vertices_625, vertices_225, vertices_790, vertices_618, vertices_426, vertices_778, vertices_594, vertices_482, vertices_908] (by decide +kernel)
  polygons := literalFinset [vertices_21, vertices_133, vertices_261, vertices_81, vertices_273, vertices_529, vertices_97, vertices_161, vertices_545, vertices_193, vertices_321, vertices_641, vertices_42, vertices_266, vertices_522, vertices_82, vertices_274, vertices_530, vertices_98, vertices_418, vertices_322, vertices_578, vertices_770, vertices_276, vertices_532, vertices_388, vertices_644, vertices_772, vertices_168, vertices_552, vertices_392, vertices_648, vertices_776, vertices_592, vertices_224, vertices_608, vertices_448] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_339), (false, vertices_661), (false, vertices_277), (false, vertices_453), (false, vertices_681), (false, vertices_625), (false, vertices_225), (true, vertices_42), (true, vertices_266), (true, vertices_522), (true, vertices_530), (true, vertices_98), (true, vertices_418), (true, vertices_578), (true, vertices_770), (true, vertices_772), (true, vertices_392), (true, vertices_776)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 12 15 18 20 22 23 24 25 26
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_339) then 13 else
  if p.val = (false, vertices_661) then 16 else
  if p.val = (false, vertices_277) then 10 else
  if p.val = (false, vertices_453) then 17 else
  if p.val = (false, vertices_681) then 19 else
  if p.val = (false, vertices_625) then 21 else
  if p.val = (false, vertices_225) then 11 else
  if p.val = (true, vertices_42) then 0 else
  if p.val = (true, vertices_266) then 1 else
  if p.val = (true, vertices_522) then 2 else
  if p.val = (true, vertices_530) then 3 else
  if p.val = (true, vertices_98) then 4 else
  if p.val = (true, vertices_418) then 14 else
  if p.val = (true, vertices_578) then 5 else
  if p.val = (true, vertices_770) then 6 else
  if p.val = (true, vertices_772) then 7 else
  if p.val = (true, vertices_392) then 8 else
  if p.val = (true, vertices_776) then 9 else
  0
cert_priority
cert_nodeAtPriority_7 0 42 1 266 2 522 530 98 578 770 772 392 776 277 225 339 418 661 453 681 625
cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 7 8 3 790 770 1
cert_row_4 1 0 2 4 8 5 618 42 3
cert_row_4 2 2 6 7 8 1 908 392 3
cert_row_2 3 4 6 7 0 418
cert_rows
cert_pivot_2 3 5 1 0
cert_heightProof 4
cert_coverFacet 0 790
cert_cover_5 0 0 0 1 3 7 274 790 1
cert_coverFacet 1 618
cert_cover_5 1 1 0 2 4 5 42 618 3
cert_coverFacet 2 426
cert_cover_5 2 3 0 2 4 6 42 426 3
cert_coverFacet 3 778
cert_cover_2 3 2 0 7 8 266 778 3
cert_coverFacet 4 594
cert_cover_2 4 3 0 5 8 82 594 3
cert_coverFacet 5 482
cert_cover_5 5 3 0 4 5 6 98 482 3
cert_coverFacet 6 908
cert_cover_5 6 2 1 2 6 7 388 908 1
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_315

end
end BundlePart13

section BundlePart14
/- Source: ProjectionCertificates/P1_000.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P1_000

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [835, 109, 181, 789, 581, 57, 345, 614, 678, 234, 458, 914, 660, 440, 21, 37, 69, 517, 25, 41, 73, 49, 273, 321, 577, 769, 550, 202, 98, 162, 322, 578, 386, 642, 770, 148, 532, 100, 164, 580, 644, 56, 280, 104, 168, 328, 392, 176, 400, 656, 784]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_835, vertices_109, vertices_181, vertices_789, vertices_581, vertices_57, vertices_345, vertices_614, vertices_678, vertices_234, vertices_458, vertices_914, vertices_660, vertices_440] (by decide +kernel)
  polygons := literalFinset [vertices_21, vertices_37, vertices_69, vertices_517, vertices_25, vertices_41, vertices_73, vertices_49, vertices_273, vertices_321, vertices_577, vertices_769, vertices_550, vertices_202, vertices_98, vertices_162, vertices_322, vertices_578, vertices_386, vertices_642, vertices_770, vertices_148, vertices_532, vertices_100, vertices_164, vertices_580, vertices_644, vertices_56, vertices_280, vertices_104, vertices_168, vertices_328, vertices_392, vertices_176, vertices_400, vertices_656, vertices_784] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_835), (false, vertices_109), (false, vertices_181), (false, vertices_789), (false, vertices_581), (false, vertices_57), (false, vertices_345), (true, vertices_550), (true, vertices_202), (true, vertices_98), (true, vertices_162), (true, vertices_386), (true, vertices_642), (true, vertices_644), (true, vertices_168), (true, vertices_392), (true, vertices_400), (true, vertices_656)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 18 15 21 11 22 23 24 25 26
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_835) then 19 else
  if p.val = (false, vertices_109) then 16 else
  if p.val = (false, vertices_181) then 12 else
  if p.val = (false, vertices_789) then 13 else
  if p.val = (false, vertices_581) then 9 else
  if p.val = (false, vertices_57) then 10 else
  if p.val = (false, vertices_345) then 14 else
  if p.val = (true, vertices_550) then 17 else
  if p.val = (true, vertices_202) then 20 else
  if p.val = (true, vertices_98) then 0 else
  if p.val = (true, vertices_162) then 1 else
  if p.val = (true, vertices_386) then 2 else
  if p.val = (true, vertices_642) then 3 else
  if p.val = (true, vertices_644) then 4 else
  if p.val = (true, vertices_168) then 5 else
  if p.val = (true, vertices_392) then 6 else
  if p.val = (true, vertices_400) then 7 else
  if p.val = (true, vertices_656) then 8 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_98), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_162), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_386), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_642), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_644), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_168), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_392), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_400), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_656), by decide +kernel⟩
  | 9 => Sum.inr ⟨(false, vertices_581), by decide +kernel⟩
  | 10 => Sum.inr ⟨(false, vertices_57), by decide +kernel⟩
  | 11 => Sum.inl 3
  | 12 => Sum.inr ⟨(false, vertices_181), by decide +kernel⟩
  | 13 => Sum.inr ⟨(false, vertices_789), by decide +kernel⟩
  | 14 => Sum.inr ⟨(false, vertices_345), by decide +kernel⟩
  | 15 => Sum.inl 1
  | 16 => Sum.inr ⟨(false, vertices_109), by decide +kernel⟩
  | 17 => Sum.inr ⟨(true, vertices_550), by decide +kernel⟩
  | 18 => Sum.inl 0
  | 19 => Sum.inr ⟨(false, vertices_835), by decide +kernel⟩
  | 20 => Sum.inr ⟨(true, vertices_202), by decide +kernel⟩
  | 21 => Sum.inl 2
  | 22 => Sum.inl 4
  | 23 => Sum.inl 5
  | 24 => Sum.inl 6
  | 25 => Sum.inl 7
  | 26 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 2 6 5 202
cert_row_4 1 3 4 6 7 2 440 176 3
cert_row_4 2 0 6 7 8 3 914 386 3
cert_row_2 3 1 4 8 0 550
cert_rows
cert_pivot_2 5 2 3 0
cert_heightProof 4
cert_coverFacet 0 614
cert_cover_5 0 3 0 1 4 5 550 614 3
cert_coverFacet 1 678
cert_cover_5 1 3 0 1 4 6 550 678 3
cert_coverFacet 2 234
cert_cover_5 2 0 0 2 4 5 202 234 2
cert_coverFacet 3 458
cert_cover_5 3 0 0 2 5 7 202 458 3
cert_coverFacet 4 914
cert_cover_5 4 2 0 3 6 7 386 914 1
cert_coverFacet 5 660
cert_cover_2 5 3 1 6 8 148 660 3
cert_coverFacet 6 440
cert_cover_5 6 1 2 3 4 6 56 440 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P1_000

end
end BundlePart14

section BundlePart15
/- Source: ProjectionCertificates/P1_002.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P1_002

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [899, 357, 677, 389, 841, 625, 158, 398, 602, 778, 690, 316, 180, 376, 37, 133, 261, 97, 545, 321, 577, 385, 641, 769, 142, 26, 266, 522, 146, 530, 386, 642, 770, 28, 268, 52, 148, 164, 292, 388, 312, 88, 328, 584, 776, 112, 176, 560, 592, 352, 672]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_899, vertices_357, vertices_677, vertices_389, vertices_841, vertices_625, vertices_158, vertices_398, vertices_602, vertices_778, vertices_690, vertices_316, vertices_180, vertices_376] (by decide +kernel)
  polygons := literalFinset [vertices_37, vertices_133, vertices_261, vertices_97, vertices_545, vertices_321, vertices_577, vertices_385, vertices_641, vertices_769, vertices_142, vertices_26, vertices_266, vertices_522, vertices_146, vertices_530, vertices_386, vertices_642, vertices_770, vertices_28, vertices_268, vertices_52, vertices_148, vertices_164, vertices_292, vertices_388, vertices_312, vertices_88, vertices_328, vertices_584, vertices_776, vertices_112, vertices_176, vertices_560, vertices_592, vertices_352, vertices_672] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_899), (false, vertices_357), (false, vertices_677), (false, vertices_389), (false, vertices_841), (false, vertices_625), (true, vertices_142), (true, vertices_26), (true, vertices_266), (true, vertices_522), (true, vertices_146), (true, vertices_530), (true, vertices_28), (true, vertices_268), (true, vertices_52), (true, vertices_148), (true, vertices_312), (true, vertices_88), (true, vertices_176)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 12 15 18 21 23 24 25 26 27
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_899) then 13 else
  if p.val = (false, vertices_357) then 16 else
  if p.val = (false, vertices_677) then 17 else
  if p.val = (false, vertices_389) then 11 else
  if p.val = (false, vertices_841) then 19 else
  if p.val = (false, vertices_625) then 22 else
  if p.val = (true, vertices_142) then 14 else
  if p.val = (true, vertices_26) then 0 else
  if p.val = (true, vertices_266) then 1 else
  if p.val = (true, vertices_522) then 2 else
  if p.val = (true, vertices_146) then 3 else
  if p.val = (true, vertices_530) then 4 else
  if p.val = (true, vertices_28) then 5 else
  if p.val = (true, vertices_268) then 6 else
  if p.val = (true, vertices_52) then 7 else
  if p.val = (true, vertices_148) then 8 else
  if p.val = (true, vertices_312) then 20 else
  if p.val = (true, vertices_88) then 9 else
  if p.val = (true, vertices_176) then 10 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_26), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_266), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_522), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_146), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_530), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_28), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_268), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_52), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_148), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_88), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_176), by decide +kernel⟩
  | 11 => Sum.inr ⟨(false, vertices_389), by decide +kernel⟩
  | 12 => Sum.inl 0
  | 13 => Sum.inr ⟨(false, vertices_899), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_142), by decide +kernel⟩
  | 15 => Sum.inl 1
  | 16 => Sum.inr ⟨(false, vertices_357), by decide +kernel⟩
  | 17 => Sum.inr ⟨(false, vertices_677), by decide +kernel⟩
  | 18 => Sum.inl 2
  | 19 => Sum.inr ⟨(false, vertices_841), by decide +kernel⟩
  | 20 => Sum.inr ⟨(true, vertices_312), by decide +kernel⟩
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
cert_row_4 0 0 2 3 8 5 602 26 3
cert_row_4 1 0 3 4 6 8 690 146 2
cert_row_2 2 1 2 6 0 142
cert_row_2 3 3 4 7 2 312
cert_rows
cert_pivot_2 5 8 0 2
cert_heightProof 4
cert_coverFacet 0 158
cert_cover_5 0 2 0 1 2 3 142 158 3
cert_coverFacet 1 398
cert_cover_5 1 2 0 1 2 7 142 398 3
cert_coverFacet 2 602
cert_cover_5 2 0 0 2 3 5 26 602 3
cert_coverFacet 3 778
cert_cover_2 3 2 0 7 8 266 778 3
cert_coverFacet 4 690
cert_cover_5 4 1 0 3 4 6 146 690 2
cert_coverFacet 5 316
cert_cover_5 5 3 1 2 3 4 28 316 3
cert_coverFacet 6 180
cert_cover_2 6 3 1 4 6 52 180 3
cert_coverFacet 7 376
cert_cover_5 7 3 2 3 4 5 312 376 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P1_002

end
end BundlePart15

section BundlePart16
/- Source: ProjectionCertificates/P1_004.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P1_004

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [659, 333, 601, 425, 649, 465, 118, 406, 422, 682, 626, 620, 300, 340, 73, 137, 265, 521, 81, 145, 529, 321, 385, 641, 22, 38, 390, 114, 146, 530, 162, 546, 642, 44, 76, 268, 84, 276, 100, 292, 324, 168, 296, 552, 584, 648, 336, 592, 400, 608, 416]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_659, vertices_333, vertices_601, vertices_425, vertices_649, vertices_465, vertices_118, vertices_406, vertices_422, vertices_682, vertices_626, vertices_620, vertices_300, vertices_340] (by decide +kernel)
  polygons := literalFinset [vertices_73, vertices_137, vertices_265, vertices_521, vertices_81, vertices_145, vertices_529, vertices_321, vertices_385, vertices_641, vertices_22, vertices_38, vertices_390, vertices_114, vertices_146, vertices_530, vertices_162, vertices_546, vertices_642, vertices_44, vertices_76, vertices_268, vertices_84, vertices_276, vertices_100, vertices_292, vertices_324, vertices_168, vertices_296, vertices_552, vertices_584, vertices_648, vertices_336, vertices_592, vertices_400, vertices_608, vertices_416] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_659), (false, vertices_333), (false, vertices_601), (false, vertices_425), (false, vertices_649), (false, vertices_465), (true, vertices_22), (true, vertices_38), (true, vertices_390), (true, vertices_114), (true, vertices_162), (true, vertices_546), (true, vertices_44), (true, vertices_84), (true, vertices_276), (true, vertices_100), (true, vertices_292), (true, vertices_552), (true, vertices_608)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 12 18 21 23 24 25 26 27
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_659) then 16 else
  if p.val = (false, vertices_333) then 13 else
  if p.val = (false, vertices_601) then 19 else
  if p.val = (false, vertices_425) then 20 else
  if p.val = (false, vertices_649) then 11 else
  if p.val = (false, vertices_465) then 22 else
  if p.val = (true, vertices_22) then 0 else
  if p.val = (true, vertices_38) then 1 else
  if p.val = (true, vertices_390) then 14 else
  if p.val = (true, vertices_114) then 17 else
  if p.val = (true, vertices_162) then 2 else
  if p.val = (true, vertices_546) then 3 else
  if p.val = (true, vertices_44) then 4 else
  if p.val = (true, vertices_84) then 5 else
  if p.val = (true, vertices_276) then 6 else
  if p.val = (true, vertices_100) then 7 else
  if p.val = (true, vertices_292) then 8 else
  if p.val = (true, vertices_552) then 9 else
  if p.val = (true, vertices_608) then 10 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_22), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_38), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_162), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_546), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_44), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_84), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_276), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_100), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_292), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_552), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_608), by decide +kernel⟩
  | 11 => Sum.inr ⟨(false, vertices_649), by decide +kernel⟩
  | 12 => Sum.inl 1
  | 13 => Sum.inr ⟨(false, vertices_333), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_390), by decide +kernel⟩
  | 15 => Sum.inl 0
  | 16 => Sum.inr ⟨(false, vertices_659), by decide +kernel⟩
  | 17 => Sum.inr ⟨(true, vertices_114), by decide +kernel⟩
  | 18 => Sum.inl 2
  | 19 => Sum.inr ⟨(false, vertices_601), by decide +kernel⟩
  | 20 => Sum.inr ⟨(false, vertices_425), by decide +kernel⟩
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
cert_row_2 0 0 4 5 3 114
cert_row_4 1 1 2 4 8 5 620 44 3
cert_row_4 2 0 4 6 8 2 682 162 3
cert_row_2 3 1 6 7 0 390
cert_rows
cert_pivot_2 3 5 2 0
cert_heightProof 4
cert_coverFacet 0 118
cert_cover_5 0 0 0 1 3 4 22 118 3
cert_coverFacet 1 406
cert_cover_5 1 3 0 1 3 6 22 406 3
cert_coverFacet 2 422
cert_cover_5 2 3 0 1 4 6 38 422 3
cert_coverFacet 3 682
cert_cover_5 3 2 0 2 4 6 162 682 1
cert_coverFacet 4 626
cert_cover_5 4 0 0 3 4 8 114 626 3
cert_coverFacet 5 620
cert_cover_5 5 1 1 2 4 5 44 620 3
cert_coverFacet 6 300
cert_cover_2 6 2 1 4 7 44 300 3
cert_coverFacet 7 340
cert_cover_2 7 3 1 5 7 84 340 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P1_004

end
end BundlePart16

section BundlePart17
/- Source: ProjectionCertificates/P2_000.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P2_000

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [279, 91, 395, 213, 901, 233, 122, 298, 818, 628, 788, 740, 936, 11, 19, 259, 21, 133, 261, 73, 137, 81, 193, 385, 90, 42, 266, 50, 274, 290, 84, 276, 532, 612, 196, 644, 772, 104, 168, 296, 392, 112, 560, 784, 224, 672, 800, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_279, vertices_91, vertices_395, vertices_213, vertices_901, vertices_233, vertices_122, vertices_298, vertices_818, vertices_628, vertices_788, vertices_740, vertices_936] (by decide +kernel)
  polygons := literalFinset [vertices_11, vertices_19, vertices_259, vertices_21, vertices_133, vertices_261, vertices_73, vertices_137, vertices_81, vertices_193, vertices_385, vertices_90, vertices_42, vertices_266, vertices_50, vertices_274, vertices_290, vertices_84, vertices_276, vertices_532, vertices_612, vertices_196, vertices_644, vertices_772, vertices_104, vertices_168, vertices_296, vertices_392, vertices_112, vertices_560, vertices_784, vertices_224, vertices_672, vertices_800, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_279), (false, vertices_91), (false, vertices_395), (false, vertices_213), (false, vertices_901), (false, vertices_233), (true, vertices_42), (true, vertices_50), (true, vertices_290), (true, vertices_532), (true, vertices_612), (true, vertices_296), (true, vertices_112), (true, vertices_560), (true, vertices_784), (true, vertices_672), (true, vertices_800)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 10 18 14 16 21 22 23 24 25
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_279) then 11 else
  if p.val = (false, vertices_91) then 13 else
  if p.val = (false, vertices_395) then 12 else
  if p.val = (false, vertices_213) then 17 else
  if p.val = (false, vertices_901) then 19 else
  if p.val = (false, vertices_233) then 15 else
  if p.val = (true, vertices_42) then 0 else
  if p.val = (true, vertices_50) then 1 else
  if p.val = (true, vertices_290) then 2 else
  if p.val = (true, vertices_532) then 3 else
  if p.val = (true, vertices_612) then 20 else
  if p.val = (true, vertices_296) then 4 else
  if p.val = (true, vertices_112) then 5 else
  if p.val = (true, vertices_560) then 6 else
  if p.val = (true, vertices_784) then 7 else
  if p.val = (true, vertices_672) then 8 else
  if p.val = (true, vertices_800) then 9 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_42), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_50), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_290), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_532), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_296), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_112), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_560), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_784), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_672), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_800), by decide +kernel⟩
  | 10 => Sum.inl 0
  | 11 => Sum.inr ⟨(false, vertices_279), by decide +kernel⟩
  | 12 => Sum.inr ⟨(false, vertices_395), by decide +kernel⟩
  | 13 => Sum.inr ⟨(false, vertices_91), by decide +kernel⟩
  | 14 => Sum.inl 2
  | 15 => Sum.inr ⟨(false, vertices_233), by decide +kernel⟩
  | 16 => Sum.inl 3
  | 17 => Sum.inr ⟨(false, vertices_213), by decide +kernel⟩
  | 18 => Sum.inl 1
  | 19 => Sum.inr ⟨(false, vertices_901), by decide +kernel⟩
  | 20 => Sum.inr ⟨(true, vertices_612), by decide +kernel⟩
  | 21 => Sum.inl 4
  | 22 => Sum.inl 5
  | 23 => Sum.inl 6
  | 24 => Sum.inl 7
  | 25 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 2 4 7 8 6 936 296 3
cert_row_4 1 0 3 4 8 7 818 50 3
cert_row_2 2 2 3 5 0 90
cert_row_2 3 4 5 8 1 612
cert_rows
cert_pivot_2 6 7 0 1
cert_heightProof 4
cert_coverFacet 0 122
cert_cover_5 0 2 0 2 3 4 90 122 3
cert_coverFacet 1 298
cert_cover_2 1 2 0 4 7 42 298 3
cert_coverFacet 2 818
cert_cover_5 2 1 0 3 4 7 50 818 3
cert_coverFacet 3 628
cert_cover_5 3 3 1 3 4 5 84 628 2
cert_coverFacet 4 788
cert_cover_2 4 3 1 7 8 276 788 3
cert_coverFacet 5 740
cert_cover_5 5 3 1 4 5 6 612 740 3
cert_coverFacet 6 936
cert_cover_5 6 0 2 4 6 7 168 936 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P2_000

end
end BundlePart17

section BundlePart18
/- Source: ProjectionCertificates/P2_001.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P2_001

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [563, 789, 905, 433, 737, 334, 782, 118, 534, 714, 610, 372, 488, 49, 273, 529, 161, 545, 385, 641, 769, 270, 22, 70, 518, 74, 522, 50, 530, 98, 546, 578, 116, 276, 532, 324, 772, 200, 328, 392, 648, 776, 304, 224, 352, 608, 416, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_563, vertices_789, vertices_905, vertices_433, vertices_737, vertices_334, vertices_782, vertices_118, vertices_534, vertices_714, vertices_610, vertices_372, vertices_488] (by decide +kernel)
  polygons := literalFinset [vertices_49, vertices_273, vertices_529, vertices_161, vertices_545, vertices_385, vertices_641, vertices_769, vertices_270, vertices_22, vertices_70, vertices_518, vertices_74, vertices_522, vertices_50, vertices_530, vertices_98, vertices_546, vertices_578, vertices_116, vertices_276, vertices_532, vertices_324, vertices_772, vertices_200, vertices_328, vertices_392, vertices_648, vertices_776, vertices_304, vertices_224, vertices_352, vertices_608, vertices_416, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_563), (false, vertices_789), (false, vertices_905), (false, vertices_433), (false, vertices_737), (true, vertices_270), (true, vertices_22), (true, vertices_70), (true, vertices_518), (true, vertices_74), (true, vertices_522), (true, vertices_98), (true, vertices_578), (true, vertices_116), (true, vertices_324), (true, vertices_200), (true, vertices_328), (true, vertices_352)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 11 14 17 19 21 23 24 25 26
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_563) then 12 else
  if p.val = (false, vertices_789) then 15 else
  if p.val = (false, vertices_905) then 18 else
  if p.val = (false, vertices_433) then 20 else
  if p.val = (false, vertices_737) then 22 else
  if p.val = (true, vertices_270) then 13 else
  if p.val = (true, vertices_22) then 0 else
  if p.val = (true, vertices_70) then 1 else
  if p.val = (true, vertices_518) then 2 else
  if p.val = (true, vertices_74) then 3 else
  if p.val = (true, vertices_522) then 4 else
  if p.val = (true, vertices_98) then 5 else
  if p.val = (true, vertices_578) then 6 else
  if p.val = (true, vertices_116) then 16 else
  if p.val = (true, vertices_324) then 7 else
  if p.val = (true, vertices_200) then 8 else
  if p.val = (true, vertices_328) then 9 else
  if p.val = (true, vertices_352) then 10 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_22), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_70), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_518), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_74), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_522), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_98), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_578), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_324), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_200), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_328), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_352), by decide +kernel⟩
  | 11 => Sum.inl 0
  | 12 => Sum.inr ⟨(false, vertices_563), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_270), by decide +kernel⟩
  | 14 => Sum.inl 1
  | 15 => Sum.inr ⟨(false, vertices_789), by decide +kernel⟩
  | 16 => Sum.inr ⟨(true, vertices_116), by decide +kernel⟩
  | 17 => Sum.inl 2
  | 18 => Sum.inr ⟨(false, vertices_905), by decide +kernel⟩
  | 19 => Sum.inl 3
  | 20 => Sum.inr ⟨(false, vertices_433), by decide +kernel⟩
  | 21 => Sum.inl 4
  | 22 => Sum.inr ⟨(false, vertices_737), by decide +kernel⟩
  | 23 => Sum.inl 5
  | 24 => Sum.inl 6
  | 25 => Sum.inl 7
  | 26 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 2 5 6 8 714 74 3
cert_row_4 1 2 4 5 7 6 488 328 1
cert_row_2 2 1 2 7 0 270
cert_row_2 3 3 4 5 1 116
cert_rows
cert_pivot_2 8 6 0 1
cert_heightProof 4
cert_coverFacet 0 334
cert_cover_5 0 2 0 1 2 5 270 334 3
cert_coverFacet 1 782
cert_cover_5 1 2 0 1 2 8 270 782 3
cert_coverFacet 2 118
cert_cover_5 2 3 0 1 3 4 22 118 3
cert_coverFacet 3 534
cert_cover_2 3 1 0 3 8 22 534 3
cert_coverFacet 4 714
cert_cover_5 4 0 0 2 5 6 74 714 3
cert_coverFacet 5 610
cert_cover_2 5 4 0 5 8 98 610 3
cert_coverFacet 6 372
cert_cover_5 6 3 1 3 4 7 116 372 3
cert_coverFacet 7 488
cert_cover_5 7 1 2 4 5 6 200 488 1
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P2_001

end
end BundlePart18

section BundlePart19
/- Source: ProjectionCertificates/P2_002.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P2_002

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [211, 659, 789, 677, 453, 345, 90, 794, 618, 738, 812, 420, 488, 147, 133, 261, 517, 81, 273, 529, 193, 321, 641, 26, 74, 522, 82, 530, 610, 194, 642, 164, 292, 548, 388, 772, 88, 280, 104, 296, 552, 328, 776, 784, 224, 416, 672, 448]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_211, vertices_659, vertices_789, vertices_677, vertices_453, vertices_345, vertices_90, vertices_794, vertices_618, vertices_738, vertices_812, vertices_420, vertices_488] (by decide +kernel)
  polygons := literalFinset [vertices_147, vertices_133, vertices_261, vertices_517, vertices_81, vertices_273, vertices_529, vertices_193, vertices_321, vertices_641, vertices_26, vertices_74, vertices_522, vertices_82, vertices_530, vertices_610, vertices_194, vertices_642, vertices_164, vertices_292, vertices_548, vertices_388, vertices_772, vertices_88, vertices_280, vertices_104, vertices_296, vertices_552, vertices_328, vertices_776, vertices_784, vertices_224, vertices_416, vertices_672, vertices_448] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_211), (false, vertices_659), (false, vertices_789), (false, vertices_677), (false, vertices_453), (false, vertices_345), (true, vertices_26), (true, vertices_74), (true, vertices_522), (true, vertices_610), (true, vertices_292), (true, vertices_104), (true, vertices_296), (true, vertices_552), (true, vertices_776), (true, vertices_224), (true, vertices_416)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 19 10 14 16 21 22 23 24 25
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_211) then 17 else
  if p.val = (false, vertices_659) then 18 else
  if p.val = (false, vertices_789) then 11 else
  if p.val = (false, vertices_677) then 12 else
  if p.val = (false, vertices_453) then 13 else
  if p.val = (false, vertices_345) then 15 else
  if p.val = (true, vertices_26) then 0 else
  if p.val = (true, vertices_74) then 1 else
  if p.val = (true, vertices_522) then 2 else
  if p.val = (true, vertices_610) then 20 else
  if p.val = (true, vertices_292) then 3 else
  if p.val = (true, vertices_104) then 4 else
  if p.val = (true, vertices_296) then 5 else
  if p.val = (true, vertices_552) then 6 else
  if p.val = (true, vertices_776) then 7 else
  if p.val = (true, vertices_224) then 8 else
  if p.val = (true, vertices_416) then 9 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_26), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_74), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_522), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_292), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_104), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_296), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_552), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_776), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_224), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_416), by decide +kernel⟩
  | 10 => Sum.inl 1
  | 11 => Sum.inr ⟨(false, vertices_789), by decide +kernel⟩
  | 12 => Sum.inr ⟨(false, vertices_677), by decide +kernel⟩
  | 13 => Sum.inr ⟨(false, vertices_453), by decide +kernel⟩
  | 14 => Sum.inl 2
  | 15 => Sum.inr ⟨(false, vertices_345), by decide +kernel⟩
  | 16 => Sum.inl 3
  | 17 => Sum.inr ⟨(false, vertices_211), by decide +kernel⟩
  | 18 => Sum.inr ⟨(false, vertices_659), by decide +kernel⟩
  | 19 => Sum.inl 0
  | 20 => Sum.inr ⟨(true, vertices_610), by decide +kernel⟩
  | 21 => Sum.inl 4
  | 22 => Sum.inl 5
  | 23 => Sum.inl 6
  | 24 => Sum.inl 7
  | 25 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 2 7 8 3 794 522 2
cert_row_4 1 2 4 7 8 1 812 296 3
cert_row_4 2 4 5 6 7 2 488 224 3
cert_row_2 3 4 5 8 0 610
cert_rows
cert_pivot_2 3 1 2 0
cert_heightProof 4
cert_coverFacet 0 90
cert_cover_2 0 2 0 3 5 26 90 3
cert_coverFacet 1 794
cert_cover_5 1 0 0 2 3 7 26 794 3
cert_coverFacet 2 618
cert_cover_5 2 3 0 2 4 5 74 618 2
cert_coverFacet 3 738
cert_cover_5 3 3 0 4 5 6 610 738 3
cert_coverFacet 4 812
cert_cover_5 4 1 1 2 4 7 292 812 1
cert_coverFacet 5 420
cert_cover_2 5 4 1 6 7 164 420 3
cert_coverFacet 6 488
cert_cover_5 6 2 2 4 5 6 104 488 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P2_002

end
end BundlePart19

section BundlePart20
/- Source: ProjectionCertificates/P2_003.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P2_003

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [611, 805, 409, 241, 849, 417, 654, 678, 218, 602, 226, 796, 428, 81, 145, 273, 97, 161, 289, 545, 577, 385, 769, 646, 90, 138, 522, 98, 162, 546, 194, 578, 140, 268, 524, 164, 292, 548, 772, 152, 280, 536, 392, 208, 592, 784, 224, 416]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_611, vertices_805, vertices_409, vertices_241, vertices_849, vertices_417, vertices_654, vertices_678, vertices_218, vertices_602, vertices_226, vertices_796, vertices_428] (by decide +kernel)
  polygons := literalFinset [vertices_81, vertices_145, vertices_273, vertices_97, vertices_161, vertices_289, vertices_545, vertices_577, vertices_385, vertices_769, vertices_646, vertices_90, vertices_138, vertices_522, vertices_98, vertices_162, vertices_546, vertices_194, vertices_578, vertices_140, vertices_268, vertices_524, vertices_164, vertices_292, vertices_548, vertices_772, vertices_152, vertices_280, vertices_536, vertices_392, vertices_208, vertices_592, vertices_784, vertices_224, vertices_416] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_611), (false, vertices_805), (false, vertices_409), (false, vertices_241), (false, vertices_849), (false, vertices_417), (true, vertices_646), (true, vertices_90), (true, vertices_138), (true, vertices_522), (true, vertices_162), (true, vertices_194), (true, vertices_140), (true, vertices_268), (true, vertices_524), (true, vertices_164), (true, vertices_536)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 13 10 16 18 21 22 23 24 25
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_611) then 14 else
  if p.val = (false, vertices_805) then 11 else
  if p.val = (false, vertices_409) then 17 else
  if p.val = (false, vertices_241) then 19 else
  if p.val = (false, vertices_849) then 20 else
  if p.val = (false, vertices_417) then 9 else
  if p.val = (true, vertices_646) then 12 else
  if p.val = (true, vertices_90) then 15 else
  if p.val = (true, vertices_138) then 0 else
  if p.val = (true, vertices_522) then 1 else
  if p.val = (true, vertices_162) then 2 else
  if p.val = (true, vertices_194) then 3 else
  if p.val = (true, vertices_140) then 4 else
  if p.val = (true, vertices_268) then 5 else
  if p.val = (true, vertices_524) then 6 else
  if p.val = (true, vertices_164) then 7 else
  if p.val = (true, vertices_536) then 8 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_138), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_522), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_162), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_194), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_140), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_268), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_524), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_164), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_536), by decide +kernel⟩
  | 9 => Sum.inr ⟨(false, vertices_417), by decide +kernel⟩
  | 10 => Sum.inl 1
  | 11 => Sum.inr ⟨(false, vertices_805), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_646), by decide +kernel⟩
  | 13 => Sum.inl 0
  | 14 => Sum.inr ⟨(false, vertices_611), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_90), by decide +kernel⟩
  | 16 => Sum.inl 2
  | 17 => Sum.inr ⟨(false, vertices_409), by decide +kernel⟩
  | 18 => Sum.inl 3
  | 19 => Sum.inr ⟨(false, vertices_241), by decide +kernel⟩
  | 20 => Sum.inr ⟨(false, vertices_849), by decide +kernel⟩
  | 21 => Sum.inl 4
  | 22 => Sum.inl 5
  | 23 => Sum.inl 6
  | 24 => Sum.inl 7
  | 25 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 1 2 6 7 4 428 140 3
cert_row_4 1 1 2 3 8 7 796 524 2
cert_row_2 2 0 6 8 1 646
cert_row_2 3 2 3 5 0 90
cert_rows
cert_pivot_2 4 7 1 0
cert_heightProof 4
cert_coverFacet 0 654
cert_cover_5 0 2 0 1 2 6 646 654 2
cert_coverFacet 1 678
cert_cover_5 1 2 0 1 4 6 646 678 2
cert_coverFacet 2 218
cert_cover_5 2 3 0 2 3 6 90 218 3
cert_coverFacet 3 602
cert_cover_5 3 3 0 2 3 8 90 602 3
cert_coverFacet 4 226
cert_cover_2 4 4 0 5 6 98 226 3
cert_coverFacet 5 796
cert_cover_5 5 1 1 2 3 7 268 796 2
cert_coverFacet 6 428
cert_cover_5 6 0 1 2 4 6 140 428 2
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P2_003

end
end BundlePart20

section BundlePart21
/- Source: ProjectionCertificates/R_m12e11q1_0002.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m12e11q1_0002

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [775, 651, 419, 233, 841, 369, 662, 390, 436, 852, 632, 696, 131, 259, 515, 73, 137, 521, 97, 161, 289, 321, 769, 134, 262, 518, 386, 642, 148, 276, 532, 388, 772, 568, 104, 168, 584, 648, 112, 176, 304, 336, 592, 656, 416, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_775, vertices_651, vertices_419, vertices_233, vertices_841, vertices_369, vertices_662, vertices_390, vertices_436, vertices_852, vertices_632, vertices_696] (by decide +kernel)
  polygons := literalFinset [vertices_131, vertices_259, vertices_515, vertices_73, vertices_137, vertices_521, vertices_97, vertices_161, vertices_289, vertices_321, vertices_769, vertices_134, vertices_262, vertices_518, vertices_386, vertices_642, vertices_148, vertices_276, vertices_532, vertices_388, vertices_772, vertices_568, vertices_104, vertices_168, vertices_584, vertices_648, vertices_112, vertices_176, vertices_304, vertices_336, vertices_592, vertices_656, vertices_416, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_775), (false, vertices_651), (false, vertices_419), (false, vertices_233), (false, vertices_841), (false, vertices_369), (true, vertices_134), (true, vertices_148), (true, vertices_276), (true, vertices_532), (true, vertices_388), (true, vertices_568), (true, vertices_176), (true, vertices_592), (true, vertices_656)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 8 12 13 17 19 20 21 22 23
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_775) then 9 else
  if p.val = (false, vertices_651) then 10 else
  if p.val = (false, vertices_419) then 11 else
  if p.val = (false, vertices_233) then 14 else
  if p.val = (false, vertices_841) then 15 else
  if p.val = (false, vertices_369) then 18 else
  if p.val = (true, vertices_134) then 0 else
  if p.val = (true, vertices_148) then 1 else
  if p.val = (true, vertices_276) then 2 else
  if p.val = (true, vertices_532) then 3 else
  if p.val = (true, vertices_388) then 4 else
  if p.val = (true, vertices_568) then 16 else
  if p.val = (true, vertices_176) then 5 else
  if p.val = (true, vertices_592) then 6 else
  if p.val = (true, vertices_656) then 7 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_134), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_148), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_276), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_532), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_388), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_176), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_592), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_656), by decide +kernel⟩
  | 8 => Sum.inl 0
  | 9 => Sum.inr ⟨(false, vertices_775), by decide +kernel⟩
  | 10 => Sum.inr ⟨(false, vertices_651), by decide +kernel⟩
  | 11 => Sum.inr ⟨(false, vertices_419), by decide +kernel⟩
  | 12 => Sum.inl 1
  | 13 => Sum.inl 2
  | 14 => Sum.inr ⟨(false, vertices_233), by decide +kernel⟩
  | 15 => Sum.inr ⟨(false, vertices_841), by decide +kernel⟩
  | 16 => Sum.inr ⟨(true, vertices_568), by decide +kernel⟩
  | 17 => Sum.inl 3
  | 18 => Sum.inr ⟨(false, vertices_369), by decide +kernel⟩
  | 19 => Sum.inl 4
  | 20 => Sum.inl 5
  | 21 => Sum.inl 6
  | 22 => Sum.inl 7
  | 23 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 2 3 4 8 568
cert_row_4 1 0 1 3 6 8 662 134 2
cert_row_4 2 1 3 4 6 7 436 148 2
cert_row_4 3 1 3 5 7 8 852 276 2
cert_rows
cert_pivot_2 2 0 4 1
cert_heightProof 4
cert_coverFacet 0 662
cert_cover_5 0 1 0 1 3 6 134 662 2
cert_coverFacet 1 390
cert_cover_2 1 1 0 6 7 134 390 3
cert_coverFacet 2 436
cert_cover_5 2 2 1 3 4 6 148 436 2
cert_coverFacet 3 852
cert_cover_5 3 3 1 3 5 7 276 852 2
cert_coverFacet 4 632
cert_cover_5 4 0 2 3 4 5 568 632 3
cert_coverFacet 5 696
cert_cover_5 5 0 2 3 4 6 568 696 3
cert_coveringFacets
cert_coveringProof_6
cert_certificate 4 6
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m12e11q1_0002

end
end BundlePart21

section BundlePart22
/- Source: ProjectionCertificates/R_m13e10q0_0019.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m13e10q0_0019

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [395, 595, 147, 803, 301, 217, 617, 902, 658, 236, 396, 724, 868, 19, 131, 259, 515, 41, 73, 137, 265, 81, 145, 289, 545, 577, 146, 530, 386, 642, 770, 44, 140, 268, 100, 292, 196, 580, 388, 644, 772, 104, 200, 392, 208, 592, 656, 608, 800]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_395, vertices_595, vertices_147, vertices_803, vertices_301, vertices_217, vertices_617, vertices_902, vertices_658, vertices_236, vertices_396, vertices_724, vertices_868] (by decide +kernel)
  polygons := literalFinset [vertices_19, vertices_131, vertices_259, vertices_515, vertices_41, vertices_73, vertices_137, vertices_265, vertices_81, vertices_145, vertices_289, vertices_545, vertices_577, vertices_146, vertices_530, vertices_386, vertices_642, vertices_770, vertices_44, vertices_140, vertices_268, vertices_100, vertices_292, vertices_196, vertices_580, vertices_388, vertices_644, vertices_772, vertices_104, vertices_200, vertices_392, vertices_208, vertices_592, vertices_656, vertices_608, vertices_800] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_395), (false, vertices_595), (false, vertices_147), (false, vertices_803), (false, vertices_301), (false, vertices_217), (false, vertices_617), (true, vertices_642), (true, vertices_140), (true, vertices_100), (true, vertices_196), (true, vertices_580), (true, vertices_388), (true, vertices_644), (true, vertices_772), (true, vertices_656)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 10 14 16 19 20 21 22 23 24
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_395) then 11 else
  if p.val = (false, vertices_595) then 12 else
  if p.val = (false, vertices_147) then 0 else
  if p.val = (false, vertices_803) then 13 else
  if p.val = (false, vertices_301) then 15 else
  if p.val = (false, vertices_217) then 17 else
  if p.val = (false, vertices_617) then 18 else
  if p.val = (true, vertices_642) then 1 else
  if p.val = (true, vertices_140) then 2 else
  if p.val = (true, vertices_100) then 3 else
  if p.val = (true, vertices_196) then 4 else
  if p.val = (true, vertices_580) then 5 else
  if p.val = (true, vertices_388) then 6 else
  if p.val = (true, vertices_644) then 7 else
  if p.val = (true, vertices_772) then 8 else
  if p.val = (true, vertices_656) then 9 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_147), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_642), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_140), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_100), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_196), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_580), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_388), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_644), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_772), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_656), by decide +kernel⟩
  | 10 => Sum.inl 0
  | 11 => Sum.inr ⟨(false, vertices_395), by decide +kernel⟩
  | 12 => Sum.inr ⟨(false, vertices_595), by decide +kernel⟩
  | 13 => Sum.inr ⟨(false, vertices_803), by decide +kernel⟩
  | 14 => Sum.inl 1
  | 15 => Sum.inr ⟨(false, vertices_301), by decide +kernel⟩
  | 16 => Sum.inl 2
  | 17 => Sum.inr ⟨(false, vertices_217), by decide +kernel⟩
  | 18 => Sum.inr ⟨(false, vertices_617), by decide +kernel⟩
  | 19 => Sum.inl 3
  | 20 => Sum.inl 4
  | 21 => Sum.inl 5
  | 22 => Sum.inl 6
  | 23 => Sum.inl 7
  | 24 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 6 7 8 902 386 1
cert_row_4 1 1 2 4 5 6 236 44 3
cert_row_4 2 1 3 5 6 8 724 196 1
cert_row_4 3 1 4 5 7 8 868 100 3
cert_rows
cert_pivot_2 0 2 3 1
cert_heightProof 4
cert_coverFacet 0 902
cert_cover_5 0 0 0 1 6 7 386 902 1
cert_coverFacet 1 658
cert_cover_2 1 3 0 6 8 146 658 3
cert_coverFacet 2 236
cert_cover_5 2 1 1 2 4 5 44 236 3
cert_coverFacet 3 396
cert_cover_2 3 2 1 6 7 140 396 3
cert_coverFacet 4 724
cert_cover_5 4 2 1 3 5 6 196 724 1
cert_coverFacet 5 868
cert_cover_5 5 3 1 4 5 7 100 868 3
cert_coveringFacets
cert_coveringProof_6
cert_certificate 4 6
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m13e10q0_0019

end
end BundlePart22

section BundlePart23
/- Source: ProjectionCertificates/R_m13e10q0_0020.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m13e10q0_0020

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [775, 653, 405, 217, 841, 369, 422, 646, 682, 866, 632, 184, 432, 133, 261, 517, 73, 137, 521, 81, 145, 273, 321, 769, 134, 262, 518, 162, 290, 546, 642, 770, 388, 644, 56, 88, 152, 168, 552, 584, 648, 112, 176, 304, 400, 352, 608, 416, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_775, vertices_653, vertices_405, vertices_217, vertices_841, vertices_369, vertices_422, vertices_646, vertices_682, vertices_866, vertices_632, vertices_184, vertices_432] (by decide +kernel)
  polygons := literalFinset [vertices_133, vertices_261, vertices_517, vertices_73, vertices_137, vertices_521, vertices_81, vertices_145, vertices_273, vertices_321, vertices_769, vertices_134, vertices_262, vertices_518, vertices_162, vertices_290, vertices_546, vertices_642, vertices_770, vertices_388, vertices_644, vertices_56, vertices_88, vertices_152, vertices_168, vertices_552, vertices_584, vertices_648, vertices_112, vertices_176, vertices_304, vertices_400, vertices_352, vertices_608, vertices_416, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_775), (false, vertices_653), (false, vertices_405), (false, vertices_217), (false, vertices_841), (false, vertices_369), (true, vertices_134), (true, vertices_162), (true, vertices_290), (true, vertices_546), (true, vertices_642), (true, vertices_56), (true, vertices_168), (true, vertices_552), (true, vertices_176), (true, vertices_608), (true, vertices_416)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 11 13 16 19 21 22 23 24 25
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_775) then 12 else
  if p.val = (false, vertices_653) then 14 else
  if p.val = (false, vertices_405) then 15 else
  if p.val = (false, vertices_217) then 17 else
  if p.val = (false, vertices_841) then 18 else
  if p.val = (false, vertices_369) then 20 else
  if p.val = (true, vertices_134) then 0 else
  if p.val = (true, vertices_162) then 1 else
  if p.val = (true, vertices_290) then 2 else
  if p.val = (true, vertices_546) then 3 else
  if p.val = (true, vertices_642) then 4 else
  if p.val = (true, vertices_56) then 5 else
  if p.val = (true, vertices_168) then 6 else
  if p.val = (true, vertices_552) then 7 else
  if p.val = (true, vertices_176) then 8 else
  if p.val = (true, vertices_608) then 9 else
  if p.val = (true, vertices_416) then 10 else
  0
cert_priority
cert_nodeAtPriority_59 0 134 1 162 2 290 546 642 56 168 552 176 608 416 775 653 405 217 841 369
cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 4 6 7 422 134 2
cert_row_4 1 0 2 4 6 8 682 162 1
cert_row_4 2 0 4 5 7 8 866 290 2
cert_row_4 3 2 3 4 5 8 632 56 3
cert_rows
cert_pivot_2 1 6 0 2
cert_heightProof 4
cert_coverFacet 0 422
cert_cover_5 0 0 0 1 4 6 134 422 2
cert_coverFacet 1 646
cert_cover_2 1 1 0 6 8 134 646 3
cert_coverFacet 2 682
cert_cover_5 2 1 0 2 4 6 162 682 1
cert_coverFacet 3 866
cert_cover_5 3 2 0 4 5 7 290 866 2
cert_coverFacet 4 632
cert_cover_5 4 3 2 3 4 5 56 632 3
cert_coverFacet 5 184
cert_cover_2 5 3 2 4 6 56 184 3
cert_coverFacet 6 432
cert_cover_2 6 4 3 6 7 176 432 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m13e10q0_0020

end
end BundlePart23

section BundlePart24
/- Source: ProjectionCertificates/R_m13e10q0_0028.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m13e10q0_0028

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [647, 779, 451, 229, 805, 369, 666, 394, 724, 612, 824, 472, 624, 131, 259, 515, 37, 133, 517, 97, 289, 193, 321, 769, 138, 266, 522, 386, 642, 100, 548, 196, 580, 644, 152, 280, 536, 392, 776, 112, 304, 560, 208, 336, 592, 656, 608, 800, 448]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_647, vertices_779, vertices_451, vertices_229, vertices_805, vertices_369, vertices_666, vertices_394, vertices_724, vertices_612, vertices_824, vertices_472, vertices_624] (by decide +kernel)
  polygons := literalFinset [vertices_131, vertices_259, vertices_515, vertices_37, vertices_133, vertices_517, vertices_97, vertices_289, vertices_193, vertices_321, vertices_769, vertices_138, vertices_266, vertices_522, vertices_386, vertices_642, vertices_100, vertices_548, vertices_196, vertices_580, vertices_644, vertices_152, vertices_280, vertices_536, vertices_392, vertices_776, vertices_112, vertices_304, vertices_560, vertices_208, vertices_336, vertices_592, vertices_656, vertices_608, vertices_800, vertices_448] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_647), (false, vertices_779), (false, vertices_451), (false, vertices_229), (false, vertices_805), (false, vertices_369), (true, vertices_138), (true, vertices_580), (true, vertices_152), (true, vertices_280), (true, vertices_536), (true, vertices_392), (true, vertices_560), (true, vertices_208), (true, vertices_592), (true, vertices_656), (true, vertices_608)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 11 15 18 19 21 22 23 24 25
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_647) then 12 else
  if p.val = (false, vertices_779) then 13 else
  if p.val = (false, vertices_451) then 14 else
  if p.val = (false, vertices_229) then 16 else
  if p.val = (false, vertices_805) then 17 else
  if p.val = (false, vertices_369) then 20 else
  if p.val = (true, vertices_138) then 0 else
  if p.val = (true, vertices_580) then 1 else
  if p.val = (true, vertices_152) then 2 else
  if p.val = (true, vertices_280) then 3 else
  if p.val = (true, vertices_536) then 4 else
  if p.val = (true, vertices_392) then 5 else
  if p.val = (true, vertices_560) then 6 else
  if p.val = (true, vertices_208) then 7 else
  if p.val = (true, vertices_592) then 8 else
  if p.val = (true, vertices_656) then 9 else
  if p.val = (true, vertices_608) then 10 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_138), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_580), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_152), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_280), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_536), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_392), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_560), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_208), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_592), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_656), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_608), by decide +kernel⟩
  | 11 => Sum.inl 0
  | 12 => Sum.inr ⟨(false, vertices_647), by decide +kernel⟩
  | 13 => Sum.inr ⟨(false, vertices_779), by decide +kernel⟩
  | 14 => Sum.inr ⟨(false, vertices_451), by decide +kernel⟩
  | 15 => Sum.inl 1
  | 16 => Sum.inr ⟨(false, vertices_229), by decide +kernel⟩
  | 17 => Sum.inr ⟨(false, vertices_805), by decide +kernel⟩
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
cert_row_4 0 0 2 3 6 8 666 138 2
cert_row_4 1 1 3 5 6 8 724 196 1
cert_row_4 2 2 3 4 7 8 824 280 2
cert_row_4 3 2 3 5 6 7 472 152 2
cert_rows
cert_pivot_2 0 1 4 2
cert_heightProof 4
cert_coverFacet 0 666
cert_cover_5 0 0 0 2 3 6 138 666 2
cert_coverFacet 1 394
cert_cover_2 1 2 0 6 7 138 394 3
cert_coverFacet 2 724
cert_cover_5 2 1 1 3 5 6 196 724 1
cert_coverFacet 3 612
cert_cover_2 3 4 1 5 8 100 612 3
cert_coverFacet 4 824
cert_cover_5 4 2 2 3 4 7 280 824 2
cert_coverFacet 5 472
cert_cover_5 5 3 2 3 5 6 152 472 2
cert_coverFacet 6 624
cert_cover_2 6 4 3 5 8 112 624 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m13e10q0_0028

end
end BundlePart24

section BundlePart25
/- Source: ProjectionCertificates/R_m13e10q0_0029.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m13e10q0_0029

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [775, 653, 405, 217, 617, 849, 422, 646, 682, 866, 376, 184, 432, 133, 261, 517, 73, 137, 521, 81, 145, 273, 577, 769, 134, 262, 518, 162, 290, 546, 642, 770, 388, 644, 56, 88, 152, 104, 168, 552, 648, 176, 304, 336, 400, 352, 608, 416, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_775, vertices_653, vertices_405, vertices_217, vertices_617, vertices_849, vertices_422, vertices_646, vertices_682, vertices_866, vertices_376, vertices_184, vertices_432] (by decide +kernel)
  polygons := literalFinset [vertices_133, vertices_261, vertices_517, vertices_73, vertices_137, vertices_521, vertices_81, vertices_145, vertices_273, vertices_577, vertices_769, vertices_134, vertices_262, vertices_518, vertices_162, vertices_290, vertices_546, vertices_642, vertices_770, vertices_388, vertices_644, vertices_56, vertices_88, vertices_152, vertices_104, vertices_168, vertices_552, vertices_648, vertices_176, vertices_304, vertices_336, vertices_400, vertices_352, vertices_608, vertices_416, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_775), (false, vertices_653), (false, vertices_405), (false, vertices_217), (false, vertices_617), (false, vertices_849), (true, vertices_134), (true, vertices_162), (true, vertices_290), (true, vertices_546), (true, vertices_642), (true, vertices_56), (true, vertices_168), (true, vertices_176), (true, vertices_304), (true, vertices_352), (true, vertices_416)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 11 13 16 19 21 22 23 24 25
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_775) then 12 else
  if p.val = (false, vertices_653) then 14 else
  if p.val = (false, vertices_405) then 15 else
  if p.val = (false, vertices_217) then 17 else
  if p.val = (false, vertices_617) then 18 else
  if p.val = (false, vertices_849) then 20 else
  if p.val = (true, vertices_134) then 0 else
  if p.val = (true, vertices_162) then 1 else
  if p.val = (true, vertices_290) then 2 else
  if p.val = (true, vertices_546) then 3 else
  if p.val = (true, vertices_642) then 4 else
  if p.val = (true, vertices_56) then 5 else
  if p.val = (true, vertices_168) then 6 else
  if p.val = (true, vertices_176) then 7 else
  if p.val = (true, vertices_304) then 8 else
  if p.val = (true, vertices_352) then 9 else
  if p.val = (true, vertices_416) then 10 else
  0
cert_priority
cert_nodeAtPriority_59 0 134 1 162 2 290 546 642 56 168 176 304 352 416 775 653 405 217 617 849
cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 4 6 7 422 134 2
cert_row_4 1 0 2 4 6 8 682 162 1
cert_row_4 2 0 4 5 7 8 866 290 2
cert_row_4 3 2 3 4 5 7 376 56 3
cert_rows
cert_pivot_2 1 6 0 2
cert_heightProof 4
cert_coverFacet 0 422
cert_cover_5 0 0 0 1 4 6 134 422 2
cert_coverFacet 1 646
cert_cover_2 1 1 0 6 8 134 646 3
cert_coverFacet 2 682
cert_cover_5 2 1 0 2 4 6 162 682 1
cert_coverFacet 3 866
cert_cover_5 3 2 0 4 5 7 290 866 2
cert_coverFacet 4 376
cert_cover_5 4 3 2 3 4 5 56 376 3
cert_coverFacet 5 184
cert_cover_2 5 3 2 4 6 56 184 3
cert_coverFacet 6 432
cert_cover_2 6 4 3 6 7 176 432 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m13e10q0_0029

end
end BundlePart25

section BundlePart26
/- Source: ProjectionCertificates/R_m13e10q1_0012.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m13e10q1_0012

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [651, 403, 835, 597, 661, 369, 810, 394, 684, 244, 868, 424, 432, 131, 259, 515, 533, 81, 145, 273, 321, 577, 641, 138, 266, 522, 386, 770, 84, 148, 100, 164, 548, 580, 644, 168, 296, 552, 392, 648, 112, 176, 304, 400, 352, 416, 800, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_651, vertices_403, vertices_835, vertices_597, vertices_661, vertices_369, vertices_810, vertices_394, vertices_684, vertices_244, vertices_868, vertices_424, vertices_432] (by decide +kernel)
  polygons := literalFinset [vertices_131, vertices_259, vertices_515, vertices_533, vertices_81, vertices_145, vertices_273, vertices_321, vertices_577, vertices_641, vertices_138, vertices_266, vertices_522, vertices_386, vertices_770, vertices_84, vertices_148, vertices_100, vertices_164, vertices_548, vertices_580, vertices_644, vertices_168, vertices_296, vertices_552, vertices_392, vertices_648, vertices_112, vertices_176, vertices_304, vertices_400, vertices_352, vertices_416, vertices_800, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_651), (false, vertices_403), (false, vertices_835), (false, vertices_597), (false, vertices_661), (false, vertices_369), (true, vertices_266), (true, vertices_100), (true, vertices_164), (true, vertices_548), (true, vertices_168), (true, vertices_296), (true, vertices_552), (true, vertices_392), (true, vertices_176), (true, vertices_416), (true, vertices_800)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 11 15 18 19 21 22 23 24 25
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_651) then 12 else
  if p.val = (false, vertices_403) then 13 else
  if p.val = (false, vertices_835) then 14 else
  if p.val = (false, vertices_597) then 16 else
  if p.val = (false, vertices_661) then 17 else
  if p.val = (false, vertices_369) then 20 else
  if p.val = (true, vertices_266) then 0 else
  if p.val = (true, vertices_100) then 1 else
  if p.val = (true, vertices_164) then 2 else
  if p.val = (true, vertices_548) then 3 else
  if p.val = (true, vertices_168) then 4 else
  if p.val = (true, vertices_296) then 5 else
  if p.val = (true, vertices_552) then 6 else
  if p.val = (true, vertices_392) then 7 else
  if p.val = (true, vertices_176) then 8 else
  if p.val = (true, vertices_416) then 9 else
  if p.val = (true, vertices_800) then 10 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_266), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_100), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_164), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_548), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_168), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_296), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_552), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_392), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_176), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_416), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_800), by decide +kernel⟩
  | 11 => Sum.inl 0
  | 12 => Sum.inr ⟨(false, vertices_651), by decide +kernel⟩
  | 13 => Sum.inr ⟨(false, vertices_403), by decide +kernel⟩
  | 14 => Sum.inr ⟨(false, vertices_835), by decide +kernel⟩
  | 15 => Sum.inl 1
  | 16 => Sum.inr ⟨(false, vertices_597), by decide +kernel⟩
  | 17 => Sum.inr ⟨(false, vertices_661), by decide +kernel⟩
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
cert_row_4 0 0 2 4 7 8 810 266 2
cert_row_4 1 1 2 4 6 8 684 164 1
cert_row_4 2 1 3 4 5 6 244 84 2
cert_row_4 3 1 4 5 7 8 868 100 3
cert_rows
cert_pivot_2 0 2 3 1
cert_heightProof 4
cert_coverFacet 0 810
cert_cover_5 0 0 0 2 4 7 266 810 2
cert_coverFacet 1 394
cert_cover_2 1 2 0 6 7 138 394 3
cert_coverFacet 2 684
cert_cover_5 2 1 1 2 4 6 164 684 1
cert_coverFacet 3 244
cert_cover_5 3 2 1 3 4 5 84 244 2
cert_coverFacet 4 868
cert_cover_5 4 3 1 4 5 7 100 868 3
cert_coverFacet 5 424
cert_cover_2 5 4 2 6 7 168 424 3
cert_coverFacet 6 432
cert_cover_2 6 4 3 6 7 176 432 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m13e10q1_0012

end
end BundlePart26

section BundlePart27
/- Source: ProjectionCertificates/R_m13e10q1_0033.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m13e10q1_0033

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [647, 341, 405, 613, 681, 241, 398, 838, 810, 650, 424, 880, 432, 277, 69, 133, 517, 81, 145, 97, 161, 545, 641, 134, 262, 518, 138, 266, 522, 642, 770, 324, 580, 388, 168, 296, 552, 392, 648, 112, 176, 304, 336, 400, 608, 416, 800, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_647, vertices_341, vertices_405, vertices_613, vertices_681, vertices_241, vertices_398, vertices_838, vertices_810, vertices_650, vertices_424, vertices_880, vertices_432] (by decide +kernel)
  polygons := literalFinset [vertices_277, vertices_69, vertices_133, vertices_517, vertices_81, vertices_145, vertices_97, vertices_161, vertices_545, vertices_641, vertices_134, vertices_262, vertices_518, vertices_138, vertices_266, vertices_522, vertices_642, vertices_770, vertices_324, vertices_580, vertices_388, vertices_168, vertices_296, vertices_552, vertices_392, vertices_648, vertices_112, vertices_176, vertices_304, vertices_336, vertices_400, vertices_608, vertices_416, vertices_800, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_647), (false, vertices_341), (false, vertices_405), (false, vertices_613), (false, vertices_681), (false, vertices_241), (true, vertices_262), (true, vertices_138), (true, vertices_266), (true, vertices_522), (true, vertices_770), (true, vertices_296), (true, vertices_392), (true, vertices_304), (true, vertices_416), (true, vertices_800), (true, vertices_832)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 11 13 17 19 21 22 23 24 25
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_647) then 12 else
  if p.val = (false, vertices_341) then 14 else
  if p.val = (false, vertices_405) then 15 else
  if p.val = (false, vertices_613) then 16 else
  if p.val = (false, vertices_681) then 18 else
  if p.val = (false, vertices_241) then 20 else
  if p.val = (true, vertices_262) then 0 else
  if p.val = (true, vertices_138) then 1 else
  if p.val = (true, vertices_266) then 2 else
  if p.val = (true, vertices_522) then 3 else
  if p.val = (true, vertices_770) then 4 else
  if p.val = (true, vertices_296) then 5 else
  if p.val = (true, vertices_392) then 6 else
  if p.val = (true, vertices_304) then 7 else
  if p.val = (true, vertices_416) then 8 else
  if p.val = (true, vertices_800) then 9 else
  if p.val = (true, vertices_832) then 10 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_262), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_138), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_266), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_522), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_770), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_296), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_392), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_304), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_416), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_800), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_832), by decide +kernel⟩
  | 11 => Sum.inl 0
  | 12 => Sum.inr ⟨(false, vertices_647), by decide +kernel⟩
  | 13 => Sum.inl 1
  | 14 => Sum.inr ⟨(false, vertices_341), by decide +kernel⟩
  | 15 => Sum.inr ⟨(false, vertices_405), by decide +kernel⟩
  | 16 => Sum.inr ⟨(false, vertices_613), by decide +kernel⟩
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
cert_row_4 0 0 1 2 6 7 398 134 2
cert_row_4 1 0 1 5 7 8 838 262 2
cert_row_4 2 0 2 4 7 8 810 266 2
cert_row_4 3 3 4 5 7 8 880 112 3
cert_rows
cert_pivot_2 6 1 0 3
cert_heightProof 4
cert_coverFacet 0 398
cert_cover_5 0 0 0 1 2 6 134 398 2
cert_coverFacet 1 838
cert_cover_5 1 1 0 1 5 7 262 838 2
cert_coverFacet 2 810
cert_cover_5 2 2 0 2 4 7 266 810 2
cert_coverFacet 3 650
cert_cover_2 3 2 0 6 8 138 650 3
cert_coverFacet 4 424
cert_cover_2 4 4 2 6 7 168 424 3
cert_coverFacet 5 880
cert_cover_5 5 3 3 4 5 7 112 880 3
cert_coverFacet 6 432
cert_cover_2 6 4 3 6 7 176 432 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m13e10q1_0033

end
end BundlePart27

section BundlePart28
/- Source: ProjectionCertificates/R_m13e10q1_0076.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m13e10q1_0076

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [787, 837, 665, 281, 457, 737, 310, 614, 774, 690, 356, 248, 376, 25, 137, 265, 273, 529, 193, 321, 577, 641, 769, 38, 262, 518, 50, 274, 530, 546, 770, 100, 292, 324, 580, 772, 120, 152, 280, 200, 328, 176, 304, 656, 224, 352, 608, 672]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_787, vertices_837, vertices_665, vertices_281, vertices_457, vertices_737, vertices_310, vertices_614, vertices_774, vertices_690, vertices_356, vertices_248, vertices_376] (by decide +kernel)
  polygons := literalFinset [vertices_25, vertices_137, vertices_265, vertices_273, vertices_529, vertices_193, vertices_321, vertices_577, vertices_641, vertices_769, vertices_38, vertices_262, vertices_518, vertices_50, vertices_274, vertices_530, vertices_546, vertices_770, vertices_100, vertices_292, vertices_324, vertices_580, vertices_772, vertices_120, vertices_152, vertices_280, vertices_200, vertices_328, vertices_176, vertices_304, vertices_656, vertices_224, vertices_352, vertices_608, vertices_672] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_787), (false, vertices_837), (false, vertices_665), (false, vertices_281), (false, vertices_457), (false, vertices_737), (true, vertices_38), (true, vertices_262), (true, vertices_518), (true, vertices_50), (true, vertices_546), (true, vertices_100), (true, vertices_292), (true, vertices_120), (true, vertices_176), (true, vertices_304), (true, vertices_352)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 11 13 15 19 20 22 23 24 25
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_787) then 12 else
  if p.val = (false, vertices_837) then 14 else
  if p.val = (false, vertices_665) then 16 else
  if p.val = (false, vertices_281) then 0 else
  if p.val = (false, vertices_457) then 17 else
  if p.val = (false, vertices_737) then 21 else
  if p.val = (true, vertices_38) then 1 else
  if p.val = (true, vertices_262) then 2 else
  if p.val = (true, vertices_518) then 3 else
  if p.val = (true, vertices_50) then 4 else
  if p.val = (true, vertices_546) then 5 else
  if p.val = (true, vertices_100) then 6 else
  if p.val = (true, vertices_292) then 7 else
  if p.val = (true, vertices_120) then 18 else
  if p.val = (true, vertices_176) then 8 else
  if p.val = (true, vertices_304) then 9 else
  if p.val = (true, vertices_352) then 10 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_281), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_38), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_262), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_518), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_50), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_546), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_100), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_292), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_176), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_304), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_352), by decide +kernel⟩
  | 11 => Sum.inl 0
  | 12 => Sum.inr ⟨(false, vertices_787), by decide +kernel⟩
  | 13 => Sum.inl 1
  | 14 => Sum.inr ⟨(false, vertices_837), by decide +kernel⟩
  | 15 => Sum.inl 2
  | 16 => Sum.inr ⟨(false, vertices_665), by decide +kernel⟩
  | 17 => Sum.inr ⟨(false, vertices_457), by decide +kernel⟩
  | 18 => Sum.inr ⟨(true, vertices_120), by decide +kernel⟩
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
cert_row_2 0 2 3 4 5 120
cert_row_4 1 0 1 3 4 7 310 38 2
cert_row_4 2 0 1 4 5 8 614 38 3
cert_row_4 3 0 3 4 6 8 690 50 3
cert_rows
cert_pivot_2 2 7 1 0
cert_heightProof 4
cert_coverFacet 0 310
cert_cover_5 0 1 0 1 3 4 38 310 2
cert_coverFacet 1 614
cert_cover_5 1 2 0 1 4 5 38 614 3
cert_coverFacet 2 774
cert_cover_2 2 1 0 7 8 262 774 3
cert_coverFacet 3 690
cert_cover_5 3 3 0 3 4 6 50 690 3
cert_coverFacet 4 356
cert_cover_2 4 4 1 5 7 100 356 3
cert_coverFacet 5 248
cert_cover_5 5 0 2 3 4 6 120 248 3
cert_coverFacet 6 376
cert_cover_5 6 0 2 3 4 7 120 376 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m13e10q1_0076

end
end BundlePart28

section BundlePart29
/- Source: ProjectionCertificates/R_m13e10q1_0085.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m13e10q1_0085

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [395, 651, 595, 355, 613, 809, 662, 210, 450, 684, 244, 596, 488, 139, 67, 259, 515, 265, 521, 97, 289, 545, 577, 82, 146, 530, 194, 322, 386, 642, 84, 148, 532, 100, 164, 548, 580, 644, 168, 296, 552, 392, 648, 208, 592, 224, 352, 448]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_395, vertices_651, vertices_595, vertices_355, vertices_613, vertices_809, vertices_662, vertices_210, vertices_450, vertices_684, vertices_244, vertices_596, vertices_488] (by decide +kernel)
  polygons := literalFinset [vertices_139, vertices_67, vertices_259, vertices_515, vertices_265, vertices_521, vertices_97, vertices_289, vertices_545, vertices_577, vertices_82, vertices_146, vertices_530, vertices_194, vertices_322, vertices_386, vertices_642, vertices_84, vertices_148, vertices_532, vertices_100, vertices_164, vertices_548, vertices_580, vertices_644, vertices_168, vertices_296, vertices_552, vertices_392, vertices_648, vertices_208, vertices_592, vertices_224, vertices_352, vertices_448] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_395), (false, vertices_651), (false, vertices_595), (false, vertices_355), (false, vertices_613), (false, vertices_809), (true, vertices_146), (true, vertices_194), (true, vertices_84), (true, vertices_148), (true, vertices_532), (true, vertices_164), (true, vertices_644), (true, vertices_168), (true, vertices_208), (true, vertices_224), (true, vertices_448)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 17 11 13 20 21 22 23 24 25
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_395) then 14 else
  if p.val = (false, vertices_651) then 15 else
  if p.val = (false, vertices_595) then 18 else
  if p.val = (false, vertices_355) then 19 else
  if p.val = (false, vertices_613) then 12 else
  if p.val = (false, vertices_809) then 16 else
  if p.val = (true, vertices_146) then 0 else
  if p.val = (true, vertices_194) then 1 else
  if p.val = (true, vertices_84) then 2 else
  if p.val = (true, vertices_148) then 3 else
  if p.val = (true, vertices_532) then 4 else
  if p.val = (true, vertices_164) then 5 else
  if p.val = (true, vertices_644) then 6 else
  if p.val = (true, vertices_168) then 7 else
  if p.val = (true, vertices_208) then 8 else
  if p.val = (true, vertices_224) then 9 else
  if p.val = (true, vertices_448) then 10 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_146), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_194), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_84), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_148), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_532), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_164), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_644), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_168), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_208), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_224), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_448), by decide +kernel⟩
  | 11 => Sum.inl 1
  | 12 => Sum.inr ⟨(false, vertices_613), by decide +kernel⟩
  | 13 => Sum.inl 2
  | 14 => Sum.inr ⟨(false, vertices_395), by decide +kernel⟩
  | 15 => Sum.inr ⟨(false, vertices_651), by decide +kernel⟩
  | 16 => Sum.inr ⟨(false, vertices_809), by decide +kernel⟩
  | 17 => Sum.inl 0
  | 18 => Sum.inr ⟨(false, vertices_595), by decide +kernel⟩
  | 19 => Sum.inr ⟨(false, vertices_355), by decide +kernel⟩
  | 20 => Sum.inl 3
  | 21 => Sum.inl 4
  | 22 => Sum.inl 5
  | 23 => Sum.inl 6
  | 24 => Sum.inl 7
  | 25 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 3 6 8 662 146 1
cert_row_4 1 1 2 4 6 8 684 164 1
cert_row_4 2 1 3 4 5 6 244 84 2
cert_row_4 3 2 4 5 6 7 488 168 2
cert_rows
cert_pivot_2 0 8 1 2
cert_heightProof 4
cert_coverFacet 0 662
cert_cover_5 0 0 0 1 3 6 146 662 1
cert_coverFacet 1 210
cert_cover_2 1 3 0 5 6 82 210 3
cert_coverFacet 2 450
cert_cover_2 2 5 0 6 7 194 450 3
cert_coverFacet 3 684
cert_cover_5 3 1 1 2 4 6 164 684 1
cert_coverFacet 4 244
cert_cover_5 4 2 1 3 4 5 84 244 2
cert_coverFacet 5 596
cert_cover_2 5 3 1 5 8 84 596 3
cert_coverFacet 6 488
cert_cover_5 6 3 2 4 5 6 168 488 2
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m13e10q1_0085

end
end BundlePart29
-- Explicit facial frame witnesses.

-- Public target certificates; internal witness data stays private.
namespace Nonrational.TerminalVerification
open Papers.RationalityTen.ChirotopeDensity.FiniteProjection
open Nonrational.TerminalData
set_option maxRecDepth 100000
set_option maxHeartbeats 0

public theorem projection_0120 : Certifies 120 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_242.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0121 : Certifies 121 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_243.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0122 : Certifies 122 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_244.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0123 : Certifies 123 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_245.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0124 : Certifies 124 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_253.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0125 : Certifies 125 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_254.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0126 : Certifies 126 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_259.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0127 : Certifies 127 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_269.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0128 : Certifies 128 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_272.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0129 : Certifies 129 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_285.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0130 : Certifies 130 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_296.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0131 : Certifies 131 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_299.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0132 : Certifies 132 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_300.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0133 : Certifies 133 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_315.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0134 : Certifies 134 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P1_000.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0135 : Certifies 135 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P1_002.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0136 : Certifies 136 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P1_004.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0137 : Certifies 137 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P2_000.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0138 : Certifies 138 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P2_001.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0139 : Certifies 139 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P2_002.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0140 : Certifies 140 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P2_003.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0141 : Certifies 141 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m12e11q1_0002.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0142 : Certifies 142 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m13e10q0_0019.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0143 : Certifies 143 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m13e10q0_0020.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0144 : Certifies 144 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m13e10q0_0028.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0145 : Certifies 145 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m13e10q0_0029.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0146 : Certifies 146 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m13e10q1_0012.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0147 : Certifies 147 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m13e10q1_0033.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0148 : Certifies 148 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m13e10q1_0076.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0149 : Certifies 149 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m13e10q1_0085.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem certified_B004 (j : Fin 30) :
    Certifies (120 + j.val) := by
  fin_cases j
  · exact projection_0120
  · exact projection_0121
  · exact projection_0122
  · exact projection_0123
  · exact projection_0124
  · exact projection_0125
  · exact projection_0126
  · exact projection_0127
  · exact projection_0128
  · exact projection_0129
  · exact projection_0130
  · exact projection_0131
  · exact projection_0132
  · exact projection_0133
  · exact projection_0134
  · exact projection_0135
  · exact projection_0136
  · exact projection_0137
  · exact projection_0138
  · exact projection_0139
  · exact projection_0140
  · exact projection_0141
  · exact projection_0142
  · exact projection_0143
  · exact projection_0144
  · exact projection_0145
  · exact projection_0146
  · exact projection_0147
  · exact projection_0148
  · exact projection_0149

end Nonrational.TerminalVerification
