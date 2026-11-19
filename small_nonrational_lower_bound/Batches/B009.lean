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
/- Source: ProjectionCertificates/R_m14e10q1_0120.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0120

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [647, 787, 419, 541, 405, 362, 610, 674, 834, 188, 620, 676, 440, 856, 131, 259, 515, 21, 133, 517, 273, 529, 385, 98, 162, 290, 546, 322, 578, 642, 770, 28, 44, 524, 148, 164, 548, 644, 184, 280, 536, 104, 296, 328, 584, 400, 784, 608, 416, 672, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_647, vertices_787, vertices_419, vertices_541, vertices_405, vertices_362, vertices_610, vertices_674, vertices_834, vertices_188, vertices_620, vertices_676, vertices_440, vertices_856] (by decide +kernel)
  polygons := literalFinset [vertices_131, vertices_259, vertices_515, vertices_21, vertices_133, vertices_517, vertices_273, vertices_529, vertices_385, vertices_98, vertices_162, vertices_290, vertices_546, vertices_322, vertices_578, vertices_642, vertices_770, vertices_28, vertices_44, vertices_524, vertices_148, vertices_164, vertices_548, vertices_644, vertices_184, vertices_280, vertices_536, vertices_104, vertices_296, vertices_328, vertices_584, vertices_400, vertices_784, vertices_608, vertices_416, vertices_672, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_647), (false, vertices_787), (false, vertices_419), (false, vertices_541), (false, vertices_405), (true, vertices_98), (true, vertices_546), (true, vertices_322), (true, vertices_578), (true, vertices_44), (true, vertices_164), (true, vertices_548), (true, vertices_184), (true, vertices_280), (true, vertices_104), (true, vertices_296), (true, vertices_328), (true, vertices_584), (true, vertices_608), (true, vertices_672), (true, vertices_832)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 19 22 24 25 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_647) then 16 else
  if p.val = (false, vertices_787) then 17 else
  if p.val = (false, vertices_419) then 18 else
  if p.val = (false, vertices_541) then 20 else
  if p.val = (false, vertices_405) then 21 else
  if p.val = (true, vertices_98) then 0 else
  if p.val = (true, vertices_546) then 1 else
  if p.val = (true, vertices_322) then 2 else
  if p.val = (true, vertices_578) then 3 else
  if p.val = (true, vertices_44) then 4 else
  if p.val = (true, vertices_164) then 5 else
  if p.val = (true, vertices_548) then 6 else
  if p.val = (true, vertices_184) then 23 else
  if p.val = (true, vertices_280) then 7 else
  if p.val = (true, vertices_104) then 8 else
  if p.val = (true, vertices_296) then 9 else
  if p.val = (true, vertices_328) then 10 else
  if p.val = (true, vertices_584) then 11 else
  if p.val = (true, vertices_608) then 12 else
  if p.val = (true, vertices_672) then 13 else
  if p.val = (true, vertices_832) then 14 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_98), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_546), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_322), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_578), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_44), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_164), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_548), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_280), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_104), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_296), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_328), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_584), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_608), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_672), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_832), by decide +kernel⟩
  | 15 => Sum.inl 0
  | 16 => Sum.inr ⟨(false, vertices_647), by decide +kernel⟩
  | 17 => Sum.inr ⟨(false, vertices_787), by decide +kernel⟩
  | 18 => Sum.inr ⟨(false, vertices_419), by decide +kernel⟩
  | 19 => Sum.inl 1
  | 20 => Sum.inr ⟨(false, vertices_541), by decide +kernel⟩
  | 21 => Sum.inr ⟨(false, vertices_405), by decide +kernel⟩
  | 22 => Sum.inl 2
  | 23 => Sum.inr ⟨(true, vertices_184), by decide +kernel⟩
  | 24 => Sum.inl 3
  | 25 => Sum.inl 4
  | 26 => Sum.inl 5
  | 27 => Sum.inl 6
  | 28 => Sum.inl 7
  | 29 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 2 3 4 6 184
cert_row_4 1 0 2 4 5 7 362 98 1
cert_row_4 2 1 2 4 5 8 620 44 3
cert_row_4 3 2 3 5 7 8 856 280 2
cert_rows
cert_pivot_2 6 0 1 2
cert_heightProof 4
cert_coverFacet 0 362
cert_cover_5 0 1 0 2 4 5 98 362 1
cert_coverFacet 1 610
cert_cover_2 1 4 0 5 8 98 610 3
cert_coverFacet 2 674
cert_cover_2 2 4 0 6 8 162 674 3
cert_coverFacet 3 834
cert_cover_2 3 5 0 7 8 322 834 3
cert_coverFacet 4 188
cert_cover_5 4 0 1 2 3 4 28 188 3
cert_coverFacet 5 620
cert_cover_5 5 2 1 2 4 5 44 620 3
cert_coverFacet 6 676
cert_cover_2 6 4 1 6 8 164 676 3
cert_coverFacet 7 440
cert_cover_5 7 0 2 3 4 7 184 440 3
cert_coverFacet 8 856
cert_cover_5 8 3 2 3 5 7 280 856 2
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0120

end
end BundlePart0

section BundlePart1
/- Source: ProjectionCertificates/R_m14e10q1_0122.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0122

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [327, 583, 541, 405, 345, 617, 662, 422, 682, 866, 408, 664, 360, 424, 71, 21, 261, 517, 25, 73, 521, 273, 321, 577, 134, 262, 518, 162, 290, 546, 322, 578, 642, 148, 532, 388, 152, 280, 536, 104, 168, 296, 552, 328, 392, 648, 400, 656, 352, 608, 416]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_327, vertices_583, vertices_541, vertices_405, vertices_345, vertices_617, vertices_662, vertices_422, vertices_682, vertices_866, vertices_408, vertices_664, vertices_360, vertices_424] (by decide +kernel)
  polygons := literalFinset [vertices_71, vertices_21, vertices_261, vertices_517, vertices_25, vertices_73, vertices_521, vertices_273, vertices_321, vertices_577, vertices_134, vertices_262, vertices_518, vertices_162, vertices_290, vertices_546, vertices_322, vertices_578, vertices_642, vertices_148, vertices_532, vertices_388, vertices_152, vertices_280, vertices_536, vertices_104, vertices_168, vertices_296, vertices_552, vertices_328, vertices_392, vertices_648, vertices_400, vertices_656, vertices_352, vertices_608, vertices_416] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_327), (false, vertices_583), (false, vertices_541), (false, vertices_405), (false, vertices_345), (false, vertices_617), (true, vertices_134), (true, vertices_162), (true, vertices_290), (true, vertices_546), (true, vertices_642), (true, vertices_152), (true, vertices_168), (true, vertices_296), (true, vertices_392), (true, vertices_648), (true, vertices_656), (true, vertices_352), (true, vertices_416)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 13 16 19 22 23 24 25 26 27
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_327) then 14 else
  if p.val = (false, vertices_583) then 15 else
  if p.val = (false, vertices_541) then 17 else
  if p.val = (false, vertices_405) then 18 else
  if p.val = (false, vertices_345) then 20 else
  if p.val = (false, vertices_617) then 21 else
  if p.val = (true, vertices_134) then 0 else
  if p.val = (true, vertices_162) then 1 else
  if p.val = (true, vertices_290) then 2 else
  if p.val = (true, vertices_546) then 3 else
  if p.val = (true, vertices_642) then 4 else
  if p.val = (true, vertices_152) then 5 else
  if p.val = (true, vertices_168) then 6 else
  if p.val = (true, vertices_296) then 7 else
  if p.val = (true, vertices_392) then 8 else
  if p.val = (true, vertices_648) then 9 else
  if p.val = (true, vertices_656) then 10 else
  if p.val = (true, vertices_352) then 11 else
  if p.val = (true, vertices_416) then 12 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_134), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_162), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_290), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_546), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_642), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_152), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_168), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_296), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_392), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_648), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_656), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_352), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_416), by decide +kernel⟩
  | 13 => Sum.inl 0
  | 14 => Sum.inr ⟨(false, vertices_327), by decide +kernel⟩
  | 15 => Sum.inr ⟨(false, vertices_583), by decide +kernel⟩
  | 16 => Sum.inl 1
  | 17 => Sum.inr ⟨(false, vertices_541), by decide +kernel⟩
  | 18 => Sum.inr ⟨(false, vertices_405), by decide +kernel⟩
  | 19 => Sum.inl 2
  | 20 => Sum.inr ⟨(false, vertices_345), by decide +kernel⟩
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
cert_row_4 0 0 1 3 6 8 662 134 2
cert_row_4 1 0 1 4 6 7 422 134 2
cert_row_4 2 0 2 4 6 8 682 162 1
cert_row_4 3 0 4 5 7 8 866 290 2
cert_rows
cert_pivot_2 3 1 2 0
cert_heightProof 4
cert_coverFacet 0 662
cert_cover_5 0 0 0 1 3 6 134 662 2
cert_coverFacet 1 422
cert_cover_5 1 1 0 1 4 6 134 422 2
cert_coverFacet 2 682
cert_cover_5 2 2 0 2 4 6 162 682 1
cert_coverFacet 3 866
cert_cover_5 3 3 0 4 5 7 290 866 2
cert_coverFacet 4 408
cert_cover_2 4 3 2 6 7 152 408 3
cert_coverFacet 5 664
cert_cover_2 5 3 2 6 8 152 664 3
cert_coverFacet 6 360
cert_cover_2 6 4 2 5 7 104 360 3
cert_coverFacet 7 424
cert_cover_2 7 4 2 6 7 168 424 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0122

end
end BundlePart1

section BundlePart2
/- Source: ProjectionCertificates/R_m14e10q1_0129.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0129

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [395, 333, 653, 597, 369, 401, 657, 302, 558, 666, 626, 306, 402, 868, 13, 69, 517, 137, 265, 81, 145, 273, 529, 321, 385, 641, 46, 138, 266, 522, 50, 146, 274, 530, 290, 546, 386, 268, 524, 292, 548, 324, 580, 648, 112, 304, 592, 400, 656, 352, 608]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_395, vertices_333, vertices_653, vertices_597, vertices_369, vertices_401, vertices_657, vertices_302, vertices_558, vertices_666, vertices_626, vertices_306, vertices_402, vertices_868] (by decide +kernel)
  polygons := literalFinset [vertices_13, vertices_69, vertices_517, vertices_137, vertices_265, vertices_81, vertices_145, vertices_273, vertices_529, vertices_321, vertices_385, vertices_641, vertices_46, vertices_138, vertices_266, vertices_522, vertices_50, vertices_146, vertices_274, vertices_530, vertices_290, vertices_546, vertices_386, vertices_268, vertices_524, vertices_292, vertices_548, vertices_324, vertices_580, vertices_648, vertices_112, vertices_304, vertices_592, vertices_400, vertices_656, vertices_352, vertices_608] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_395), (false, vertices_333), (false, vertices_653), (false, vertices_597), (false, vertices_369), (false, vertices_401), (false, vertices_657), (true, vertices_46), (true, vertices_522), (true, vertices_50), (true, vertices_146), (true, vertices_274), (true, vertices_530), (true, vertices_290), (true, vertices_546), (true, vertices_292), (true, vertices_548), (true, vertices_608)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 12 15 19 20 22 23 24 25 26
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_395) then 13 else
  if p.val = (false, vertices_333) then 16 else
  if p.val = (false, vertices_653) then 17 else
  if p.val = (false, vertices_597) then 18 else
  if p.val = (false, vertices_369) then 21 else
  if p.val = (false, vertices_401) then 0 else
  if p.val = (false, vertices_657) then 1 else
  if p.val = (true, vertices_46) then 14 else
  if p.val = (true, vertices_522) then 2 else
  if p.val = (true, vertices_50) then 3 else
  if p.val = (true, vertices_146) then 4 else
  if p.val = (true, vertices_274) then 5 else
  if p.val = (true, vertices_530) then 6 else
  if p.val = (true, vertices_290) then 7 else
  if p.val = (true, vertices_546) then 8 else
  if p.val = (true, vertices_292) then 9 else
  if p.val = (true, vertices_548) then 10 else
  if p.val = (true, vertices_608) then 11 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_401), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_657), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_522), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_50), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_146), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_274), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_530), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_290), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_546), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_292), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_548), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_608), by decide +kernel⟩
  | 12 => Sum.inl 0
  | 13 => Sum.inr ⟨(false, vertices_395), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_46), by decide +kernel⟩
  | 15 => Sum.inl 1
  | 16 => Sum.inr ⟨(false, vertices_333), by decide +kernel⟩
  | 17 => Sum.inr ⟨(false, vertices_653), by decide +kernel⟩
  | 18 => Sum.inr ⟨(false, vertices_597), by decide +kernel⟩
  | 19 => Sum.inl 2
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
cert_row_4 0 0 2 3 6 8 666 138 2
cert_row_2 1 0 1 2 4 46
cert_row_4 2 0 3 4 5 8 626 50 3
cert_row_4 3 1 4 5 7 8 868 292 2
cert_rows
cert_pivot_2 6 2 0 1
cert_heightProof 4
cert_coverFacet 0 302
cert_cover_5 0 1 0 1 2 7 46 302 3
cert_coverFacet 1 558
cert_cover_5 1 1 0 1 2 8 46 558 3
cert_coverFacet 2 666
cert_cover_5 2 0 0 2 3 6 138 666 2
cert_coverFacet 3 626
cert_cover_5 3 2 0 3 4 5 50 626 3
cert_coverFacet 4 306
cert_cover_2 4 3 0 4 7 50 306 3
cert_coverFacet 5 402
cert_cover_2 5 3 0 6 7 146 402 3
cert_coverFacet 6 868
cert_cover_5 6 3 1 4 5 7 292 868 2
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0129

end
end BundlePart2

section BundlePart3
/- Source: ProjectionCertificates/R_m14e10q1_0131.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0131

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [775, 173, 397, 613, 361, 849, 406, 678, 666, 786, 472, 600, 616, 680, 141, 37, 261, 517, 41, 265, 97, 321, 577, 769, 134, 262, 518, 146, 274, 530, 642, 770, 164, 548, 388, 88, 152, 536, 104, 168, 552, 328, 584, 392, 648, 336, 592, 400, 784, 608, 672]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_775, vertices_173, vertices_397, vertices_613, vertices_361, vertices_849, vertices_406, vertices_678, vertices_666, vertices_786, vertices_472, vertices_600, vertices_616, vertices_680] (by decide +kernel)
  polygons := literalFinset [vertices_141, vertices_37, vertices_261, vertices_517, vertices_41, vertices_265, vertices_97, vertices_321, vertices_577, vertices_769, vertices_134, vertices_262, vertices_518, vertices_146, vertices_274, vertices_530, vertices_642, vertices_770, vertices_164, vertices_548, vertices_388, vertices_88, vertices_152, vertices_536, vertices_104, vertices_168, vertices_552, vertices_328, vertices_584, vertices_392, vertices_648, vertices_336, vertices_592, vertices_400, vertices_784, vertices_608, vertices_672] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_775), (false, vertices_173), (false, vertices_397), (false, vertices_613), (false, vertices_361), (false, vertices_849), (true, vertices_134), (true, vertices_146), (true, vertices_274), (true, vertices_530), (true, vertices_642), (true, vertices_88), (true, vertices_152), (true, vertices_536), (true, vertices_552), (true, vertices_584), (true, vertices_648), (true, vertices_400), (true, vertices_672)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 13 15 19 21 23 24 25 26 27
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_775) then 14 else
  if p.val = (false, vertices_173) then 16 else
  if p.val = (false, vertices_397) then 17 else
  if p.val = (false, vertices_613) then 18 else
  if p.val = (false, vertices_361) then 20 else
  if p.val = (false, vertices_849) then 22 else
  if p.val = (true, vertices_134) then 0 else
  if p.val = (true, vertices_146) then 1 else
  if p.val = (true, vertices_274) then 2 else
  if p.val = (true, vertices_530) then 3 else
  if p.val = (true, vertices_642) then 4 else
  if p.val = (true, vertices_88) then 5 else
  if p.val = (true, vertices_152) then 6 else
  if p.val = (true, vertices_536) then 7 else
  if p.val = (true, vertices_552) then 8 else
  if p.val = (true, vertices_584) then 9 else
  if p.val = (true, vertices_648) then 10 else
  if p.val = (true, vertices_400) then 11 else
  if p.val = (true, vertices_672) then 12 else
  0
cert_priority
cert_nodeAtPriority_11 134 146 274 530 642 88 152 536 552 584 648 400 672 775 173 397 613 361 849
cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 4 6 8 678 134 2
cert_row_4 1 0 1 3 6 7 406 134 2
cert_row_4 2 0 2 3 6 8 666 146 1
cert_row_4 3 2 3 5 6 7 472 88 3
cert_rows
cert_pivot_2 4 1 0 2
cert_heightProof 4
cert_coverFacet 0 406
cert_cover_5 0 1 0 1 3 6 134 406 2
cert_coverFacet 1 678
cert_cover_5 1 0 0 1 4 6 134 678 2
cert_coverFacet 2 666
cert_cover_5 2 2 0 2 3 6 146 666 1
cert_coverFacet 3 786
cert_cover_2 3 3 0 7 8 274 786 3
cert_coverFacet 4 472
cert_cover_5 4 3 2 3 5 6 88 472 3
cert_coverFacet 5 600
cert_cover_2 5 3 2 5 8 88 600 3
cert_coverFacet 6 616
cert_cover_2 6 4 2 5 8 104 616 3
cert_coverFacet 7 680
cert_cover_2 7 4 2 6 8 168 680 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0131

end
end BundlePart3

section BundlePart4
/- Source: ProjectionCertificates/R_m14e10q1_0133.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0133

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [171, 93, 157, 677, 837, 617, 902, 298, 394, 866, 674, 468, 376, 408, 29, 69, 133, 517, 41, 73, 137, 161, 545, 577, 42, 138, 266, 162, 290, 546, 386, 642, 770, 84, 148, 324, 388, 644, 772, 88, 152, 280, 104, 296, 392, 336, 400, 352, 608, 672, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_171, vertices_93, vertices_157, vertices_677, vertices_837, vertices_617, vertices_902, vertices_298, vertices_394, vertices_866, vertices_674, vertices_468, vertices_376, vertices_408] (by decide +kernel)
  polygons := literalFinset [vertices_29, vertices_69, vertices_133, vertices_517, vertices_41, vertices_73, vertices_137, vertices_161, vertices_545, vertices_577, vertices_42, vertices_138, vertices_266, vertices_162, vertices_290, vertices_546, vertices_386, vertices_642, vertices_770, vertices_84, vertices_148, vertices_324, vertices_388, vertices_644, vertices_772, vertices_88, vertices_152, vertices_280, vertices_104, vertices_296, vertices_392, vertices_336, vertices_400, vertices_352, vertices_608, vertices_672, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_171), (false, vertices_93), (false, vertices_157), (false, vertices_677), (false, vertices_837), (false, vertices_617), (true, vertices_266), (true, vertices_290), (true, vertices_546), (true, vertices_386), (true, vertices_642), (true, vertices_770), (true, vertices_388), (true, vertices_280), (true, vertices_296), (true, vertices_392), (true, vertices_336), (true, vertices_400), (true, vertices_352)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 13 19 15 22 23 24 25 26 27
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_171) then 14 else
  if p.val = (false, vertices_93) then 16 else
  if p.val = (false, vertices_157) then 17 else
  if p.val = (false, vertices_677) then 20 else
  if p.val = (false, vertices_837) then 21 else
  if p.val = (false, vertices_617) then 18 else
  if p.val = (true, vertices_266) then 0 else
  if p.val = (true, vertices_290) then 1 else
  if p.val = (true, vertices_546) then 2 else
  if p.val = (true, vertices_386) then 3 else
  if p.val = (true, vertices_642) then 4 else
  if p.val = (true, vertices_770) then 5 else
  if p.val = (true, vertices_388) then 6 else
  if p.val = (true, vertices_280) then 7 else
  if p.val = (true, vertices_296) then 8 else
  if p.val = (true, vertices_392) then 9 else
  if p.val = (true, vertices_336) then 10 else
  if p.val = (true, vertices_400) then 11 else
  if p.val = (true, vertices_352) then 12 else
  0
cert_priority
cert_nodeAtPriority 0 266 2 290 1 546 386 642 770 388 280 296 392 336 400 352 171 93 157 617 677 837
cert_priority_injective
cert_incidenceProof
cert_row_4 0 2 3 4 5 7 376 88 2
cert_row_4 1 0 4 5 7 8 866 290 2
cert_row_4 2 0 1 6 7 8 902 386 1
cert_row_4 3 1 3 5 6 7 468 84 3
cert_rows
cert_pivot_2 2 4 0 1
cert_heightProof 4
cert_coverFacet 0 902
cert_cover_5 0 2 0 1 6 7 386 902 1
cert_coverFacet 1 298
cert_cover_2 1 2 0 4 7 42 298 3
cert_coverFacet 2 394
cert_cover_2 2 2 0 6 7 138 394 3
cert_coverFacet 3 866
cert_cover_5 3 1 0 4 5 7 290 866 2
cert_coverFacet 4 674
cert_cover_2 4 4 0 6 8 162 674 3
cert_coverFacet 5 468
cert_cover_5 5 3 1 3 5 6 84 468 3
cert_coverFacet 6 376
cert_cover_5 6 0 2 3 4 5 88 376 2
cert_coverFacet 7 408
cert_cover_2 7 3 2 6 7 152 408 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0133

end
end BundlePart4

section BundlePart5
/- Source: ProjectionCertificates/R_m14e10q1_0163.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0163

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [595, 453, 569, 433, 337, 737, 94, 782, 710, 538, 348, 932, 312, 808, 49, 81, 273, 529, 161, 545, 193, 321, 577, 385, 14, 70, 518, 26, 522, 82, 530, 578, 92, 268, 196, 324, 388, 644, 772, 56, 280, 536, 296, 552, 776, 304, 336, 416, 672, 800, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_595, vertices_453, vertices_569, vertices_433, vertices_337, vertices_737, vertices_94, vertices_782, vertices_710, vertices_538, vertices_348, vertices_932, vertices_312, vertices_808] (by decide +kernel)
  polygons := literalFinset [vertices_49, vertices_81, vertices_273, vertices_529, vertices_161, vertices_545, vertices_193, vertices_321, vertices_577, vertices_385, vertices_14, vertices_70, vertices_518, vertices_26, vertices_522, vertices_82, vertices_530, vertices_578, vertices_92, vertices_268, vertices_196, vertices_324, vertices_388, vertices_644, vertices_772, vertices_56, vertices_280, vertices_536, vertices_296, vertices_552, vertices_776, vertices_304, vertices_336, vertices_416, vertices_672, vertices_800, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_595), (false, vertices_453), (false, vertices_569), (false, vertices_433), (false, vertices_337), (false, vertices_737), (true, vertices_14), (true, vertices_70), (true, vertices_518), (true, vertices_26), (true, vertices_522), (true, vertices_92), (true, vertices_268), (true, vertices_644), (true, vertices_772), (true, vertices_280), (true, vertices_296), (true, vertices_776), (true, vertices_800)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 13 15 18 20 22 24 25 26 27
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_595) then 14 else
  if p.val = (false, vertices_453) then 16 else
  if p.val = (false, vertices_569) then 19 else
  if p.val = (false, vertices_433) then 21 else
  if p.val = (false, vertices_337) then 0 else
  if p.val = (false, vertices_737) then 23 else
  if p.val = (true, vertices_14) then 1 else
  if p.val = (true, vertices_70) then 2 else
  if p.val = (true, vertices_518) then 3 else
  if p.val = (true, vertices_26) then 4 else
  if p.val = (true, vertices_522) then 5 else
  if p.val = (true, vertices_92) then 17 else
  if p.val = (true, vertices_268) then 6 else
  if p.val = (true, vertices_644) then 7 else
  if p.val = (true, vertices_772) then 8 else
  if p.val = (true, vertices_280) then 9 else
  if p.val = (true, vertices_296) then 10 else
  if p.val = (true, vertices_776) then 11 else
  if p.val = (true, vertices_800) then 12 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_337), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_14), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_70), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_518), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_26), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_522), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_268), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_644), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_772), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_280), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_296), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_776), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_800), by decide +kernel⟩
  | 13 => Sum.inl 0
  | 14 => Sum.inr ⟨(false, vertices_595), by decide +kernel⟩
  | 15 => Sum.inl 1
  | 16 => Sum.inr ⟨(false, vertices_453), by decide +kernel⟩
  | 17 => Sum.inr ⟨(true, vertices_92), by decide +kernel⟩
  | 18 => Sum.inl 2
  | 19 => Sum.inr ⟨(false, vertices_569), by decide +kernel⟩
  | 20 => Sum.inl 3
  | 21 => Sum.inr ⟨(false, vertices_433), by decide +kernel⟩
  | 22 => Sum.inl 4
  | 23 => Sum.inr ⟨(false, vertices_737), by decide +kernel⟩
  | 24 => Sum.inl 5
  | 25 => Sum.inl 6
  | 26 => Sum.inl 7
  | 27 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 1 2 3 5 92
cert_row_4 1 0 1 2 7 8 782 14 3
cert_row_4 2 0 1 5 6 8 710 70 3
cert_row_4 3 1 4 6 7 8 932 388 1
cert_rows
cert_pivot_2 3 2 0 1
cert_heightProof 4
cert_coverFacet 0 94
cert_cover_5 0 0 0 1 2 3 14 94 3
cert_coverFacet 1 782
cert_cover_5 1 1 0 1 2 7 14 782 3
cert_coverFacet 2 710
cert_cover_5 2 2 0 1 5 6 70 710 3
cert_coverFacet 3 538
cert_cover_2 3 2 0 3 8 26 538 3
cert_coverFacet 4 348
cert_cover_5 4 0 1 2 3 7 92 348 3
cert_coverFacet 5 932
cert_cover_5 5 3 1 4 6 7 388 932 1
cert_coverFacet 6 312
cert_cover_2 6 3 2 4 7 56 312 3
cert_coverFacet 7 808
cert_cover_2 7 4 2 7 8 296 808 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0163

end
end BundlePart5

section BundlePart6
/- Source: ProjectionCertificates/R_m14e10q1_0167.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0167

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [899, 117, 309, 837, 425, 737, 790, 410, 538, 682, 604, 120, 312, 616, 53, 69, 261, 97, 161, 289, 577, 385, 641, 769, 26, 138, 522, 274, 530, 386, 642, 770, 84, 276, 532, 580, 772, 56, 88, 280, 536, 104, 168, 296, 552, 584, 392, 112, 304, 608, 672]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_899, vertices_117, vertices_309, vertices_837, vertices_425, vertices_737, vertices_790, vertices_410, vertices_538, vertices_682, vertices_604, vertices_120, vertices_312, vertices_616] (by decide +kernel)
  polygons := literalFinset [vertices_53, vertices_69, vertices_261, vertices_97, vertices_161, vertices_289, vertices_577, vertices_385, vertices_641, vertices_769, vertices_26, vertices_138, vertices_522, vertices_274, vertices_530, vertices_386, vertices_642, vertices_770, vertices_84, vertices_276, vertices_532, vertices_580, vertices_772, vertices_56, vertices_88, vertices_280, vertices_536, vertices_104, vertices_168, vertices_296, vertices_552, vertices_584, vertices_392, vertices_112, vertices_304, vertices_608, vertices_672] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_899), (false, vertices_117), (false, vertices_309), (false, vertices_837), (false, vertices_425), (false, vertices_737), (true, vertices_26), (true, vertices_138), (true, vertices_522), (true, vertices_274), (true, vertices_530), (true, vertices_532), (true, vertices_56), (true, vertices_88), (true, vertices_280), (true, vertices_536), (true, vertices_104), (true, vertices_552), (true, vertices_584)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 13 15 19 21 22 24 25 26 27
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_899) then 14 else
  if p.val = (false, vertices_117) then 16 else
  if p.val = (false, vertices_309) then 17 else
  if p.val = (false, vertices_837) then 18 else
  if p.val = (false, vertices_425) then 20 else
  if p.val = (false, vertices_737) then 23 else
  if p.val = (true, vertices_26) then 0 else
  if p.val = (true, vertices_138) then 1 else
  if p.val = (true, vertices_522) then 2 else
  if p.val = (true, vertices_274) then 3 else
  if p.val = (true, vertices_530) then 4 else
  if p.val = (true, vertices_532) then 5 else
  if p.val = (true, vertices_56) then 6 else
  if p.val = (true, vertices_88) then 7 else
  if p.val = (true, vertices_280) then 8 else
  if p.val = (true, vertices_536) then 9 else
  if p.val = (true, vertices_104) then 10 else
  if p.val = (true, vertices_552) then 11 else
  if p.val = (true, vertices_584) then 12 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_26), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_138), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_522), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_274), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_530), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_532), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_56), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_88), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_280), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_536), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_104), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_552), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_584), by decide +kernel⟩
  | 13 => Sum.inl 0
  | 14 => Sum.inr ⟨(false, vertices_899), by decide +kernel⟩
  | 15 => Sum.inl 1
  | 16 => Sum.inr ⟨(false, vertices_117), by decide +kernel⟩
  | 17 => Sum.inr ⟨(false, vertices_309), by decide +kernel⟩
  | 18 => Sum.inr ⟨(false, vertices_837), by decide +kernel⟩
  | 19 => Sum.inl 2
  | 20 => Sum.inr ⟨(false, vertices_425), by decide +kernel⟩
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
cert_row_4 0 0 2 4 6 8 682 138 2
cert_row_4 1 0 2 3 6 7 410 26 3
cert_row_4 2 0 1 3 7 8 790 274 1
cert_row_4 3 1 2 3 5 8 604 84 1
cert_rows
cert_pivot_2 4 6 0 1
cert_heightProof 4
cert_coverFacet 0 790
cert_cover_5 0 2 0 1 3 7 274 790 1
cert_coverFacet 1 410
cert_cover_5 1 1 0 2 3 6 26 410 3
cert_coverFacet 2 538
cert_cover_2 2 2 0 3 8 26 538 3
cert_coverFacet 3 682
cert_cover_5 3 0 0 2 4 6 138 682 2
cert_coverFacet 4 604
cert_cover_5 4 3 1 2 3 5 84 604 1
cert_coverFacet 5 120
cert_cover_2 5 3 2 4 5 56 120 3
cert_coverFacet 6 312
cert_cover_2 6 3 2 4 7 56 312 3
cert_coverFacet 7 616
cert_cover_2 7 4 2 5 8 104 616 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0167

end
end BundlePart6

section BundlePart7
/- Source: ProjectionCertificates/R_m14e10q1_0184.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0184

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [775, 357, 677, 841, 721, 225, 174, 302, 662, 602, 154, 778, 216, 488, 37, 261, 517, 97, 161, 193, 321, 577, 641, 769, 46, 134, 262, 518, 26, 138, 266, 522, 146, 530, 770, 164, 292, 644, 88, 152, 168, 296, 200, 328, 584, 776, 208, 592, 656, 224, 352]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_775, vertices_357, vertices_677, vertices_841, vertices_721, vertices_225, vertices_174, vertices_302, vertices_662, vertices_602, vertices_154, vertices_778, vertices_216, vertices_488] (by decide +kernel)
  polygons := literalFinset [vertices_37, vertices_261, vertices_517, vertices_97, vertices_161, vertices_193, vertices_321, vertices_577, vertices_641, vertices_769, vertices_46, vertices_134, vertices_262, vertices_518, vertices_26, vertices_138, vertices_266, vertices_522, vertices_146, vertices_530, vertices_770, vertices_164, vertices_292, vertices_644, vertices_88, vertices_152, vertices_168, vertices_296, vertices_200, vertices_328, vertices_584, vertices_776, vertices_208, vertices_592, vertices_656, vertices_224, vertices_352] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_775), (false, vertices_357), (false, vertices_677), (false, vertices_841), (false, vertices_721), (false, vertices_225), (true, vertices_46), (true, vertices_134), (true, vertices_26), (true, vertices_138), (true, vertices_266), (true, vertices_522), (true, vertices_146), (true, vertices_530), (true, vertices_88), (true, vertices_152), (true, vertices_168), (true, vertices_296), (true, vertices_200)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 13 16 19 21 23 24 25 26 27
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_775) then 14 else
  if p.val = (false, vertices_357) then 17 else
  if p.val = (false, vertices_677) then 18 else
  if p.val = (false, vertices_841) then 20 else
  if p.val = (false, vertices_721) then 22 else
  if p.val = (false, vertices_225) then 0 else
  if p.val = (true, vertices_46) then 15 else
  if p.val = (true, vertices_134) then 1 else
  if p.val = (true, vertices_26) then 2 else
  if p.val = (true, vertices_138) then 3 else
  if p.val = (true, vertices_266) then 4 else
  if p.val = (true, vertices_522) then 5 else
  if p.val = (true, vertices_146) then 6 else
  if p.val = (true, vertices_530) then 7 else
  if p.val = (true, vertices_88) then 8 else
  if p.val = (true, vertices_152) then 9 else
  if p.val = (true, vertices_168) then 10 else
  if p.val = (true, vertices_296) then 11 else
  if p.val = (true, vertices_200) then 12 else
  0
cert_priority
cert_nodeAtPriority_17 225 134 26 138 266 522 146 530 88 152 168 296 200 775 46 357 677 841 721
cert_priority_injective
cert_incidenceProof
cert_row_4 0 2 4 5 6 7 488 168 2
cert_row_2 1 0 1 2 4 46
cert_row_4 2 0 1 3 6 8 662 134 2
cert_row_4 3 0 2 3 5 8 602 26 3
cert_rows
cert_pivot_2 7 4 1 0
cert_heightProof 4
cert_coverFacet 0 174
cert_cover_5 0 1 0 1 2 6 46 174 3
cert_coverFacet 1 302
cert_cover_5 1 1 0 1 2 7 46 302 3
cert_coverFacet 2 662
cert_cover_5 2 2 0 1 3 6 134 662 2
cert_coverFacet 3 602
cert_cover_5 3 3 0 2 3 5 26 602 3
cert_coverFacet 4 154
cert_cover_2 4 2 0 3 6 26 154 3
cert_coverFacet 5 778
cert_cover_2 5 2 0 7 8 266 778 3
cert_coverFacet 6 216
cert_cover_2 6 3 2 5 6 88 216 3
cert_coverFacet 7 488
cert_cover_5 7 0 2 4 5 6 168 488 2
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0184

end
end BundlePart7

section BundlePart8
/- Source: ProjectionCertificates/R_m14e10q1_0193.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0193

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [803, 565, 149, 421, 409, 849, 614, 346, 234, 426, 834, 220, 596, 228, 21, 37, 133, 145, 273, 529, 289, 545, 385, 769, 170, 74, 266, 98, 290, 546, 322, 578, 770, 84, 148, 532, 100, 164, 548, 196, 580, 88, 152, 280, 200, 392, 336, 592, 224, 416, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_803, vertices_565, vertices_149, vertices_421, vertices_409, vertices_849, vertices_614, vertices_346, vertices_234, vertices_426, vertices_834, vertices_220, vertices_596, vertices_228] (by decide +kernel)
  polygons := literalFinset [vertices_21, vertices_37, vertices_133, vertices_145, vertices_273, vertices_529, vertices_289, vertices_545, vertices_385, vertices_769, vertices_170, vertices_74, vertices_266, vertices_98, vertices_290, vertices_546, vertices_322, vertices_578, vertices_770, vertices_84, vertices_148, vertices_532, vertices_100, vertices_164, vertices_548, vertices_196, vertices_580, vertices_88, vertices_152, vertices_280, vertices_200, vertices_392, vertices_336, vertices_592, vertices_224, vertices_416, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_803), (false, vertices_565), (false, vertices_149), (false, vertices_421), (false, vertices_409), (false, vertices_849), (true, vertices_170), (true, vertices_74), (true, vertices_266), (true, vertices_98), (true, vertices_322), (true, vertices_578), (true, vertices_84), (true, vertices_100), (true, vertices_196), (true, vertices_580), (true, vertices_88), (true, vertices_200), (true, vertices_224)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 13 16 19 21 23 24 25 26 27
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_803) then 14 else
  if p.val = (false, vertices_565) then 17 else
  if p.val = (false, vertices_149) then 0 else
  if p.val = (false, vertices_421) then 18 else
  if p.val = (false, vertices_409) then 20 else
  if p.val = (false, vertices_849) then 22 else
  if p.val = (true, vertices_170) then 15 else
  if p.val = (true, vertices_74) then 1 else
  if p.val = (true, vertices_266) then 2 else
  if p.val = (true, vertices_98) then 3 else
  if p.val = (true, vertices_322) then 4 else
  if p.val = (true, vertices_578) then 5 else
  if p.val = (true, vertices_84) then 6 else
  if p.val = (true, vertices_100) then 7 else
  if p.val = (true, vertices_196) then 8 else
  if p.val = (true, vertices_580) then 9 else
  if p.val = (true, vertices_88) then 10 else
  if p.val = (true, vertices_200) then 11 else
  if p.val = (true, vertices_224) then 12 else
  0
cert_priority
cert_nodeAtPriority_17 149 74 266 98 322 578 84 100 196 580 88 200 224 803 170 565 421 409 849
cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 4 5 8 614 98 1
cert_row_2 1 0 2 4 6 170
cert_row_4 2 0 2 3 5 7 346 74 2
cert_row_4 3 1 2 3 5 6 220 84 1
cert_rows
cert_pivot_2 8 4 0 1
cert_heightProof 4
cert_coverFacet 0 614
cert_cover_5 0 0 0 1 4 5 98 614 1
cert_coverFacet 1 346
cert_cover_5 1 2 0 2 3 5 74 346 2
cert_coverFacet 2 234
cert_cover_5 2 1 0 2 4 5 170 234 3
cert_coverFacet 3 426
cert_cover_5 3 1 0 2 4 7 170 426 3
cert_coverFacet 4 834
cert_cover_2 4 5 0 7 8 322 834 3
cert_coverFacet 5 220
cert_cover_5 5 3 1 2 3 5 84 220 1
cert_coverFacet 6 596
cert_cover_2 6 3 1 5 8 84 596 3
cert_coverFacet 7 228
cert_cover_2 7 4 1 5 6 100 228 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0193

end
end BundlePart8

section BundlePart9
/- Source: ProjectionCertificates/R_m14e10q1_0194.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0194

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [391, 107, 139, 355, 653, 789, 809, 714, 450, 724, 404, 632, 496, 816, 11, 99, 131, 259, 133, 261, 517, 41, 137, 521, 289, 769, 74, 138, 194, 322, 386, 148, 276, 532, 388, 644, 104, 552, 584, 648, 112, 304, 560, 208, 592, 400, 784, 352, 800, 448, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_391, vertices_107, vertices_139, vertices_355, vertices_653, vertices_789, vertices_809, vertices_714, vertices_450, vertices_724, vertices_404, vertices_632, vertices_496, vertices_816] (by decide +kernel)
  polygons := literalFinset [vertices_11, vertices_99, vertices_131, vertices_259, vertices_133, vertices_261, vertices_517, vertices_41, vertices_137, vertices_521, vertices_289, vertices_769, vertices_74, vertices_138, vertices_194, vertices_322, vertices_386, vertices_148, vertices_276, vertices_532, vertices_388, vertices_644, vertices_104, vertices_552, vertices_584, vertices_648, vertices_112, vertices_304, vertices_560, vertices_208, vertices_592, vertices_400, vertices_784, vertices_352, vertices_800, vertices_448, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_391), (false, vertices_107), (false, vertices_139), (false, vertices_355), (false, vertices_653), (false, vertices_789), (false, vertices_809), (true, vertices_194), (true, vertices_148), (true, vertices_584), (true, vertices_112), (true, vertices_304), (true, vertices_560), (true, vertices_208), (true, vertices_592), (true, vertices_400), (true, vertices_448), (true, vertices_704)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 12 16 19 21 22 23 24 25 26
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_391) then 13 else
  if p.val = (false, vertices_107) then 14 else
  if p.val = (false, vertices_139) then 0 else
  if p.val = (false, vertices_355) then 15 else
  if p.val = (false, vertices_653) then 17 else
  if p.val = (false, vertices_789) then 18 else
  if p.val = (false, vertices_809) then 20 else
  if p.val = (true, vertices_194) then 1 else
  if p.val = (true, vertices_148) then 2 else
  if p.val = (true, vertices_584) then 3 else
  if p.val = (true, vertices_112) then 4 else
  if p.val = (true, vertices_304) then 5 else
  if p.val = (true, vertices_560) then 6 else
  if p.val = (true, vertices_208) then 7 else
  if p.val = (true, vertices_592) then 8 else
  if p.val = (true, vertices_400) then 9 else
  if p.val = (true, vertices_448) then 10 else
  if p.val = (true, vertices_704) then 11 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_139), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_194), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_148), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_584), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_112), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_304), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_560), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_208), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_592), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_400), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_448), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_704), by decide +kernel⟩
  | 12 => Sum.inl 0
  | 13 => Sum.inr ⟨(false, vertices_391), by decide +kernel⟩
  | 14 => Sum.inr ⟨(false, vertices_107), by decide +kernel⟩
  | 15 => Sum.inr ⟨(false, vertices_355), by decide +kernel⟩
  | 16 => Sum.inl 1
  | 17 => Sum.inr ⟨(false, vertices_653), by decide +kernel⟩
  | 18 => Sum.inr ⟨(false, vertices_789), by decide +kernel⟩
  | 19 => Sum.inl 2
  | 20 => Sum.inr ⟨(false, vertices_809), by decide +kernel⟩
  | 21 => Sum.inl 3
  | 22 => Sum.inl 4
  | 23 => Sum.inl 5
  | 24 => Sum.inl 6
  | 25 => Sum.inl 7
  | 26 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 2 5 6 8 714 74 3
cert_row_4 1 1 3 5 6 8 724 148 2
cert_row_4 2 2 3 4 5 8 632 104 1
cert_row_4 3 3 4 5 6 7 496 112 3
cert_rows
cert_pivot_2 0 1 2 3
cert_heightProof 4
cert_coverFacet 0 714
cert_cover_5 0 0 0 2 5 6 74 714 3
cert_coverFacet 1 450
cert_cover_2 1 5 0 6 7 194 450 3
cert_coverFacet 2 724
cert_cover_5 2 1 1 3 5 6 148 724 2
cert_coverFacet 3 404
cert_cover_2 3 3 1 6 7 148 404 3
cert_coverFacet 4 632
cert_cover_5 4 2 2 3 4 5 104 632 1
cert_coverFacet 5 496
cert_cover_5 5 3 3 4 5 6 112 496 3
cert_coverFacet 6 816
cert_cover_2 6 4 3 7 8 304 816 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0194

end
end BundlePart9

section BundlePart10
/- Source: ProjectionCertificates/R_m14e10q1_0197.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0197

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [835, 557, 53, 597, 369, 929, 206, 590, 682, 466, 898, 172, 436, 212, 21, 37, 517, 49, 81, 289, 545, 321, 577, 769, 78, 138, 522, 194, 322, 578, 386, 642, 770, 44, 140, 524, 52, 84, 148, 164, 196, 580, 168, 552, 304, 208, 336, 400, 416, 672, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_835, vertices_557, vertices_53, vertices_597, vertices_369, vertices_929, vertices_206, vertices_590, vertices_682, vertices_466, vertices_898, vertices_172, vertices_436, vertices_212] (by decide +kernel)
  polygons := literalFinset [vertices_21, vertices_37, vertices_517, vertices_49, vertices_81, vertices_289, vertices_545, vertices_321, vertices_577, vertices_769, vertices_78, vertices_138, vertices_522, vertices_194, vertices_322, vertices_578, vertices_386, vertices_642, vertices_770, vertices_44, vertices_140, vertices_524, vertices_52, vertices_84, vertices_148, vertices_164, vertices_196, vertices_580, vertices_168, vertices_552, vertices_304, vertices_208, vertices_336, vertices_400, vertices_416, vertices_672, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_835), (false, vertices_557), (false, vertices_53), (false, vertices_597), (false, vertices_369), (false, vertices_929), (true, vertices_78), (true, vertices_138), (true, vertices_522), (true, vertices_194), (true, vertices_386), (true, vertices_642), (true, vertices_140), (true, vertices_148), (true, vertices_164), (true, vertices_196), (true, vertices_168), (true, vertices_208), (true, vertices_400)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 13 16 19 20 22 24 25 26 27
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_835) then 14 else
  if p.val = (false, vertices_557) then 17 else
  if p.val = (false, vertices_53) then 0 else
  if p.val = (false, vertices_597) then 18 else
  if p.val = (false, vertices_369) then 21 else
  if p.val = (false, vertices_929) then 23 else
  if p.val = (true, vertices_78) then 15 else
  if p.val = (true, vertices_138) then 1 else
  if p.val = (true, vertices_522) then 2 else
  if p.val = (true, vertices_194) then 3 else
  if p.val = (true, vertices_386) then 4 else
  if p.val = (true, vertices_642) then 5 else
  if p.val = (true, vertices_140) then 6 else
  if p.val = (true, vertices_148) then 7 else
  if p.val = (true, vertices_164) then 8 else
  if p.val = (true, vertices_196) then 9 else
  if p.val = (true, vertices_168) then 10 else
  if p.val = (true, vertices_208) then 11 else
  if p.val = (true, vertices_400) then 12 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_53), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_138), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_522), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_194), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_386), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_642), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_140), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_148), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_164), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_196), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_168), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_208), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_400), by decide +kernel⟩
  | 13 => Sum.inl 0
  | 14 => Sum.inr ⟨(false, vertices_835), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_78), by decide +kernel⟩
  | 16 => Sum.inl 1
  | 17 => Sum.inr ⟨(false, vertices_557), by decide +kernel⟩
  | 18 => Sum.inr ⟨(false, vertices_597), by decide +kernel⟩
  | 19 => Sum.inl 2
  | 20 => Sum.inl 3
  | 21 => Sum.inr ⟨(false, vertices_369), by decide +kernel⟩
  | 22 => Sum.inl 4
  | 23 => Sum.inr ⟨(false, vertices_929), by decide +kernel⟩
  | 24 => Sum.inl 5
  | 25 => Sum.inl 6
  | 26 => Sum.inl 7
  | 27 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 2 4 6 8 682 138 2
cert_row_2 1 0 1 2 5 78
cert_row_4 2 0 3 5 6 7 466 194 1
cert_row_4 3 1 3 4 6 7 436 52 3
cert_rows
cert_pivot_2 8 2 0 1
cert_heightProof 4
cert_coverFacet 0 206
cert_cover_5 0 1 0 1 2 6 78 206 3
cert_coverFacet 1 590
cert_cover_5 1 1 0 1 2 8 78 590 3
cert_coverFacet 2 682
cert_cover_5 2 0 0 2 4 6 138 682 2
cert_coverFacet 3 466
cert_cover_5 3 2 0 3 5 6 194 466 1
cert_coverFacet 4 898
cert_cover_2 4 6 0 7 8 386 898 3
cert_coverFacet 5 172
cert_cover_2 5 2 1 4 6 44 172 3
cert_coverFacet 6 436
cert_cover_5 6 3 1 3 4 6 52 436 3
cert_coverFacet 7 212
cert_cover_2 7 3 1 5 6 84 212 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0197

end
end BundlePart10

section BundlePart11
/- Source: ProjectionCertificates/R_m14e10q1_0215.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0215

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [87, 151, 331, 139, 653, 837, 809, 426, 850, 402, 724, 696, 432, 816, 23, 11, 67, 131, 69, 133, 517, 137, 265, 521, 321, 769, 138, 266, 82, 146, 274, 322, 386, 84, 148, 580, 644, 168, 296, 552, 648, 176, 304, 560, 592, 400, 656, 784, 416, 800, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_87, vertices_151, vertices_331, vertices_139, vertices_653, vertices_837, vertices_809, vertices_426, vertices_850, vertices_402, vertices_724, vertices_696, vertices_432, vertices_816] (by decide +kernel)
  polygons := literalFinset [vertices_23, vertices_11, vertices_67, vertices_131, vertices_69, vertices_133, vertices_517, vertices_137, vertices_265, vertices_521, vertices_321, vertices_769, vertices_138, vertices_266, vertices_82, vertices_146, vertices_274, vertices_322, vertices_386, vertices_84, vertices_148, vertices_580, vertices_644, vertices_168, vertices_296, vertices_552, vertices_648, vertices_176, vertices_304, vertices_560, vertices_592, vertices_400, vertices_656, vertices_784, vertices_416, vertices_800, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_87), (false, vertices_151), (false, vertices_331), (false, vertices_139), (false, vertices_653), (false, vertices_837), (false, vertices_809), (true, vertices_274), (true, vertices_386), (true, vertices_168), (true, vertices_176), (true, vertices_304), (true, vertices_560), (true, vertices_592), (true, vertices_400), (true, vertices_656), (true, vertices_784), (true, vertices_416)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 12 16 19 21 22 23 24 25 26
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_87) then 13 else
  if p.val = (false, vertices_151) then 14 else
  if p.val = (false, vertices_331) then 15 else
  if p.val = (false, vertices_139) then 0 else
  if p.val = (false, vertices_653) then 17 else
  if p.val = (false, vertices_837) then 18 else
  if p.val = (false, vertices_809) then 20 else
  if p.val = (true, vertices_274) then 1 else
  if p.val = (true, vertices_386) then 2 else
  if p.val = (true, vertices_168) then 3 else
  if p.val = (true, vertices_176) then 4 else
  if p.val = (true, vertices_304) then 5 else
  if p.val = (true, vertices_560) then 6 else
  if p.val = (true, vertices_592) then 7 else
  if p.val = (true, vertices_400) then 8 else
  if p.val = (true, vertices_656) then 9 else
  if p.val = (true, vertices_784) then 10 else
  if p.val = (true, vertices_416) then 11 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_139), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_274), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_386), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_168), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_176), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_304), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_560), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_592), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_400), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_656), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_784), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_416), by decide +kernel⟩
  | 12 => Sum.inl 0
  | 13 => Sum.inr ⟨(false, vertices_87), by decide +kernel⟩
  | 14 => Sum.inr ⟨(false, vertices_151), by decide +kernel⟩
  | 15 => Sum.inr ⟨(false, vertices_331), by decide +kernel⟩
  | 16 => Sum.inl 1
  | 17 => Sum.inr ⟨(false, vertices_653), by decide +kernel⟩
  | 18 => Sum.inr ⟨(false, vertices_837), by decide +kernel⟩
  | 19 => Sum.inl 2
  | 20 => Sum.inr ⟨(false, vertices_809), by decide +kernel⟩
  | 21 => Sum.inl 3
  | 22 => Sum.inl 4
  | 23 => Sum.inl 5
  | 24 => Sum.inl 6
  | 25 => Sum.inl 7
  | 26 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 1 3 5 6 8 724 84 3
cert_row_4 1 0 3 5 7 8 850 82 3
cert_row_4 2 0 2 4 6 7 426 138 2
cert_row_4 3 2 3 4 6 8 696 168 1
cert_rows
cert_pivot_2 1 5 0 2
cert_heightProof 4
cert_coverFacet 0 426
cert_cover_5 0 2 0 2 4 6 138 426 2
cert_coverFacet 1 850
cert_cover_5 1 1 0 3 5 7 82 850 3
cert_coverFacet 2 402
cert_cover_2 2 3 0 6 7 146 402 3
cert_coverFacet 3 724
cert_cover_5 3 0 1 3 5 6 84 724 3
cert_coverFacet 4 696
cert_cover_5 4 3 2 3 4 6 168 696 1
cert_coverFacet 5 432
cert_cover_2 5 4 3 6 7 176 432 3
cert_coverFacet 6 816
cert_cover_2 6 4 3 7 8 304 816 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0215

end
end BundlePart11

section BundlePart12
/- Source: ProjectionCertificates/R_m14e10q1_0223.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0223

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [899, 805, 217, 361, 681, 449, 790, 666, 210, 338, 450, 604, 620, 372, 41, 73, 137, 289, 545, 193, 321, 385, 641, 769, 82, 146, 274, 530, 194, 322, 386, 642, 770, 588, 84, 276, 532, 100, 292, 548, 772, 88, 152, 536, 104, 552, 648, 208, 336, 352, 448]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_899, vertices_805, vertices_217, vertices_361, vertices_681, vertices_449, vertices_790, vertices_666, vertices_210, vertices_338, vertices_450, vertices_604, vertices_620, vertices_372] (by decide +kernel)
  polygons := literalFinset [vertices_41, vertices_73, vertices_137, vertices_289, vertices_545, vertices_193, vertices_321, vertices_385, vertices_641, vertices_769, vertices_82, vertices_146, vertices_274, vertices_530, vertices_194, vertices_322, vertices_386, vertices_642, vertices_770, vertices_588, vertices_84, vertices_276, vertices_532, vertices_100, vertices_292, vertices_548, vertices_772, vertices_88, vertices_152, vertices_536, vertices_104, vertices_552, vertices_648, vertices_208, vertices_336, vertices_352, vertices_448] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_899), (false, vertices_805), (false, vertices_217), (false, vertices_361), (false, vertices_681), (false, vertices_449), (true, vertices_82), (true, vertices_146), (true, vertices_274), (true, vertices_530), (true, vertices_194), (true, vertices_322), (true, vertices_588), (true, vertices_84), (true, vertices_276), (true, vertices_532), (true, vertices_100), (true, vertices_536), (true, vertices_336)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 13 15 18 22 23 24 25 26 27
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_899) then 14 else
  if p.val = (false, vertices_805) then 16 else
  if p.val = (false, vertices_217) then 19 else
  if p.val = (false, vertices_361) then 20 else
  if p.val = (false, vertices_681) then 21 else
  if p.val = (false, vertices_449) then 0 else
  if p.val = (true, vertices_82) then 1 else
  if p.val = (true, vertices_146) then 2 else
  if p.val = (true, vertices_274) then 3 else
  if p.val = (true, vertices_530) then 4 else
  if p.val = (true, vertices_194) then 5 else
  if p.val = (true, vertices_322) then 6 else
  if p.val = (true, vertices_588) then 17 else
  if p.val = (true, vertices_84) then 7 else
  if p.val = (true, vertices_276) then 8 else
  if p.val = (true, vertices_532) then 9 else
  if p.val = (true, vertices_100) then 10 else
  if p.val = (true, vertices_536) then 11 else
  if p.val = (true, vertices_336) then 12 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_449), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_82), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_146), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_274), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_530), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_194), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_322), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_84), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_276), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_532), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_100), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_536), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_336), by decide +kernel⟩
  | 13 => Sum.inl 0
  | 14 => Sum.inr ⟨(false, vertices_899), by decide +kernel⟩
  | 15 => Sum.inl 1
  | 16 => Sum.inr ⟨(false, vertices_805), by decide +kernel⟩
  | 17 => Sum.inr ⟨(true, vertices_588), by decide +kernel⟩
  | 18 => Sum.inl 2
  | 19 => Sum.inr ⟨(false, vertices_217), by decide +kernel⟩
  | 20 => Sum.inr ⟨(false, vertices_361), by decide +kernel⟩
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
cert_row_4 0 0 2 3 6 8 666 146 1
cert_row_2 1 1 2 5 8 588
cert_row_4 2 0 1 3 7 8 790 274 1
cert_row_4 3 1 3 4 5 7 372 84 2
cert_rows
cert_pivot_2 6 2 0 1
cert_heightProof 4
cert_coverFacet 0 790
cert_cover_5 0 2 0 1 3 7 274 790 1
cert_coverFacet 1 666
cert_cover_5 1 0 0 2 3 6 146 666 1
cert_coverFacet 2 210
cert_cover_2 2 3 0 5 6 82 210 3
cert_coverFacet 3 338
cert_cover_2 3 3 0 5 7 82 338 3
cert_coverFacet 4 450
cert_cover_2 4 5 0 6 7 194 450 3
cert_coverFacet 5 604
cert_cover_5 5 1 1 2 3 5 588 604 2
cert_coverFacet 6 620
cert_cover_5 6 1 1 2 4 5 588 620 2
cert_coverFacet 7 372
cert_cover_5 7 3 1 3 4 5 84 372 2
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0223

end
end BundlePart12

section BundlePart13
/- Source: ProjectionCertificates/R_m14e10q1_0252.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0252

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [707, 309, 213, 645, 773, 809, 625, 902, 218, 410, 618, 778, 404, 376, 21, 133, 261, 517, 49, 81, 289, 545, 193, 577, 641, 769, 154, 74, 266, 522, 194, 578, 386, 642, 770, 148, 276, 388, 644, 772, 88, 280, 104, 296, 552, 776, 112, 304, 208, 400, 608]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_707, vertices_309, vertices_213, vertices_645, vertices_773, vertices_809, vertices_625, vertices_902, vertices_218, vertices_410, vertices_618, vertices_778, vertices_404, vertices_376] (by decide +kernel)
  polygons := literalFinset [vertices_21, vertices_133, vertices_261, vertices_517, vertices_49, vertices_81, vertices_289, vertices_545, vertices_193, vertices_577, vertices_641, vertices_769, vertices_154, vertices_74, vertices_266, vertices_522, vertices_194, vertices_578, vertices_386, vertices_642, vertices_770, vertices_148, vertices_276, vertices_388, vertices_644, vertices_772, vertices_88, vertices_280, vertices_104, vertices_296, vertices_552, vertices_776, vertices_112, vertices_304, vertices_208, vertices_400, vertices_608] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_707), (false, vertices_309), (false, vertices_213), (false, vertices_645), (false, vertices_773), (false, vertices_809), (false, vertices_625), (true, vertices_154), (true, vertices_74), (true, vertices_266), (true, vertices_522), (true, vertices_386), (true, vertices_770), (true, vertices_388), (true, vertices_88), (true, vertices_280), (true, vertices_104), (true, vertices_400)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 12 15 18 20 22 23 24 25 26
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_707) then 13 else
  if p.val = (false, vertices_309) then 16 else
  if p.val = (false, vertices_213) then 17 else
  if p.val = (false, vertices_645) then 0 else
  if p.val = (false, vertices_773) then 1 else
  if p.val = (false, vertices_809) then 19 else
  if p.val = (false, vertices_625) then 21 else
  if p.val = (true, vertices_154) then 14 else
  if p.val = (true, vertices_74) then 2 else
  if p.val = (true, vertices_266) then 3 else
  if p.val = (true, vertices_522) then 4 else
  if p.val = (true, vertices_386) then 5 else
  if p.val = (true, vertices_770) then 6 else
  if p.val = (true, vertices_388) then 7 else
  if p.val = (true, vertices_88) then 8 else
  if p.val = (true, vertices_280) then 9 else
  if p.val = (true, vertices_104) then 10 else
  if p.val = (true, vertices_400) then 11 else
  0
cert_priority
cert_nodeAtPriority_67 0 645 1 773 74 266 522 386 770 388 88 280 104 400 707 154 309 213 809 625
cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 6 7 8 902 386 1
cert_row_2 1 0 2 3 6 154
cert_row_4 2 0 2 4 5 8 618 74 2
cert_row_4 3 2 3 4 5 7 376 88 2
cert_rows
cert_pivot_2 1 6 0 2
cert_heightProof 4
cert_coverFacet 0 902
cert_cover_5 0 0 0 1 6 7 386 902 1
cert_coverFacet 1 218
cert_cover_5 1 1 0 2 3 5 154 218 3
cert_coverFacet 2 410
cert_cover_5 2 1 0 2 3 7 154 410 3
cert_coverFacet 3 618
cert_cover_5 3 2 0 2 4 5 74 618 2
cert_coverFacet 4 778
cert_cover_2 4 2 0 7 8 266 778 3
cert_coverFacet 5 404
cert_cover_2 5 3 1 6 7 148 404 3
cert_coverFacet 6 376
cert_cover_5 6 3 2 3 4 5 88 376 2
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0252

end
end BundlePart13

section BundlePart14
/- Source: ProjectionCertificates/R_m14e10q1_0253.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0253

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [595, 787, 781, 309, 613, 241, 654, 394, 778, 466, 738, 428, 676, 432, 531, 37, 261, 517, 49, 81, 273, 97, 577, 769, 138, 266, 522, 82, 274, 194, 578, 386, 642, 770, 140, 268, 524, 164, 292, 548, 644, 392, 776, 176, 304, 208, 400, 224, 608, 416, 672]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_595, vertices_787, vertices_781, vertices_309, vertices_613, vertices_241, vertices_654, vertices_394, vertices_778, vertices_466, vertices_738, vertices_428, vertices_676, vertices_432] (by decide +kernel)
  polygons := literalFinset [vertices_531, vertices_37, vertices_261, vertices_517, vertices_49, vertices_81, vertices_273, vertices_97, vertices_577, vertices_769, vertices_138, vertices_266, vertices_522, vertices_82, vertices_274, vertices_194, vertices_578, vertices_386, vertices_642, vertices_770, vertices_140, vertices_268, vertices_524, vertices_164, vertices_292, vertices_548, vertices_644, vertices_392, vertices_776, vertices_176, vertices_304, vertices_208, vertices_400, vertices_224, vertices_608, vertices_416, vertices_672] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_595), (false, vertices_787), (false, vertices_781), (false, vertices_309), (false, vertices_613), (false, vertices_241), (true, vertices_138), (true, vertices_266), (true, vertices_522), (true, vertices_194), (true, vertices_386), (true, vertices_642), (true, vertices_140), (true, vertices_164), (true, vertices_644), (true, vertices_392), (true, vertices_400), (true, vertices_416), (true, vertices_672)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 13 16 20 21 23 24 25 26 27
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_595) then 14 else
  if p.val = (false, vertices_787) then 15 else
  if p.val = (false, vertices_781) then 17 else
  if p.val = (false, vertices_309) then 18 else
  if p.val = (false, vertices_613) then 19 else
  if p.val = (false, vertices_241) then 22 else
  if p.val = (true, vertices_138) then 0 else
  if p.val = (true, vertices_266) then 1 else
  if p.val = (true, vertices_522) then 2 else
  if p.val = (true, vertices_194) then 3 else
  if p.val = (true, vertices_386) then 4 else
  if p.val = (true, vertices_642) then 5 else
  if p.val = (true, vertices_140) then 6 else
  if p.val = (true, vertices_164) then 7 else
  if p.val = (true, vertices_644) then 8 else
  if p.val = (true, vertices_392) then 9 else
  if p.val = (true, vertices_400) then 10 else
  if p.val = (true, vertices_416) then 11 else
  if p.val = (true, vertices_672) then 12 else
  0
cert_priority
cert_nodeAtPriority_30 0 138 1 266 522 194 386 642 140 164 644 392 400 416 672 595 787 781 309 613 241
cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 3 5 6 7 466 82 3
cert_row_4 1 0 4 5 6 8 738 194 1
cert_row_4 2 0 1 2 6 8 654 138 1
cert_row_4 3 1 2 4 6 7 428 140 2
cert_rows
cert_pivot_2 3 5 0 1
cert_heightProof 4
cert_coverFacet 0 654
cert_cover_5 0 2 0 1 2 6 138 654 1
cert_coverFacet 1 394
cert_cover_2 1 2 0 6 7 138 394 3
cert_coverFacet 2 778
cert_cover_2 2 2 0 7 8 266 778 3
cert_coverFacet 3 466
cert_cover_5 3 0 0 3 5 6 82 466 3
cert_coverFacet 4 738
cert_cover_5 4 1 0 4 5 6 194 738 1
cert_coverFacet 5 428
cert_cover_5 5 3 1 2 4 6 140 428 2
cert_coverFacet 6 676
cert_cover_2 6 4 1 6 8 164 676 3
cert_coverFacet 7 432
cert_cover_2 7 4 3 6 7 176 432 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0253

end
end BundlePart14

section BundlePart15
/- Source: ProjectionCertificates/R_m14e10q1_0254.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0254

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [79, 535, 451, 643, 525, 841, 929, 214, 690, 108, 812, 244, 564, 488, 7, 67, 131, 515, 13, 517, 73, 521, 321, 385, 641, 769, 22, 70, 146, 530, 194, 642, 44, 76, 524, 52, 212, 532, 100, 548, 104, 296, 328, 776, 176, 560, 224, 416, 672, 800, 448]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_79, vertices_535, vertices_451, vertices_643, vertices_525, vertices_841, vertices_929, vertices_214, vertices_690, vertices_108, vertices_812, vertices_244, vertices_564, vertices_488] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_67, vertices_131, vertices_515, vertices_13, vertices_517, vertices_73, vertices_521, vertices_321, vertices_385, vertices_641, vertices_769, vertices_22, vertices_70, vertices_146, vertices_530, vertices_194, vertices_642, vertices_44, vertices_76, vertices_524, vertices_52, vertices_212, vertices_532, vertices_100, vertices_548, vertices_104, vertices_296, vertices_328, vertices_776, vertices_176, vertices_560, vertices_224, vertices_416, vertices_672, vertices_800, vertices_448] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_79), (false, vertices_535), (false, vertices_451), (false, vertices_643), (false, vertices_525), (false, vertices_841), (false, vertices_929), (true, vertices_146), (true, vertices_44), (true, vertices_52), (true, vertices_212), (true, vertices_100), (true, vertices_548), (true, vertices_104), (true, vertices_296), (true, vertices_176), (true, vertices_560), (true, vertices_224)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 12 16 18 20 21 23 24 25 26
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_79) then 13 else
  if p.val = (false, vertices_535) then 14 else
  if p.val = (false, vertices_451) then 15 else
  if p.val = (false, vertices_643) then 0 else
  if p.val = (false, vertices_525) then 1 else
  if p.val = (false, vertices_841) then 19 else
  if p.val = (false, vertices_929) then 22 else
  if p.val = (true, vertices_146) then 2 else
  if p.val = (true, vertices_44) then 3 else
  if p.val = (true, vertices_52) then 4 else
  if p.val = (true, vertices_212) then 17 else
  if p.val = (true, vertices_100) then 5 else
  if p.val = (true, vertices_548) then 6 else
  if p.val = (true, vertices_104) then 7 else
  if p.val = (true, vertices_296) then 8 else
  if p.val = (true, vertices_176) then 9 else
  if p.val = (true, vertices_560) then 10 else
  if p.val = (true, vertices_224) then 11 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_643), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_525), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_146), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_44), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_52), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_100), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_548), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_104), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_296), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_176), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_560), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_224), by decide +kernel⟩
  | 12 => Sum.inl 0
  | 13 => Sum.inr ⟨(false, vertices_79), by decide +kernel⟩
  | 14 => Sum.inr ⟨(false, vertices_535), by decide +kernel⟩
  | 15 => Sum.inr ⟨(false, vertices_451), by decide +kernel⟩
  | 16 => Sum.inl 1
  | 17 => Sum.inr ⟨(true, vertices_212), by decide +kernel⟩
  | 18 => Sum.inl 2
  | 19 => Sum.inr ⟨(false, vertices_841), by decide +kernel⟩
  | 20 => Sum.inl 3
  | 21 => Sum.inl 4
  | 22 => Sum.inr ⟨(false, vertices_929), by decide +kernel⟩
  | 23 => Sum.inl 5
  | 24 => Sum.inl 6
  | 25 => Sum.inl 7
  | 26 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 3 4 6 8 690 146 2
cert_row_2 1 1 3 5 6 212
cert_row_4 2 1 2 4 7 8 812 44 3
cert_row_4 3 2 4 5 6 7 488 104 3
cert_rows
cert_pivot_2 0 3 1 2
cert_heightProof 4
cert_coverFacet 0 214
cert_cover_5 0 1 0 1 3 5 22 214 3
cert_coverFacet 1 690
cert_cover_5 1 0 0 3 4 6 146 690 2
cert_coverFacet 2 108
cert_cover_2 2 2 1 4 5 44 108 3
cert_coverFacet 3 812
cert_cover_5 3 2 1 2 4 7 44 812 3
cert_coverFacet 4 244
cert_cover_5 4 1 1 3 4 5 52 244 3
cert_coverFacet 5 564
cert_cover_2 5 3 1 4 8 52 564 3
cert_coverFacet 6 488
cert_cover_5 6 3 2 4 5 6 104 488 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0254

end
end BundlePart15

section BundlePart16
/- Source: ProjectionCertificates/R_m14e10q1_0258.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0258

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [659, 227, 835, 357, 905, 417, 598, 210, 572, 428, 844, 116, 696, 240, 67, 131, 515, 97, 161, 289, 321, 385, 641, 769, 82, 146, 530, 194, 578, 44, 268, 524, 52, 84, 532, 100, 292, 324, 580, 568, 168, 392, 648, 776, 112, 176, 208, 656, 224, 416, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_659, vertices_227, vertices_835, vertices_357, vertices_905, vertices_417, vertices_598, vertices_210, vertices_572, vertices_428, vertices_844, vertices_116, vertices_696, vertices_240] (by decide +kernel)
  polygons := literalFinset [vertices_67, vertices_131, vertices_515, vertices_97, vertices_161, vertices_289, vertices_321, vertices_385, vertices_641, vertices_769, vertices_82, vertices_146, vertices_530, vertices_194, vertices_578, vertices_44, vertices_268, vertices_524, vertices_52, vertices_84, vertices_532, vertices_100, vertices_292, vertices_324, vertices_580, vertices_568, vertices_168, vertices_392, vertices_648, vertices_776, vertices_112, vertices_176, vertices_208, vertices_656, vertices_224, vertices_416, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_659), (false, vertices_227), (false, vertices_835), (false, vertices_357), (false, vertices_905), (false, vertices_417), (true, vertices_82), (true, vertices_44), (true, vertices_268), (true, vertices_524), (true, vertices_52), (true, vertices_84), (true, vertices_532), (true, vertices_580), (true, vertices_568), (true, vertices_168), (true, vertices_112), (true, vertices_176), (true, vertices_208)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 13 17 19 22 23 24 25 26 27
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_659) then 14 else
  if p.val = (false, vertices_227) then 15 else
  if p.val = (false, vertices_835) then 16 else
  if p.val = (false, vertices_357) then 18 else
  if p.val = (false, vertices_905) then 20 else
  if p.val = (false, vertices_417) then 0 else
  if p.val = (true, vertices_82) then 1 else
  if p.val = (true, vertices_44) then 2 else
  if p.val = (true, vertices_268) then 3 else
  if p.val = (true, vertices_524) then 4 else
  if p.val = (true, vertices_52) then 5 else
  if p.val = (true, vertices_84) then 6 else
  if p.val = (true, vertices_532) then 7 else
  if p.val = (true, vertices_580) then 8 else
  if p.val = (true, vertices_568) then 21 else
  if p.val = (true, vertices_168) then 9 else
  if p.val = (true, vertices_112) then 10 else
  if p.val = (true, vertices_176) then 11 else
  if p.val = (true, vertices_208) then 12 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_417), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_82), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_44), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_268), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_524), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_52), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_84), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_532), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_580), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_168), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_112), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_176), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_208), by decide +kernel⟩
  | 13 => Sum.inl 0
  | 14 => Sum.inr ⟨(false, vertices_659), by decide +kernel⟩
  | 15 => Sum.inr ⟨(false, vertices_227), by decide +kernel⟩
  | 16 => Sum.inr ⟨(false, vertices_835), by decide +kernel⟩
  | 17 => Sum.inl 1
  | 18 => Sum.inr ⟨(false, vertices_357), by decide +kernel⟩
  | 19 => Sum.inl 2
  | 20 => Sum.inr ⟨(false, vertices_905), by decide +kernel⟩
  | 21 => Sum.inr ⟨(true, vertices_568), by decide +kernel⟩
  | 22 => Sum.inl 3
  | 23 => Sum.inl 4
  | 24 => Sum.inl 5
  | 25 => Sum.inl 6
  | 26 => Sum.inl 7
  | 27 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 3 5 8 598 82 1
cert_row_2 1 2 3 4 8 568
cert_row_4 2 1 2 4 6 7 428 44 3
cert_row_4 3 1 2 5 7 8 844 268 2
cert_rows
cert_pivot_2 0 3 4 1
cert_heightProof 4
cert_coverFacet 0 598
cert_cover_5 0 0 0 1 3 5 82 598 1
cert_coverFacet 1 210
cert_cover_2 1 3 0 5 6 82 210 3
cert_coverFacet 2 572
cert_cover_5 2 1 1 2 3 4 44 572 2
cert_coverFacet 3 428
cert_cover_5 3 2 1 2 4 6 44 428 3
cert_coverFacet 4 844
cert_cover_5 4 3 1 2 5 7 268 844 2
cert_coverFacet 5 116
cert_cover_2 5 3 1 4 5 52 116 3
cert_coverFacet 6 696
cert_cover_5 6 1 2 3 4 6 568 696 3
cert_coverFacet 7 240
cert_cover_2 7 4 3 5 6 112 240 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0258

end
end BundlePart16

section BundlePart17
/- Source: ProjectionCertificates/R_m14e10q1_0259.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0259

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [391, 147, 787, 781, 597, 197, 241, 810, 626, 178, 418, 428, 716, 744, 19, 131, 259, 69, 133, 261, 517, 81, 145, 529, 193, 769, 50, 146, 530, 162, 290, 546, 386, 770, 140, 268, 524, 196, 580, 388, 168, 296, 552, 712, 776, 112, 176, 592, 224, 608, 416]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_391, vertices_147, vertices_787, vertices_781, vertices_597, vertices_197, vertices_241, vertices_810, vertices_626, vertices_178, vertices_418, vertices_428, vertices_716, vertices_744] (by decide +kernel)
  polygons := literalFinset [vertices_19, vertices_131, vertices_259, vertices_69, vertices_133, vertices_261, vertices_517, vertices_81, vertices_145, vertices_529, vertices_193, vertices_769, vertices_50, vertices_146, vertices_530, vertices_162, vertices_290, vertices_546, vertices_386, vertices_770, vertices_140, vertices_268, vertices_524, vertices_196, vertices_580, vertices_388, vertices_168, vertices_296, vertices_552, vertices_712, vertices_776, vertices_112, vertices_176, vertices_592, vertices_224, vertices_608, vertices_416] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_391), (false, vertices_147), (false, vertices_787), (false, vertices_781), (false, vertices_597), (false, vertices_197), (false, vertices_241), (true, vertices_50), (true, vertices_162), (true, vertices_290), (true, vertices_546), (true, vertices_140), (true, vertices_168), (true, vertices_296), (true, vertices_552), (true, vertices_712), (true, vertices_608), (true, vertices_416)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 12 15 18 20 22 23 24 25 26
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_391) then 13 else
  if p.val = (false, vertices_147) then 0 else
  if p.val = (false, vertices_787) then 14 else
  if p.val = (false, vertices_781) then 16 else
  if p.val = (false, vertices_597) then 17 else
  if p.val = (false, vertices_197) then 1 else
  if p.val = (false, vertices_241) then 21 else
  if p.val = (true, vertices_50) then 2 else
  if p.val = (true, vertices_162) then 3 else
  if p.val = (true, vertices_290) then 4 else
  if p.val = (true, vertices_546) then 5 else
  if p.val = (true, vertices_140) then 6 else
  if p.val = (true, vertices_168) then 7 else
  if p.val = (true, vertices_296) then 8 else
  if p.val = (true, vertices_552) then 9 else
  if p.val = (true, vertices_712) then 19 else
  if p.val = (true, vertices_608) then 10 else
  if p.val = (true, vertices_416) then 11 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_147), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_197), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_50), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_162), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_290), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_546), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_140), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_168), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_296), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_552), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_608), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_416), by decide +kernel⟩
  | 12 => Sum.inl 0
  | 13 => Sum.inr ⟨(false, vertices_391), by decide +kernel⟩
  | 14 => Sum.inr ⟨(false, vertices_787), by decide +kernel⟩
  | 15 => Sum.inl 1
  | 16 => Sum.inr ⟨(false, vertices_781), by decide +kernel⟩
  | 17 => Sum.inr ⟨(false, vertices_597), by decide +kernel⟩
  | 18 => Sum.inl 2
  | 19 => Sum.inr ⟨(true, vertices_712), by decide +kernel⟩
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
cert_row_4 0 0 3 4 5 8 626 50 3
cert_row_2 1 2 5 6 8 712
cert_row_4 2 0 2 4 7 8 810 290 1
cert_row_4 3 1 2 4 6 7 428 140 2
cert_rows
cert_pivot_2 3 5 0 1
cert_heightProof 4
cert_coverFacet 0 810
cert_cover_5 0 2 0 2 4 7 290 810 1
cert_coverFacet 1 626
cert_cover_5 1 0 0 3 4 5 50 626 3
cert_coverFacet 2 178
cert_cover_2 2 3 0 4 6 50 178 3
cert_coverFacet 3 418
cert_cover_2 3 4 0 6 7 162 418 3
cert_coverFacet 4 428
cert_cover_5 4 3 1 2 4 6 140 428 2
cert_coverFacet 5 716
cert_cover_5 5 1 1 2 5 6 140 716 2
cert_coverFacet 6 744
cert_cover_5 6 1 2 4 5 6 168 744 2
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0259

end
end BundlePart17

section BundlePart18
/- Source: ProjectionCertificates/R_m14e10q1_0260.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0260

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [899, 109, 525, 421, 773, 601, 737, 542, 310, 774, 434, 722, 60, 248, 13, 37, 261, 517, 73, 521, 97, 161, 577, 385, 641, 769, 22, 262, 518, 306, 146, 530, 386, 642, 770, 28, 44, 524, 52, 292, 772, 56, 88, 536, 104, 176, 208, 592, 224, 416, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_899, vertices_109, vertices_525, vertices_421, vertices_773, vertices_601, vertices_737, vertices_542, vertices_310, vertices_774, vertices_434, vertices_722, vertices_60, vertices_248] (by decide +kernel)
  polygons := literalFinset [vertices_13, vertices_37, vertices_261, vertices_517, vertices_73, vertices_521, vertices_97, vertices_161, vertices_577, vertices_385, vertices_641, vertices_769, vertices_22, vertices_262, vertices_518, vertices_306, vertices_146, vertices_530, vertices_386, vertices_642, vertices_770, vertices_28, vertices_44, vertices_524, vertices_52, vertices_292, vertices_772, vertices_56, vertices_88, vertices_536, vertices_104, vertices_176, vertices_208, vertices_592, vertices_224, vertices_416, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_899), (false, vertices_109), (false, vertices_525), (false, vertices_421), (false, vertices_773), (false, vertices_601), (false, vertices_737), (true, vertices_22), (true, vertices_262), (true, vertices_518), (true, vertices_306), (true, vertices_146), (true, vertices_530), (true, vertices_28), (true, vertices_52), (true, vertices_56), (true, vertices_176), (true, vertices_208)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 12 15 18 20 21 23 24 25 26
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_899) then 13 else
  if p.val = (false, vertices_109) then 16 else
  if p.val = (false, vertices_525) then 0 else
  if p.val = (false, vertices_421) then 17 else
  if p.val = (false, vertices_773) then 1 else
  if p.val = (false, vertices_601) then 19 else
  if p.val = (false, vertices_737) then 22 else
  if p.val = (true, vertices_22) then 2 else
  if p.val = (true, vertices_262) then 3 else
  if p.val = (true, vertices_518) then 4 else
  if p.val = (true, vertices_306) then 14 else
  if p.val = (true, vertices_146) then 5 else
  if p.val = (true, vertices_530) then 6 else
  if p.val = (true, vertices_28) then 7 else
  if p.val = (true, vertices_52) then 8 else
  if p.val = (true, vertices_56) then 9 else
  if p.val = (true, vertices_176) then 10 else
  if p.val = (true, vertices_208) then 11 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_525), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_773), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_22), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_262), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_518), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_146), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_530), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_28), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_52), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_56), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_176), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_208), by decide +kernel⟩
  | 12 => Sum.inl 0
  | 13 => Sum.inr ⟨(false, vertices_899), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_306), by decide +kernel⟩
  | 15 => Sum.inl 1
  | 16 => Sum.inr ⟨(false, vertices_109), by decide +kernel⟩
  | 17 => Sum.inr ⟨(false, vertices_421), by decide +kernel⟩
  | 18 => Sum.inl 2
  | 19 => Sum.inr ⟨(false, vertices_601), by decide +kernel⟩
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
cert_row_2 0 0 3 4 7 306
cert_row_4 1 0 1 2 3 8 542 22 2
cert_row_4 2 0 3 5 6 8 722 146 2
cert_row_4 3 2 3 4 5 6 248 56 3
cert_rows
cert_pivot_2 7 1 0 2
cert_heightProof 4
cert_coverFacet 0 542
cert_cover_5 0 1 0 1 2 3 22 542 2
cert_coverFacet 1 310
cert_cover_5 1 0 0 1 3 4 22 310 3
cert_coverFacet 2 774
cert_cover_2 2 1 0 7 8 262 774 3
cert_coverFacet 3 434
cert_cover_5 3 0 0 3 4 6 306 434 3
cert_coverFacet 4 722
cert_cover_5 4 2 0 3 5 6 146 722 2
cert_coverFacet 5 60
cert_cover_2 5 2 1 3 4 28 60 3
cert_coverFacet 6 248
cert_cover_5 6 3 2 3 4 5 56 248 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0260

end
end BundlePart18

section BundlePart19
/- Source: ProjectionCertificates/R_m14e10q1_0263.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0263

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [47, 171, 29, 341, 421, 217, 961, 526, 550, 714, 930, 540, 820, 856, 43, 13, 21, 37, 261, 25, 137, 81, 161, 193, 321, 385, 14, 38, 518, 138, 522, 162, 546, 642, 28, 524, 276, 532, 292, 548, 88, 536, 200, 584, 336, 784, 416, 800, 704, 832, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_47, vertices_171, vertices_29, vertices_341, vertices_421, vertices_217, vertices_961, vertices_526, vertices_550, vertices_714, vertices_930, vertices_540, vertices_820, vertices_856] (by decide +kernel)
  polygons := literalFinset [vertices_43, vertices_13, vertices_21, vertices_37, vertices_261, vertices_25, vertices_137, vertices_81, vertices_161, vertices_193, vertices_321, vertices_385, vertices_14, vertices_38, vertices_518, vertices_138, vertices_522, vertices_162, vertices_546, vertices_642, vertices_28, vertices_524, vertices_276, vertices_532, vertices_292, vertices_548, vertices_88, vertices_536, vertices_200, vertices_584, vertices_336, vertices_784, vertices_416, vertices_800, vertices_704, vertices_832, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_47), (false, vertices_171), (false, vertices_29), (false, vertices_341), (false, vertices_421), (false, vertices_217), (false, vertices_961), (true, vertices_518), (true, vertices_522), (true, vertices_546), (true, vertices_642), (true, vertices_524), (true, vertices_532), (true, vertices_548), (true, vertices_536), (true, vertices_584), (true, vertices_784), (true, vertices_800)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 12 15 18 20 21 22 24 25 26
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_47) then 13 else
  if p.val = (false, vertices_171) then 14 else
  if p.val = (false, vertices_29) then 0 else
  if p.val = (false, vertices_341) then 16 else
  if p.val = (false, vertices_421) then 17 else
  if p.val = (false, vertices_217) then 19 else
  if p.val = (false, vertices_961) then 23 else
  if p.val = (true, vertices_518) then 1 else
  if p.val = (true, vertices_522) then 2 else
  if p.val = (true, vertices_546) then 3 else
  if p.val = (true, vertices_642) then 4 else
  if p.val = (true, vertices_524) then 5 else
  if p.val = (true, vertices_532) then 6 else
  if p.val = (true, vertices_548) then 7 else
  if p.val = (true, vertices_536) then 8 else
  if p.val = (true, vertices_584) then 9 else
  if p.val = (true, vertices_784) then 10 else
  if p.val = (true, vertices_800) then 11 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_29), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_518), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_522), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_546), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_642), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_524), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_532), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_548), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_536), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_584), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_784), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_800), by decide +kernel⟩
  | 12 => Sum.inl 0
  | 13 => Sum.inr ⟨(false, vertices_47), by decide +kernel⟩
  | 14 => Sum.inr ⟨(false, vertices_171), by decide +kernel⟩
  | 15 => Sum.inl 1
  | 16 => Sum.inr ⟨(false, vertices_341), by decide +kernel⟩
  | 17 => Sum.inr ⟨(false, vertices_421), by decide +kernel⟩
  | 18 => Sum.inl 2
  | 19 => Sum.inr ⟨(false, vertices_217), by decide +kernel⟩
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
cert_row_4 0 1 3 4 7 8 820 276 2
cert_row_4 1 0 4 6 7 8 930 162 3
cert_row_4 2 0 2 5 6 8 714 138 2
cert_row_4 3 2 3 5 7 8 856 88 3
cert_rows
cert_pivot_2 1 4 0 2
cert_heightProof 4
cert_coverFacet 0 526
cert_cover_2 0 1 0 2 8 14 526 3
cert_coverFacet 1 550
cert_cover_2 1 1 0 4 8 38 550 3
cert_coverFacet 2 714
cert_cover_5 2 2 0 2 5 6 138 714 2
cert_coverFacet 3 930
cert_cover_5 3 1 0 4 6 7 162 930 3
cert_coverFacet 4 540
cert_cover_2 4 2 1 3 8 28 540 3
cert_coverFacet 5 820
cert_cover_5 5 0 1 3 4 7 276 820 2
cert_coverFacet 6 856
cert_cover_5 6 3 2 3 5 7 88 856 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0263

end
end BundlePart19

section BundlePart20
/- Source: ProjectionCertificates/R_m14e10q1_0268.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0268

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [79, 535, 195, 899, 525, 841, 481, 214, 690, 364, 556, 244, 564, 936, 7, 67, 131, 515, 13, 517, 73, 521, 193, 321, 385, 769, 22, 70, 146, 530, 194, 642, 44, 76, 524, 52, 212, 532, 100, 548, 296, 552, 328, 776, 176, 560, 224, 352, 416, 672, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_79, vertices_535, vertices_195, vertices_899, vertices_525, vertices_841, vertices_481, vertices_214, vertices_690, vertices_364, vertices_556, vertices_244, vertices_564, vertices_936] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_67, vertices_131, vertices_515, vertices_13, vertices_517, vertices_73, vertices_521, vertices_193, vertices_321, vertices_385, vertices_769, vertices_22, vertices_70, vertices_146, vertices_530, vertices_194, vertices_642, vertices_44, vertices_76, vertices_524, vertices_52, vertices_212, vertices_532, vertices_100, vertices_548, vertices_296, vertices_552, vertices_328, vertices_776, vertices_176, vertices_560, vertices_224, vertices_352, vertices_416, vertices_672, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_79), (false, vertices_535), (false, vertices_195), (false, vertices_899), (false, vertices_525), (false, vertices_841), (false, vertices_481), (true, vertices_146), (true, vertices_44), (true, vertices_52), (true, vertices_212), (true, vertices_100), (true, vertices_548), (true, vertices_296), (true, vertices_552), (true, vertices_176), (true, vertices_560), (true, vertices_672)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 12 16 18 20 21 23 24 25 26
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_79) then 13 else
  if p.val = (false, vertices_535) then 14 else
  if p.val = (false, vertices_195) then 0 else
  if p.val = (false, vertices_899) then 15 else
  if p.val = (false, vertices_525) then 1 else
  if p.val = (false, vertices_841) then 19 else
  if p.val = (false, vertices_481) then 22 else
  if p.val = (true, vertices_146) then 2 else
  if p.val = (true, vertices_44) then 3 else
  if p.val = (true, vertices_52) then 4 else
  if p.val = (true, vertices_212) then 17 else
  if p.val = (true, vertices_100) then 5 else
  if p.val = (true, vertices_548) then 6 else
  if p.val = (true, vertices_296) then 7 else
  if p.val = (true, vertices_552) then 8 else
  if p.val = (true, vertices_176) then 9 else
  if p.val = (true, vertices_560) then 10 else
  if p.val = (true, vertices_672) then 11 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_195), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_525), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_146), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_44), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_52), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_100), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_548), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_296), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_552), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_176), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_560), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_672), by decide +kernel⟩
  | 12 => Sum.inl 0
  | 13 => Sum.inr ⟨(false, vertices_79), by decide +kernel⟩
  | 14 => Sum.inr ⟨(false, vertices_535), by decide +kernel⟩
  | 15 => Sum.inr ⟨(false, vertices_899), by decide +kernel⟩
  | 16 => Sum.inl 1
  | 17 => Sum.inr ⟨(true, vertices_212), by decide +kernel⟩
  | 18 => Sum.inl 2
  | 19 => Sum.inr ⟨(false, vertices_841), by decide +kernel⟩
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
cert_row_4 0 0 3 4 6 8 690 146 2
cert_row_2 1 1 3 5 6 212
cert_row_4 2 1 2 4 5 7 364 44 3
cert_row_4 3 2 4 6 7 8 936 296 2
cert_rows
cert_pivot_2 0 3 1 2
cert_heightProof 4
cert_coverFacet 0 214
cert_cover_5 0 1 0 1 3 5 22 214 3
cert_coverFacet 1 690
cert_cover_5 1 0 0 3 4 6 146 690 2
cert_coverFacet 2 364
cert_cover_5 2 2 1 2 4 5 44 364 3
cert_coverFacet 3 556
cert_cover_2 3 2 1 4 8 44 556 3
cert_coverFacet 4 244
cert_cover_5 4 1 1 3 4 5 52 244 3
cert_coverFacet 5 564
cert_cover_2 5 3 1 4 8 52 564 3
cert_coverFacet 6 936
cert_cover_5 6 3 2 4 6 7 296 936 2
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0268

end
end BundlePart20

section BundlePart21
/- Source: ProjectionCertificates/R_m14e10q1_0282.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0282

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [899, 101, 677, 453, 809, 369, 654, 314, 154, 778, 466, 124, 220, 556, 37, 69, 133, 97, 289, 545, 321, 385, 641, 769, 26, 138, 266, 522, 146, 274, 386, 642, 770, 92, 44, 140, 524, 100, 548, 196, 644, 56, 152, 296, 552, 776, 112, 304, 208, 336, 448]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_899, vertices_101, vertices_677, vertices_453, vertices_809, vertices_369, vertices_654, vertices_314, vertices_154, vertices_778, vertices_466, vertices_124, vertices_220, vertices_556] (by decide +kernel)
  polygons := literalFinset [vertices_37, vertices_69, vertices_133, vertices_97, vertices_289, vertices_545, vertices_321, vertices_385, vertices_641, vertices_769, vertices_26, vertices_138, vertices_266, vertices_522, vertices_146, vertices_274, vertices_386, vertices_642, vertices_770, vertices_92, vertices_44, vertices_140, vertices_524, vertices_100, vertices_548, vertices_196, vertices_644, vertices_56, vertices_152, vertices_296, vertices_552, vertices_776, vertices_112, vertices_304, vertices_208, vertices_336, vertices_448] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_899), (false, vertices_101), (false, vertices_677), (false, vertices_453), (false, vertices_809), (false, vertices_369), (true, vertices_26), (true, vertices_138), (true, vertices_266), (true, vertices_522), (true, vertices_146), (true, vertices_274), (true, vertices_92), (true, vertices_44), (true, vertices_140), (true, vertices_524), (true, vertices_56), (true, vertices_152), (true, vertices_208)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 13 15 19 21 23 24 25 26 27
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_899) then 14 else
  if p.val = (false, vertices_101) then 0 else
  if p.val = (false, vertices_677) then 16 else
  if p.val = (false, vertices_453) then 17 else
  if p.val = (false, vertices_809) then 20 else
  if p.val = (false, vertices_369) then 22 else
  if p.val = (true, vertices_26) then 1 else
  if p.val = (true, vertices_138) then 2 else
  if p.val = (true, vertices_266) then 3 else
  if p.val = (true, vertices_522) then 4 else
  if p.val = (true, vertices_146) then 5 else
  if p.val = (true, vertices_274) then 6 else
  if p.val = (true, vertices_92) then 18 else
  if p.val = (true, vertices_44) then 7 else
  if p.val = (true, vertices_140) then 8 else
  if p.val = (true, vertices_524) then 9 else
  if p.val = (true, vertices_56) then 10 else
  if p.val = (true, vertices_152) then 11 else
  if p.val = (true, vertices_208) then 12 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_101), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_26), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_138), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_266), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_522), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_146), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_274), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_44), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_140), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_524), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_56), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_152), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_208), by decide +kernel⟩
  | 13 => Sum.inl 0
  | 14 => Sum.inr ⟨(false, vertices_899), by decide +kernel⟩
  | 15 => Sum.inl 1
  | 16 => Sum.inr ⟨(false, vertices_677), by decide +kernel⟩
  | 17 => Sum.inr ⟨(false, vertices_453), by decide +kernel⟩
  | 18 => Sum.inr ⟨(true, vertices_92), by decide +kernel⟩
  | 19 => Sum.inl 2
  | 20 => Sum.inr ⟨(false, vertices_809), by decide +kernel⟩
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
cert_row_4 0 0 1 2 6 8 654 138 1
cert_row_2 1 1 2 3 5 92
cert_row_4 2 0 2 3 4 7 314 26 3
cert_row_4 3 0 3 5 6 7 466 146 2
cert_rows
cert_pivot_2 8 1 2 0
cert_heightProof 4
cert_coverFacet 0 654
cert_cover_5 0 0 0 1 2 6 138 654 1
cert_coverFacet 1 314
cert_cover_5 1 2 0 2 3 4 26 314 3
cert_coverFacet 2 154
cert_cover_2 2 2 0 3 6 26 154 3
cert_coverFacet 3 778
cert_cover_2 3 2 0 7 8 266 778 3
cert_coverFacet 4 466
cert_cover_5 4 3 0 3 5 6 146 466 2
cert_coverFacet 5 124
cert_cover_5 5 1 1 2 3 4 92 124 3
cert_coverFacet 6 220
cert_cover_5 6 1 1 2 3 6 92 220 3
cert_coverFacet 7 556
cert_cover_2 7 2 1 4 8 44 556 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0282

end
end BundlePart21

section BundlePart22
/- Source: ProjectionCertificates/R_m14e10q1_0283.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0283

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [327, 595, 275, 589, 661, 389, 433, 618, 690, 306, 354, 684, 460, 488, 19, 67, 259, 69, 133, 261, 517, 145, 273, 529, 577, 385, 50, 274, 530, 98, 290, 546, 322, 578, 76, 140, 524, 324, 388, 644, 104, 168, 552, 456, 584, 176, 304, 656, 352, 416, 672]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_327, vertices_595, vertices_275, vertices_589, vertices_661, vertices_389, vertices_433, vertices_618, vertices_690, vertices_306, vertices_354, vertices_684, vertices_460, vertices_488] (by decide +kernel)
  polygons := literalFinset [vertices_19, vertices_67, vertices_259, vertices_69, vertices_133, vertices_261, vertices_517, vertices_145, vertices_273, vertices_529, vertices_577, vertices_385, vertices_50, vertices_274, vertices_530, vertices_98, vertices_290, vertices_546, vertices_322, vertices_578, vertices_76, vertices_140, vertices_524, vertices_324, vertices_388, vertices_644, vertices_104, vertices_168, vertices_552, vertices_456, vertices_584, vertices_176, vertices_304, vertices_656, vertices_352, vertices_416, vertices_672] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_327), (false, vertices_595), (false, vertices_275), (false, vertices_589), (false, vertices_661), (false, vertices_389), (false, vertices_433), (true, vertices_50), (true, vertices_98), (true, vertices_290), (true, vertices_546), (true, vertices_140), (true, vertices_104), (true, vertices_168), (true, vertices_552), (true, vertices_456), (true, vertices_352), (true, vertices_672)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 12 15 18 20 22 23 24 25 26
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_327) then 13 else
  if p.val = (false, vertices_595) then 14 else
  if p.val = (false, vertices_275) then 0 else
  if p.val = (false, vertices_589) then 16 else
  if p.val = (false, vertices_661) then 17 else
  if p.val = (false, vertices_389) then 1 else
  if p.val = (false, vertices_433) then 21 else
  if p.val = (true, vertices_50) then 2 else
  if p.val = (true, vertices_98) then 3 else
  if p.val = (true, vertices_290) then 4 else
  if p.val = (true, vertices_546) then 5 else
  if p.val = (true, vertices_140) then 6 else
  if p.val = (true, vertices_104) then 7 else
  if p.val = (true, vertices_168) then 8 else
  if p.val = (true, vertices_552) then 9 else
  if p.val = (true, vertices_456) then 19 else
  if p.val = (true, vertices_352) then 10 else
  if p.val = (true, vertices_672) then 11 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_275), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_389), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_50), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_98), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_290), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_546), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_140), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_104), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_168), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_552), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_352), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_672), by decide +kernel⟩
  | 12 => Sum.inl 0
  | 13 => Sum.inr ⟨(false, vertices_327), by decide +kernel⟩
  | 14 => Sum.inr ⟨(false, vertices_595), by decide +kernel⟩
  | 15 => Sum.inl 1
  | 16 => Sum.inr ⟨(false, vertices_589), by decide +kernel⟩
  | 17 => Sum.inr ⟨(false, vertices_661), by decide +kernel⟩
  | 18 => Sum.inl 2
  | 19 => Sum.inr ⟨(true, vertices_456), by decide +kernel⟩
  | 20 => Sum.inl 3
  | 21 => Sum.inr ⟨(false, vertices_433), by decide +kernel⟩
  | 22 => Sum.inl 4
  | 23 => Sum.inl 5
  | 24 => Sum.inl 6
  | 25 => Sum.inl 7
  | 26 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 2 5 6 7 456
cert_row_4 1 0 2 4 5 8 618 98 1
cert_row_4 2 0 3 4 6 8 690 50 3
cert_row_4 3 1 2 4 6 8 684 140 2
cert_rows
cert_pivot_2 7 5 0 1
cert_heightProof 4
cert_coverFacet 0 618
cert_cover_5 0 1 0 2 4 5 98 618 1
cert_coverFacet 1 690
cert_cover_5 1 2 0 3 4 6 50 690 3
cert_coverFacet 2 306
cert_cover_2 2 3 0 4 7 50 306 3
cert_coverFacet 3 354
cert_cover_2 3 4 0 5 7 98 354 3
cert_coverFacet 4 684
cert_cover_5 4 3 1 2 4 6 140 684 2
cert_coverFacet 5 460
cert_cover_5 5 0 1 2 5 6 76 460 3
cert_coverFacet 6 488
cert_cover_5 6 0 2 4 5 6 104 488 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0283

end
end BundlePart22

section BundlePart23
/- Source: ProjectionCertificates/R_m14e10q1_0284.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0284

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [403, 803, 707, 213, 841, 337, 678, 418, 124, 812, 716, 180, 376, 432, 131, 259, 515, 81, 145, 273, 193, 321, 577, 769, 162, 290, 546, 386, 642, 44, 76, 524, 52, 84, 148, 164, 548, 196, 644, 120, 296, 328, 584, 776, 176, 304, 336, 400, 416, 800, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_403, vertices_803, vertices_707, vertices_213, vertices_841, vertices_337, vertices_678, vertices_418, vertices_124, vertices_812, vertices_716, vertices_180, vertices_376, vertices_432] (by decide +kernel)
  polygons := literalFinset [vertices_131, vertices_259, vertices_515, vertices_81, vertices_145, vertices_273, vertices_193, vertices_321, vertices_577, vertices_769, vertices_162, vertices_290, vertices_546, vertices_386, vertices_642, vertices_44, vertices_76, vertices_524, vertices_52, vertices_84, vertices_148, vertices_164, vertices_548, vertices_196, vertices_644, vertices_120, vertices_296, vertices_328, vertices_584, vertices_776, vertices_176, vertices_304, vertices_336, vertices_400, vertices_416, vertices_800, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_403), (false, vertices_803), (false, vertices_707), (false, vertices_213), (false, vertices_841), (false, vertices_337), (true, vertices_162), (true, vertices_44), (true, vertices_76), (true, vertices_524), (true, vertices_52), (true, vertices_164), (true, vertices_548), (true, vertices_644), (true, vertices_120), (true, vertices_296), (true, vertices_176), (true, vertices_304), (true, vertices_416)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 13 17 19 22 23 24 25 26 27
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_403) then 14 else
  if p.val = (false, vertices_803) then 15 else
  if p.val = (false, vertices_707) then 16 else
  if p.val = (false, vertices_213) then 18 else
  if p.val = (false, vertices_841) then 20 else
  if p.val = (false, vertices_337) then 0 else
  if p.val = (true, vertices_162) then 1 else
  if p.val = (true, vertices_44) then 2 else
  if p.val = (true, vertices_76) then 3 else
  if p.val = (true, vertices_524) then 4 else
  if p.val = (true, vertices_52) then 5 else
  if p.val = (true, vertices_164) then 6 else
  if p.val = (true, vertices_548) then 7 else
  if p.val = (true, vertices_644) then 8 else
  if p.val = (true, vertices_120) then 21 else
  if p.val = (true, vertices_296) then 9 else
  if p.val = (true, vertices_176) then 10 else
  if p.val = (true, vertices_304) then 11 else
  if p.val = (true, vertices_416) then 12 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_337), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_162), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_44), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_76), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_524), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_52), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_164), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_548), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_644), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_296), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_176), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_304), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_416), by decide +kernel⟩
  | 13 => Sum.inl 0
  | 14 => Sum.inr ⟨(false, vertices_403), by decide +kernel⟩
  | 15 => Sum.inr ⟨(false, vertices_803), by decide +kernel⟩
  | 16 => Sum.inr ⟨(false, vertices_707), by decide +kernel⟩
  | 17 => Sum.inl 1
  | 18 => Sum.inr ⟨(false, vertices_213), by decide +kernel⟩
  | 19 => Sum.inl 2
  | 20 => Sum.inr ⟨(false, vertices_841), by decide +kernel⟩
  | 21 => Sum.inr ⟨(true, vertices_120), by decide +kernel⟩
  | 22 => Sum.inl 3
  | 23 => Sum.inl 4
  | 24 => Sum.inl 5
  | 25 => Sum.inl 6
  | 26 => Sum.inl 7
  | 27 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 2 3 4 5 120
cert_row_4 1 0 1 4 6 8 678 162 1
cert_row_4 2 1 2 4 7 8 812 44 3
cert_row_4 3 1 2 5 6 8 716 76 3
cert_rows
cert_pivot_2 3 0 4 1
cert_heightProof 4
cert_coverFacet 0 678
cert_cover_5 0 1 0 1 4 6 162 678 1
cert_coverFacet 1 418
cert_cover_2 1 4 0 6 7 162 418 3
cert_coverFacet 2 124
cert_cover_5 2 0 1 2 3 4 44 124 2
cert_coverFacet 3 812
cert_cover_5 3 2 1 2 4 7 44 812 3
cert_coverFacet 4 716
cert_cover_5 4 3 1 2 5 6 76 716 3
cert_coverFacet 5 180
cert_cover_2 5 3 1 4 6 52 180 3
cert_coverFacet 6 376
cert_cover_5 6 0 2 3 4 7 120 376 3
cert_coverFacet 7 432
cert_cover_2 7 4 3 6 7 176 432 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0284

end
end BundlePart23

section BundlePart24
/- Source: ProjectionCertificates/R_m14e10q1_0296.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0296

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [227, 789, 421, 709, 617, 801, 406, 346, 362, 210, 418, 660, 824, 728, 133, 261, 517, 97, 161, 289, 545, 193, 577, 769, 330, 82, 146, 274, 98, 162, 290, 194, 386, 148, 276, 532, 388, 644, 88, 280, 536, 104, 296, 552, 584, 208, 656, 784, 416, 800, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_227, vertices_789, vertices_421, vertices_709, vertices_617, vertices_801, vertices_406, vertices_346, vertices_362, vertices_210, vertices_418, vertices_660, vertices_824, vertices_728] (by decide +kernel)
  polygons := literalFinset [vertices_133, vertices_261, vertices_517, vertices_97, vertices_161, vertices_289, vertices_545, vertices_193, vertices_577, vertices_769, vertices_330, vertices_82, vertices_146, vertices_274, vertices_98, vertices_162, vertices_290, vertices_194, vertices_386, vertices_148, vertices_276, vertices_532, vertices_388, vertices_644, vertices_88, vertices_280, vertices_536, vertices_104, vertices_296, vertices_552, vertices_584, vertices_208, vertices_656, vertices_784, vertices_416, vertices_800, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_227), (false, vertices_789), (false, vertices_421), (false, vertices_709), (false, vertices_617), (false, vertices_801), (true, vertices_330), (true, vertices_82), (true, vertices_146), (true, vertices_274), (true, vertices_290), (true, vertices_386), (true, vertices_148), (true, vertices_88), (true, vertices_280), (true, vertices_536), (true, vertices_296), (true, vertices_208), (true, vertices_656)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 13 16 20 22 23 24 25 26 27
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_227) then 14 else
  if p.val = (false, vertices_789) then 17 else
  if p.val = (false, vertices_421) then 18 else
  if p.val = (false, vertices_709) then 19 else
  if p.val = (false, vertices_617) then 21 else
  if p.val = (false, vertices_801) then 0 else
  if p.val = (true, vertices_330) then 15 else
  if p.val = (true, vertices_82) then 1 else
  if p.val = (true, vertices_146) then 2 else
  if p.val = (true, vertices_274) then 3 else
  if p.val = (true, vertices_290) then 4 else
  if p.val = (true, vertices_386) then 5 else
  if p.val = (true, vertices_148) then 6 else
  if p.val = (true, vertices_88) then 7 else
  if p.val = (true, vertices_280) then 8 else
  if p.val = (true, vertices_536) then 9 else
  if p.val = (true, vertices_296) then 10 else
  if p.val = (true, vertices_208) then 11 else
  if p.val = (true, vertices_656) then 12 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_801), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_82), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_146), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_274), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_290), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_386), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_148), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_88), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_280), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_536), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_296), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_208), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_656), by decide +kernel⟩
  | 13 => Sum.inl 0
  | 14 => Sum.inr ⟨(false, vertices_227), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_330), by decide +kernel⟩
  | 16 => Sum.inl 1
  | 17 => Sum.inr ⟨(false, vertices_789), by decide +kernel⟩
  | 18 => Sum.inr ⟨(false, vertices_421), by decide +kernel⟩
  | 19 => Sum.inr ⟨(false, vertices_709), by decide +kernel⟩
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
cert_row_4 0 0 1 3 6 7 406 146 1
cert_row_2 1 0 2 5 7 330
cert_row_4 2 2 3 4 7 8 824 280 2
cert_row_4 3 2 3 5 6 8 728 88 3
cert_rows
cert_pivot_2 1 0 4 2
cert_heightProof 4
cert_coverFacet 0 406
cert_cover_5 0 0 0 1 3 6 146 406 1
cert_coverFacet 1 346
cert_cover_5 1 1 0 2 3 5 330 346 2
cert_coverFacet 2 362
cert_cover_5 2 1 0 2 4 5 330 362 2
cert_coverFacet 3 210
cert_cover_2 3 3 0 5 6 82 210 3
cert_coverFacet 4 418
cert_cover_2 4 4 0 6 7 162 418 3
cert_coverFacet 5 660
cert_cover_2 5 3 1 6 8 148 660 3
cert_coverFacet 6 824
cert_cover_5 6 2 2 3 4 7 280 824 2
cert_coverFacet 7 728
cert_cover_5 7 3 2 3 5 6 88 728 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0296

end
end BundlePart24

section BundlePart25
/- Source: ProjectionCertificates/R_m14e10q1_0311.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0311

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [271, 527, 357, 677, 841, 625, 406, 646, 602, 282, 690, 420, 376, 432, 15, 37, 261, 517, 265, 521, 97, 545, 321, 577, 134, 262, 518, 26, 266, 522, 146, 274, 530, 642, 164, 292, 388, 644, 88, 280, 328, 584, 112, 176, 304, 560, 592, 400, 352, 416, 672]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_271, vertices_527, vertices_357, vertices_677, vertices_841, vertices_625, vertices_406, vertices_646, vertices_602, vertices_282, vertices_690, vertices_420, vertices_376, vertices_432] (by decide +kernel)
  polygons := literalFinset [vertices_15, vertices_37, vertices_261, vertices_517, vertices_265, vertices_521, vertices_97, vertices_545, vertices_321, vertices_577, vertices_134, vertices_262, vertices_518, vertices_26, vertices_266, vertices_522, vertices_146, vertices_274, vertices_530, vertices_642, vertices_164, vertices_292, vertices_388, vertices_644, vertices_88, vertices_280, vertices_328, vertices_584, vertices_112, vertices_176, vertices_304, vertices_560, vertices_592, vertices_400, vertices_352, vertices_416, vertices_672] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_271), (false, vertices_527), (false, vertices_357), (false, vertices_677), (false, vertices_841), (false, vertices_625), (true, vertices_134), (true, vertices_26), (true, vertices_146), (true, vertices_274), (true, vertices_530), (true, vertices_642), (true, vertices_388), (true, vertices_88), (true, vertices_280), (true, vertices_176), (true, vertices_304), (true, vertices_400), (true, vertices_416)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 13 16 19 21 23 24 25 26 27
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_271) then 14 else
  if p.val = (false, vertices_527) then 15 else
  if p.val = (false, vertices_357) then 17 else
  if p.val = (false, vertices_677) then 18 else
  if p.val = (false, vertices_841) then 20 else
  if p.val = (false, vertices_625) then 22 else
  if p.val = (true, vertices_134) then 0 else
  if p.val = (true, vertices_26) then 1 else
  if p.val = (true, vertices_146) then 2 else
  if p.val = (true, vertices_274) then 3 else
  if p.val = (true, vertices_530) then 4 else
  if p.val = (true, vertices_642) then 5 else
  if p.val = (true, vertices_388) then 6 else
  if p.val = (true, vertices_88) then 7 else
  if p.val = (true, vertices_280) then 8 else
  if p.val = (true, vertices_176) then 9 else
  if p.val = (true, vertices_304) then 10 else
  if p.val = (true, vertices_400) then 11 else
  if p.val = (true, vertices_416) then 12 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_134), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_26), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_146), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_274), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_530), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_642), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_388), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_88), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_280), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_176), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_304), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_400), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_416), by decide +kernel⟩
  | 13 => Sum.inl 0
  | 14 => Sum.inr ⟨(false, vertices_271), by decide +kernel⟩
  | 15 => Sum.inr ⟨(false, vertices_527), by decide +kernel⟩
  | 16 => Sum.inl 1
  | 17 => Sum.inr ⟨(false, vertices_357), by decide +kernel⟩
  | 18 => Sum.inr ⟨(false, vertices_677), by decide +kernel⟩
  | 19 => Sum.inl 2
  | 20 => Sum.inr ⟨(false, vertices_841), by decide +kernel⟩
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
cert_row_4 0 0 1 3 6 7 406 134 2
cert_row_4 1 0 3 4 6 8 690 146 2
cert_row_4 2 0 2 3 5 8 602 26 3
cert_row_4 3 2 3 4 5 7 376 88 2
cert_rows
cert_pivot_2 1 6 0 2
cert_heightProof 4
cert_coverFacet 0 406
cert_cover_5 0 0 0 1 3 6 134 406 2
cert_coverFacet 1 646
cert_cover_2 1 1 0 6 8 134 646 3
cert_coverFacet 2 602
cert_cover_5 2 2 0 2 3 5 26 602 3
cert_coverFacet 3 282
cert_cover_2 3 2 0 3 7 26 282 3
cert_coverFacet 4 690
cert_cover_5 4 1 0 3 4 6 146 690 2
cert_coverFacet 5 420
cert_cover_2 5 4 1 6 7 164 420 3
cert_coverFacet 6 376
cert_cover_5 6 3 2 3 4 5 88 376 2
cert_coverFacet 7 432
cert_cover_2 7 4 3 6 7 176 432 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0311

end
end BundlePart25

section BundlePart26
/- Source: ProjectionCertificates/R_m14e10q1_0327.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0327

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [647, 331, 587, 419, 597, 357, 165, 666, 394, 124, 692, 184, 600, 488, 75, 131, 259, 515, 37, 69, 133, 517, 161, 289, 321, 577, 138, 266, 522, 386, 642, 52, 84, 532, 100, 164, 644, 56, 88, 152, 536, 104, 168, 328, 584, 392, 176, 592, 656, 352, 416]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_647, vertices_331, vertices_587, vertices_419, vertices_597, vertices_357, vertices_165, vertices_666, vertices_394, vertices_124, vertices_692, vertices_184, vertices_600, vertices_488] (by decide +kernel)
  polygons := literalFinset [vertices_75, vertices_131, vertices_259, vertices_515, vertices_37, vertices_69, vertices_133, vertices_517, vertices_161, vertices_289, vertices_321, vertices_577, vertices_138, vertices_266, vertices_522, vertices_386, vertices_642, vertices_52, vertices_84, vertices_532, vertices_100, vertices_164, vertices_644, vertices_56, vertices_88, vertices_152, vertices_536, vertices_104, vertices_168, vertices_328, vertices_584, vertices_392, vertices_176, vertices_592, vertices_656, vertices_352, vertices_416] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_647), (false, vertices_331), (false, vertices_587), (false, vertices_419), (false, vertices_597), (false, vertices_357), (false, vertices_165), (true, vertices_138), (true, vertices_52), (true, vertices_56), (true, vertices_88), (true, vertices_152), (true, vertices_536), (true, vertices_104), (true, vertices_168), (true, vertices_392), (true, vertices_176), (true, vertices_656)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 16 12 20 21 22 23 24 25 26
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_647) then 13 else
  if p.val = (false, vertices_331) then 17 else
  if p.val = (false, vertices_587) then 18 else
  if p.val = (false, vertices_419) then 19 else
  if p.val = (false, vertices_597) then 14 else
  if p.val = (false, vertices_357) then 15 else
  if p.val = (false, vertices_165) then 0 else
  if p.val = (true, vertices_138) then 1 else
  if p.val = (true, vertices_52) then 2 else
  if p.val = (true, vertices_56) then 3 else
  if p.val = (true, vertices_88) then 4 else
  if p.val = (true, vertices_152) then 5 else
  if p.val = (true, vertices_536) then 6 else
  if p.val = (true, vertices_104) then 7 else
  if p.val = (true, vertices_168) then 8 else
  if p.val = (true, vertices_392) then 9 else
  if p.val = (true, vertices_176) then 10 else
  if p.val = (true, vertices_656) then 11 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_165), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_138), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_52), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_56), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_88), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_152), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_536), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_104), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_168), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_392), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_176), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_656), by decide +kernel⟩
  | 12 => Sum.inl 1
  | 13 => Sum.inr ⟨(false, vertices_647), by decide +kernel⟩
  | 14 => Sum.inr ⟨(false, vertices_597), by decide +kernel⟩
  | 15 => Sum.inr ⟨(false, vertices_357), by decide +kernel⟩
  | 16 => Sum.inl 0
  | 17 => Sum.inr ⟨(false, vertices_331), by decide +kernel⟩
  | 18 => Sum.inr ⟨(false, vertices_587), by decide +kernel⟩
  | 19 => Sum.inr ⟨(false, vertices_419), by decide +kernel⟩
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
cert_row_4 0 0 2 3 6 8 666 138 2
cert_row_4 1 1 3 4 6 8 692 52 3
cert_row_4 2 1 2 3 4 5 124 52 1
cert_row_4 3 2 4 5 6 7 488 104 3
cert_rows
cert_pivot_2 0 8 1 2
cert_heightProof 4
cert_coverFacet 0 666
cert_cover_5 0 0 0 2 3 6 138 666 2
cert_coverFacet 1 394
cert_cover_2 1 2 0 6 7 138 394 3
cert_coverFacet 2 124
cert_cover_5 2 2 1 2 3 4 52 124 1
cert_coverFacet 3 692
cert_cover_5 3 1 1 3 4 6 52 692 3
cert_coverFacet 4 184
cert_cover_2 4 3 2 4 6 56 184 3
cert_coverFacet 5 600
cert_cover_2 5 3 2 5 8 88 600 3
cert_coverFacet 6 488
cert_cover_5 6 3 2 4 5 6 104 488 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0327

end
end BundlePart26

section BundlePart27
/- Source: ProjectionCertificates/R_m14e10q1_0336.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0336

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [279, 71, 779, 611, 53, 229, 817, 206, 398, 586, 180, 916, 968, 752, 7, 67, 259, 515, 21, 37, 69, 49, 273, 97, 545, 769, 142, 70, 262, 74, 266, 522, 578, 52, 148, 276, 164, 196, 388, 200, 584, 392, 776, 176, 560, 656, 784, 224, 608, 704, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_279, vertices_71, vertices_779, vertices_611, vertices_53, vertices_229, vertices_817, vertices_206, vertices_398, vertices_586, vertices_180, vertices_916, vertices_968, vertices_752] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_67, vertices_259, vertices_515, vertices_21, vertices_37, vertices_69, vertices_49, vertices_273, vertices_97, vertices_545, vertices_769, vertices_142, vertices_70, vertices_262, vertices_74, vertices_266, vertices_522, vertices_578, vertices_52, vertices_148, vertices_276, vertices_164, vertices_196, vertices_388, vertices_200, vertices_584, vertices_392, vertices_776, vertices_176, vertices_560, vertices_656, vertices_784, vertices_224, vertices_608, vertices_704, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_279), (false, vertices_71), (false, vertices_779), (false, vertices_611), (false, vertices_53), (false, vertices_229), (false, vertices_817), (true, vertices_142), (true, vertices_74), (true, vertices_148), (true, vertices_388), (true, vertices_200), (true, vertices_584), (true, vertices_392), (true, vertices_176), (true, vertices_656), (true, vertices_704), (true, vertices_896)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 16 12 19 20 22 23 24 25 26
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_279) then 13 else
  if p.val = (false, vertices_71) then 0 else
  if p.val = (false, vertices_779) then 17 else
  if p.val = (false, vertices_611) then 18 else
  if p.val = (false, vertices_53) then 1 else
  if p.val = (false, vertices_229) then 14 else
  if p.val = (false, vertices_817) then 21 else
  if p.val = (true, vertices_142) then 15 else
  if p.val = (true, vertices_74) then 2 else
  if p.val = (true, vertices_148) then 3 else
  if p.val = (true, vertices_388) then 4 else
  if p.val = (true, vertices_200) then 5 else
  if p.val = (true, vertices_584) then 6 else
  if p.val = (true, vertices_392) then 7 else
  if p.val = (true, vertices_176) then 8 else
  if p.val = (true, vertices_656) then 9 else
  if p.val = (true, vertices_704) then 10 else
  if p.val = (true, vertices_896) then 11 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_71), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_53), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_74), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_148), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_388), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_200), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_584), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_392), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_176), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_656), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_704), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_896), by decide +kernel⟩
  | 12 => Sum.inl 1
  | 13 => Sum.inr ⟨(false, vertices_279), by decide +kernel⟩
  | 14 => Sum.inr ⟨(false, vertices_229), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_142), by decide +kernel⟩
  | 16 => Sum.inl 0
  | 17 => Sum.inr ⟨(false, vertices_779), by decide +kernel⟩
  | 18 => Sum.inr ⟨(false, vertices_611), by decide +kernel⟩
  | 19 => Sum.inl 2
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
cert_row_2 0 0 1 2 6 142
cert_row_4 1 1 3 6 7 8 916 148 3
cert_row_4 2 2 5 6 7 8 968 200 3
cert_row_4 3 3 4 5 6 8 752 176 2
cert_rows
cert_pivot_2 0 1 2 3
cert_heightProof 4
cert_coverFacet 0 206
cert_cover_5 0 0 0 1 2 5 142 206 3
cert_coverFacet 1 398
cert_cover_5 1 0 0 1 2 7 142 398 3
cert_coverFacet 2 586
cert_cover_2 2 2 0 5 8 74 586 3
cert_coverFacet 3 180
cert_cover_2 3 3 1 4 6 52 180 3
cert_coverFacet 4 916
cert_cover_5 4 1 1 3 6 7 148 916 3
cert_coverFacet 5 968
cert_cover_5 5 2 2 5 6 7 200 968 3
cert_coverFacet 6 752
cert_cover_5 6 3 3 4 5 6 176 752 2
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0336

end
end BundlePart27

section BundlePart28
/- Source: ProjectionCertificates/R_m14e10q1_0337.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0337

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [199, 397, 837, 793, 713, 310, 150, 358, 666, 562, 738, 404, 408, 880, 69, 133, 261, 137, 265, 521, 193, 577, 769, 22, 294, 70, 134, 50, 146, 530, 98, 546, 194, 642, 148, 276, 324, 388, 152, 280, 536, 392, 648, 304, 560, 400, 784, 352, 608, 704, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_199, vertices_397, vertices_837, vertices_793, vertices_713, vertices_310, vertices_150, vertices_358, vertices_666, vertices_562, vertices_738, vertices_404, vertices_408, vertices_880] (by decide +kernel)
  polygons := literalFinset [vertices_69, vertices_133, vertices_261, vertices_137, vertices_265, vertices_521, vertices_193, vertices_577, vertices_769, vertices_22, vertices_294, vertices_70, vertices_134, vertices_50, vertices_146, vertices_530, vertices_98, vertices_546, vertices_194, vertices_642, vertices_148, vertices_276, vertices_324, vertices_388, vertices_152, vertices_280, vertices_536, vertices_392, vertices_648, vertices_304, vertices_560, vertices_400, vertices_784, vertices_352, vertices_608, vertices_704, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_199), (false, vertices_397), (false, vertices_837), (false, vertices_793), (false, vertices_713), (true, vertices_22), (true, vertices_294), (true, vertices_50), (true, vertices_146), (true, vertices_530), (true, vertices_98), (true, vertices_546), (true, vertices_642), (true, vertices_148), (true, vertices_276), (true, vertices_152), (true, vertices_304), (true, vertices_560), (true, vertices_400), (true, vertices_352), (true, vertices_608)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 18 21 24 25 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_199) then 16 else
  if p.val = (false, vertices_397) then 19 else
  if p.val = (false, vertices_837) then 20 else
  if p.val = (false, vertices_793) then 22 else
  if p.val = (false, vertices_713) then 23 else
  if p.val = (true, vertices_22) then 0 else
  if p.val = (true, vertices_294) then 17 else
  if p.val = (true, vertices_50) then 1 else
  if p.val = (true, vertices_146) then 2 else
  if p.val = (true, vertices_530) then 3 else
  if p.val = (true, vertices_98) then 4 else
  if p.val = (true, vertices_546) then 5 else
  if p.val = (true, vertices_642) then 6 else
  if p.val = (true, vertices_148) then 7 else
  if p.val = (true, vertices_276) then 8 else
  if p.val = (true, vertices_152) then 9 else
  if p.val = (true, vertices_304) then 10 else
  if p.val = (true, vertices_560) then 11 else
  if p.val = (true, vertices_400) then 12 else
  if p.val = (true, vertices_352) then 13 else
  if p.val = (true, vertices_608) then 14 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_22), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_50), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_146), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_530), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_98), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_546), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_642), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_148), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_276), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_152), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_304), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_560), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_400), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_352), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_608), by decide +kernel⟩
  | 15 => Sum.inl 0
  | 16 => Sum.inr ⟨(false, vertices_199), by decide +kernel⟩
  | 17 => Sum.inr ⟨(true, vertices_294), by decide +kernel⟩
  | 18 => Sum.inl 1
  | 19 => Sum.inr ⟨(false, vertices_397), by decide +kernel⟩
  | 20 => Sum.inr ⟨(false, vertices_837), by decide +kernel⟩
  | 21 => Sum.inl 2
  | 22 => Sum.inr ⟨(false, vertices_793), by decide +kernel⟩
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
cert_row_2 0 0 1 4 7 294
cert_row_4 1 0 2 3 6 8 666 146 1
cert_row_4 2 0 4 5 6 8 738 98 3
cert_row_4 3 3 4 5 7 8 880 304 2
cert_rows
cert_pivot_2 1 2 0 3
cert_heightProof 4
cert_coverFacet 0 310
cert_cover_5 0 0 0 1 3 4 22 310 3
cert_coverFacet 1 150
cert_cover_2 1 1 0 3 6 22 150 3
cert_coverFacet 2 358
cert_cover_5 2 0 0 1 4 5 294 358 3
cert_coverFacet 3 666
cert_cover_5 3 1 0 2 3 6 146 666 1
cert_coverFacet 4 562
cert_cover_2 4 3 0 4 8 50 562 3
cert_coverFacet 5 738
cert_cover_5 5 2 0 4 5 6 98 738 3
cert_coverFacet 6 404
cert_cover_2 6 3 1 6 7 148 404 3
cert_coverFacet 7 408
cert_cover_2 7 3 2 6 7 152 408 3
cert_coverFacet 8 880
cert_cover_5 8 3 3 4 5 7 304 880 2
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0337

end
end BundlePart28

section BundlePart29
/- Source: ProjectionCertificates/R_m14e10q1_0342.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0342

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [899, 837, 617, 169, 457, 689, 790, 186, 282, 394, 658, 316, 364, 628, 41, 73, 137, 161, 545, 321, 577, 385, 641, 769, 26, 138, 266, 146, 274, 530, 386, 642, 770, 300, 52, 276, 532, 100, 324, 580, 772, 56, 280, 104, 168, 328, 392, 176, 560, 656, 608]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_899, vertices_837, vertices_617, vertices_169, vertices_457, vertices_689, vertices_790, vertices_186, vertices_282, vertices_394, vertices_658, vertices_316, vertices_364, vertices_628] (by decide +kernel)
  polygons := literalFinset [vertices_41, vertices_73, vertices_137, vertices_161, vertices_545, vertices_321, vertices_577, vertices_385, vertices_641, vertices_769, vertices_26, vertices_138, vertices_266, vertices_146, vertices_274, vertices_530, vertices_386, vertices_642, vertices_770, vertices_300, vertices_52, vertices_276, vertices_532, vertices_100, vertices_324, vertices_580, vertices_772, vertices_56, vertices_280, vertices_104, vertices_168, vertices_328, vertices_392, vertices_176, vertices_560, vertices_656, vertices_608] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_899), (false, vertices_837), (false, vertices_617), (false, vertices_169), (false, vertices_457), (false, vertices_689), (true, vertices_26), (true, vertices_138), (true, vertices_266), (true, vertices_146), (true, vertices_274), (true, vertices_530), (true, vertices_300), (true, vertices_52), (true, vertices_276), (true, vertices_532), (true, vertices_100), (true, vertices_56), (true, vertices_280)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 13 15 18 21 23 24 25 26 27
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_899) then 14 else
  if p.val = (false, vertices_837) then 16 else
  if p.val = (false, vertices_617) then 19 else
  if p.val = (false, vertices_169) then 0 else
  if p.val = (false, vertices_457) then 20 else
  if p.val = (false, vertices_689) then 22 else
  if p.val = (true, vertices_26) then 1 else
  if p.val = (true, vertices_138) then 2 else
  if p.val = (true, vertices_266) then 3 else
  if p.val = (true, vertices_146) then 4 else
  if p.val = (true, vertices_274) then 5 else
  if p.val = (true, vertices_530) then 6 else
  if p.val = (true, vertices_300) then 17 else
  if p.val = (true, vertices_52) then 7 else
  if p.val = (true, vertices_276) then 8 else
  if p.val = (true, vertices_532) then 9 else
  if p.val = (true, vertices_100) then 10 else
  if p.val = (true, vertices_56) then 11 else
  if p.val = (true, vertices_280) then 12 else
  0
cert_priority
cert_nodeAtPriority_2 0 169 1 26 2 138 3 266 146 274 530 52 276 532 100 56 280 899 837 300 617 457 689
cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 2 3 4 6 186 26 3
cert_row_2 1 1 2 4 7 300
cert_row_4 2 0 1 3 7 8 790 274 1
cert_row_4 3 1 3 4 5 8 628 52 3
cert_rows
cert_pivot_2 6 2 0 1
cert_heightProof 4
cert_coverFacet 0 790
cert_cover_5 0 2 0 1 3 7 274 790 1
cert_coverFacet 1 186
cert_cover_5 1 0 0 2 3 4 26 186 3
cert_coverFacet 2 282
cert_cover_2 2 2 0 3 7 26 282 3
cert_coverFacet 3 394
cert_cover_2 3 2 0 6 7 138 394 3
cert_coverFacet 4 658
cert_cover_2 4 3 0 6 8 146 658 3
cert_coverFacet 5 316
cert_cover_5 5 1 1 2 3 4 300 316 2
cert_coverFacet 6 364
cert_cover_5 6 1 1 2 4 5 300 364 3
cert_coverFacet 7 628
cert_cover_5 7 3 1 3 4 5 52 628 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0342

end
end BundlePart29
-- Explicit facial frame witnesses.

-- Public target certificates; internal witness data stays private.
namespace Nonrational.TerminalVerification
open Papers.RationalityTen.ChirotopeDensity.FiniteProjection
open Nonrational.TerminalData
set_option maxRecDepth 100000
set_option maxHeartbeats 0

public theorem projection_0270 : Certifies 270 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0120.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0271 : Certifies 271 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0122.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0272 : Certifies 272 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0129.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0273 : Certifies 273 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0131.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0274 : Certifies 274 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0133.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0275 : Certifies 275 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0163.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0276 : Certifies 276 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0167.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0277 : Certifies 277 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0184.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0278 : Certifies 278 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0193.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0279 : Certifies 279 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0194.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0280 : Certifies 280 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0197.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0281 : Certifies 281 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0215.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0282 : Certifies 282 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0223.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0283 : Certifies 283 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0252.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0284 : Certifies 284 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0253.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0285 : Certifies 285 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0254.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0286 : Certifies 286 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0258.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0287 : Certifies 287 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0259.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0288 : Certifies 288 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0260.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0289 : Certifies 289 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0263.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0290 : Certifies 290 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0268.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0291 : Certifies 291 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0282.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0292 : Certifies 292 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0283.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0293 : Certifies 293 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0284.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0294 : Certifies 294 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0296.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0295 : Certifies 295 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0311.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0296 : Certifies 296 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0327.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0297 : Certifies 297 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0336.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0298 : Certifies 298 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0337.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0299 : Certifies 299 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0342.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem certified_B009 (j : Fin 30) :
    Certifies (270 + j.val) := by
  fin_cases j
  · exact projection_0270
  · exact projection_0271
  · exact projection_0272
  · exact projection_0273
  · exact projection_0274
  · exact projection_0275
  · exact projection_0276
  · exact projection_0277
  · exact projection_0278
  · exact projection_0279
  · exact projection_0280
  · exact projection_0281
  · exact projection_0282
  · exact projection_0283
  · exact projection_0284
  · exact projection_0285
  · exact projection_0286
  · exact projection_0287
  · exact projection_0288
  · exact projection_0289
  · exact projection_0290
  · exact projection_0291
  · exact projection_0292
  · exact projection_0293
  · exact projection_0294
  · exact projection_0295
  · exact projection_0296
  · exact projection_0297
  · exact projection_0298
  · exact projection_0299

end Nonrational.TerminalVerification
