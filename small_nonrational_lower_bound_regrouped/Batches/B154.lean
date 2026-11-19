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
/- Source: ProjectionCertificates/R_m16e10q1_0771.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0771

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [595, 309, 85, 613, 793, 681, 297, 406, 906, 210, 786, 738, 364, 460, 212, 232, 21, 37, 69, 41, 265, 521, 81, 273, 529, 289, 545, 577, 82, 146, 274, 530, 194, 578, 386, 642, 770, 332, 84, 148, 276, 100, 292, 196, 388, 104, 168, 296, 200, 392, 648, 776, 208, 784, 224, 608, 672]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_595, vertices_309, vertices_85, vertices_613, vertices_793, vertices_681, vertices_297, vertices_406, vertices_906, vertices_210, vertices_786, vertices_738, vertices_364, vertices_460, vertices_212, vertices_232] (by decide +kernel)
  polygons := literalFinset [vertices_21, vertices_37, vertices_69, vertices_41, vertices_265, vertices_521, vertices_81, vertices_273, vertices_529, vertices_289, vertices_545, vertices_577, vertices_82, vertices_146, vertices_274, vertices_530, vertices_194, vertices_578, vertices_386, vertices_642, vertices_770, vertices_332, vertices_84, vertices_148, vertices_276, vertices_100, vertices_292, vertices_196, vertices_388, vertices_104, vertices_168, vertices_296, vertices_200, vertices_392, vertices_648, vertices_776, vertices_208, vertices_784, vertices_224, vertices_608, vertices_672] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_595), (false, vertices_309), (false, vertices_85), (false, vertices_613), (false, vertices_793), (false, vertices_681), (false, vertices_297), (true, vertices_146), (true, vertices_274), (true, vertices_194), (true, vertices_386), (true, vertices_642), (true, vertices_770), (true, vertices_332), (true, vertices_148), (true, vertices_196), (true, vertices_388), (true, vertices_104), (true, vertices_200), (true, vertices_392), (true, vertices_208), (true, vertices_224)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 16 18 22 25 26 27 28 29 30
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_595) then 17 else
  if p.val = (false, vertices_309) then 19 else
  if p.val = (false, vertices_85) then 0 else
  if p.val = (false, vertices_613) then 20 else
  if p.val = (false, vertices_793) then 23 else
  if p.val = (false, vertices_681) then 24 else
  if p.val = (false, vertices_297) then 1 else
  if p.val = (true, vertices_146) then 2 else
  if p.val = (true, vertices_274) then 3 else
  if p.val = (true, vertices_194) then 4 else
  if p.val = (true, vertices_386) then 5 else
  if p.val = (true, vertices_642) then 6 else
  if p.val = (true, vertices_770) then 7 else
  if p.val = (true, vertices_332) then 21 else
  if p.val = (true, vertices_148) then 8 else
  if p.val = (true, vertices_196) then 9 else
  if p.val = (true, vertices_388) then 10 else
  if p.val = (true, vertices_104) then 11 else
  if p.val = (true, vertices_200) then 12 else
  if p.val = (true, vertices_392) then 13 else
  if p.val = (true, vertices_208) then 14 else
  if p.val = (true, vertices_224) then 15 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_85), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_297), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_146), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_274), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_194), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_386), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_642), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_770), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_148), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_196), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_388), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_104), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_200), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_392), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_208), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_224), by decide +kernel⟩
  | 16 => Sum.inl 0
  | 17 => Sum.inr ⟨(false, vertices_595), by decide +kernel⟩
  | 18 => Sum.inl 1
  | 19 => Sum.inr ⟨(false, vertices_309), by decide +kernel⟩
  | 20 => Sum.inr ⟨(false, vertices_613), by decide +kernel⟩
  | 21 => Sum.inr ⟨(true, vertices_332), by decide +kernel⟩
  | 22 => Sum.inl 2
  | 23 => Sum.inr ⟨(false, vertices_793), by decide +kernel⟩
  | 24 => Sum.inr ⟨(false, vertices_681), by decide +kernel⟩
  | 25 => Sum.inl 3
  | 26 => Sum.inl 4
  | 27 => Sum.inl 5
  | 28 => Sum.inl 6
  | 29 => Sum.inl 7
  | 30 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 3 6 7 406 146 1
cert_row_2 1 1 2 5 7 332
cert_row_4 2 0 2 6 7 8 906 386 1
cert_row_4 3 0 4 5 6 8 738 194 1
cert_rows
cert_pivot_2 3 1 2 0
cert_heightProof 4
cert_coverFacet 0 406
cert_cover_5 0 0 0 1 3 6 146 406 1
cert_coverFacet 1 906
cert_cover_5 1 2 0 2 6 7 386 906 1
cert_coverFacet 2 210
cert_cover_2 2 3 0 5 6 82 210 3
cert_coverFacet 3 786
cert_cover_2 3 3 0 7 8 274 786 3
cert_coverFacet 4 738
cert_cover_5 4 3 0 4 5 6 194 738 1
cert_coverFacet 5 364
cert_cover_5 5 1 1 2 4 5 332 364 2
cert_coverFacet 6 460
cert_cover_5 6 1 1 2 5 6 332 460 3
cert_coverFacet 7 212
cert_cover_2 7 3 1 5 6 84 212 3
cert_coverFacet 8 232
cert_cover_2 8 4 2 5 6 104 232 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0771

end
end BundlePart0

section BundlePart1
/- Source: ProjectionCertificates/R_m16e10q1_0772.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0772

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [779, 563, 211, 387, 613, 113, 961, 398, 154, 538, 188, 572, 844, 356, 420, 496, 19, 131, 259, 515, 49, 81, 97, 545, 193, 577, 385, 769, 26, 138, 266, 522, 146, 530, 386, 60, 140, 268, 524, 100, 164, 292, 548, 324, 580, 388, 152, 536, 776, 112, 176, 560, 208, 352, 416, 448, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_779, vertices_563, vertices_211, vertices_387, vertices_613, vertices_113, vertices_961, vertices_398, vertices_154, vertices_538, vertices_188, vertices_572, vertices_844, vertices_356, vertices_420, vertices_496] (by decide +kernel)
  polygons := literalFinset [vertices_19, vertices_131, vertices_259, vertices_515, vertices_49, vertices_81, vertices_97, vertices_545, vertices_193, vertices_577, vertices_385, vertices_769, vertices_26, vertices_138, vertices_266, vertices_522, vertices_146, vertices_530, vertices_386, vertices_60, vertices_140, vertices_268, vertices_524, vertices_100, vertices_164, vertices_292, vertices_548, vertices_324, vertices_580, vertices_388, vertices_152, vertices_536, vertices_776, vertices_112, vertices_176, vertices_560, vertices_208, vertices_352, vertices_416, vertices_448, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_779), (false, vertices_563), (false, vertices_211), (false, vertices_387), (false, vertices_613), (false, vertices_113), (false, vertices_961), (true, vertices_26), (true, vertices_138), (true, vertices_60), (true, vertices_140), (true, vertices_268), (true, vertices_524), (true, vertices_164), (true, vertices_292), (true, vertices_324), (true, vertices_388), (true, vertices_152), (true, vertices_536), (true, vertices_176), (true, vertices_352), (true, vertices_416)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 16 20 23 24 25 26 28 29 30
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_779) then 17 else
  if p.val = (false, vertices_563) then 18 else
  if p.val = (false, vertices_211) then 19 else
  if p.val = (false, vertices_387) then 0 else
  if p.val = (false, vertices_613) then 21 else
  if p.val = (false, vertices_113) then 1 else
  if p.val = (false, vertices_961) then 27 else
  if p.val = (true, vertices_26) then 2 else
  if p.val = (true, vertices_138) then 3 else
  if p.val = (true, vertices_60) then 22 else
  if p.val = (true, vertices_140) then 4 else
  if p.val = (true, vertices_268) then 5 else
  if p.val = (true, vertices_524) then 6 else
  if p.val = (true, vertices_164) then 7 else
  if p.val = (true, vertices_292) then 8 else
  if p.val = (true, vertices_324) then 9 else
  if p.val = (true, vertices_388) then 10 else
  if p.val = (true, vertices_152) then 11 else
  if p.val = (true, vertices_536) then 12 else
  if p.val = (true, vertices_176) then 13 else
  if p.val = (true, vertices_352) then 14 else
  if p.val = (true, vertices_416) then 15 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_387), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_113), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_26), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_138), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_140), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_268), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_524), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_164), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_292), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_324), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_388), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_152), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_536), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_176), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_352), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_416), by decide +kernel⟩
  | 16 => Sum.inl 0
  | 17 => Sum.inr ⟨(false, vertices_779), by decide +kernel⟩
  | 18 => Sum.inr ⟨(false, vertices_563), by decide +kernel⟩
  | 19 => Sum.inr ⟨(false, vertices_211), by decide +kernel⟩
  | 20 => Sum.inl 1
  | 21 => Sum.inr ⟨(false, vertices_613), by decide +kernel⟩
  | 22 => Sum.inr ⟨(true, vertices_60), by decide +kernel⟩
  | 23 => Sum.inl 2
  | 24 => Sum.inl 3
  | 25 => Sum.inl 4
  | 26 => Sum.inl 5
  | 27 => Sum.inr ⟨(false, vertices_961), by decide +kernel⟩
  | 28 => Sum.inl 6
  | 29 => Sum.inl 7
  | 30 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 2 6 7 398 138 1
cert_row_4 1 1 2 5 7 8 844 268 2
cert_row_2 2 1 2 3 4 60
cert_row_4 3 3 4 5 6 7 496 112 3
cert_rows
cert_pivot_2 0 8 1 3
cert_heightProof 4
cert_coverFacet 0 398
cert_cover_5 0 0 0 1 2 6 138 398 1
cert_coverFacet 1 154
cert_cover_2 1 2 0 3 6 26 154 3
cert_coverFacet 2 538
cert_cover_2 2 2 0 3 8 26 538 3
cert_coverFacet 3 188
cert_cover_5 3 2 1 2 3 6 60 188 3
cert_coverFacet 4 572
cert_cover_5 4 2 1 2 3 8 60 572 3
cert_coverFacet 5 844
cert_cover_5 5 1 1 2 5 7 268 844 2
cert_coverFacet 6 356
cert_cover_2 6 4 1 5 7 100 356 3
cert_coverFacet 7 420
cert_cover_2 7 4 1 6 7 164 420 3
cert_coverFacet 8 496
cert_cover_5 8 3 3 4 5 6 112 496 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0772

end
end BundlePart1

section BundlePart2
/- Source: ProjectionCertificates/R_m16e10q1_0773.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0773

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [51, 339, 227, 397, 525, 837, 713, 433, 598, 682, 562, 706, 316, 572, 340, 424, 19, 35, 67, 13, 261, 517, 137, 521, 49, 273, 161, 193, 321, 577, 385, 50, 82, 530, 162, 546, 194, 578, 642, 60, 268, 524, 84, 276, 532, 324, 580, 168, 296, 552, 392, 648, 304, 560, 336, 416, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_51, vertices_339, vertices_227, vertices_397, vertices_525, vertices_837, vertices_713, vertices_433, vertices_598, vertices_682, vertices_562, vertices_706, vertices_316, vertices_572, vertices_340, vertices_424] (by decide +kernel)
  polygons := literalFinset [vertices_19, vertices_35, vertices_67, vertices_13, vertices_261, vertices_517, vertices_137, vertices_521, vertices_49, vertices_273, vertices_161, vertices_193, vertices_321, vertices_577, vertices_385, vertices_50, vertices_82, vertices_530, vertices_162, vertices_546, vertices_194, vertices_578, vertices_642, vertices_60, vertices_268, vertices_524, vertices_84, vertices_276, vertices_532, vertices_324, vertices_580, vertices_168, vertices_296, vertices_552, vertices_392, vertices_648, vertices_304, vertices_560, vertices_336, vertices_416, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_51), (false, vertices_339), (false, vertices_227), (false, vertices_397), (false, vertices_525), (false, vertices_837), (false, vertices_713), (false, vertices_433), (true, vertices_530), (true, vertices_546), (true, vertices_578), (true, vertices_642), (true, vertices_60), (true, vertices_84), (true, vertices_276), (true, vertices_532), (true, vertices_168), (true, vertices_296), (true, vertices_552), (true, vertices_560)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 13 16 20 22 24 25 26 27 28
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_51) then 0 else
  if p.val = (false, vertices_339) then 14 else
  if p.val = (false, vertices_227) then 15 else
  if p.val = (false, vertices_397) then 17 else
  if p.val = (false, vertices_525) then 1 else
  if p.val = (false, vertices_837) then 18 else
  if p.val = (false, vertices_713) then 21 else
  if p.val = (false, vertices_433) then 23 else
  if p.val = (true, vertices_530) then 2 else
  if p.val = (true, vertices_546) then 3 else
  if p.val = (true, vertices_578) then 4 else
  if p.val = (true, vertices_642) then 5 else
  if p.val = (true, vertices_60) then 19 else
  if p.val = (true, vertices_84) then 6 else
  if p.val = (true, vertices_276) then 7 else
  if p.val = (true, vertices_532) then 8 else
  if p.val = (true, vertices_168) then 9 else
  if p.val = (true, vertices_296) then 10 else
  if p.val = (true, vertices_552) then 11 else
  if p.val = (true, vertices_560) then 12 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_51), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_525), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_530), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_546), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_578), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_642), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_84), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_276), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_532), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_168), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_296), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_552), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_560), by decide +kernel⟩
  | 13 => Sum.inl 0
  | 14 => Sum.inr ⟨(false, vertices_339), by decide +kernel⟩
  | 15 => Sum.inr ⟨(false, vertices_227), by decide +kernel⟩
  | 16 => Sum.inl 1
  | 17 => Sum.inr ⟨(false, vertices_397), by decide +kernel⟩
  | 18 => Sum.inr ⟨(false, vertices_837), by decide +kernel⟩
  | 19 => Sum.inr ⟨(true, vertices_60), by decide +kernel⟩
  | 20 => Sum.inl 2
  | 21 => Sum.inr ⟨(false, vertices_713), by decide +kernel⟩
  | 22 => Sum.inl 3
  | 23 => Sum.inr ⟨(false, vertices_433), by decide +kernel⟩
  | 24 => Sum.inl 4
  | 25 => Sum.inl 5
  | 26 => Sum.inl 6
  | 27 => Sum.inl 7
  | 28 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 3 5 8 598 82 1
cert_row_2 1 1 2 3 4 60
cert_row_4 2 0 2 4 6 8 682 162 1
cert_rows_3
cert_pivot_3 1 5 0
cert_heightProof 3
cert_coverFacet 0 598
cert_cover_5 0 0 0 1 3 5 82 598 1
cert_coverFacet 1 682
cert_cover_5 1 2 0 2 4 6 162 682 1
cert_coverFacet 2 562
cert_cover_2 2 3 0 4 8 50 562 3
cert_coverFacet 3 706
cert_cover_2 3 5 0 6 8 194 706 3
cert_coverFacet 4 316
cert_cover_5 4 1 1 2 3 7 60 316 3
cert_coverFacet 5 572
cert_cover_5 5 1 1 2 3 8 60 572 3
cert_coverFacet 6 340
cert_cover_2 6 3 1 5 7 84 340 3
cert_coverFacet 7 424
cert_cover_2 7 4 2 6 7 168 424 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 3 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0773

end
end BundlePart2

section BundlePart3
/- Source: ProjectionCertificates/R_m16e10q1_0774.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0774

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [675, 333, 313, 89, 177, 721, 865, 654, 358, 614, 390, 434, 604, 396, 408, 664, 25, 73, 265, 49, 81, 145, 161, 289, 545, 321, 577, 641, 102, 134, 262, 518, 162, 290, 546, 386, 642, 76, 140, 268, 524, 324, 580, 388, 88, 152, 280, 536, 392, 648, 176, 304, 592, 400, 656, 352, 608]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_675, vertices_333, vertices_313, vertices_89, vertices_177, vertices_721, vertices_865, vertices_654, vertices_358, vertices_614, vertices_390, vertices_434, vertices_604, vertices_396, vertices_408, vertices_664] (by decide +kernel)
  polygons := literalFinset [vertices_25, vertices_73, vertices_265, vertices_49, vertices_81, vertices_145, vertices_161, vertices_289, vertices_545, vertices_321, vertices_577, vertices_641, vertices_102, vertices_134, vertices_262, vertices_518, vertices_162, vertices_290, vertices_546, vertices_386, vertices_642, vertices_76, vertices_140, vertices_268, vertices_524, vertices_324, vertices_580, vertices_388, vertices_88, vertices_152, vertices_280, vertices_536, vertices_392, vertices_648, vertices_176, vertices_304, vertices_592, vertices_400, vertices_656, vertices_352, vertices_608] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_675), (false, vertices_333), (false, vertices_313), (false, vertices_89), (false, vertices_177), (false, vertices_721), (false, vertices_865), (true, vertices_102), (true, vertices_134), (true, vertices_262), (true, vertices_518), (true, vertices_290), (true, vertices_386), (true, vertices_140), (true, vertices_524), (true, vertices_580), (true, vertices_388), (true, vertices_152), (true, vertices_536), (true, vertices_392), (true, vertices_648), (true, vertices_400)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 16 19 21 23 25 27 28 29 30
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_675) then 17 else
  if p.val = (false, vertices_333) then 20 else
  if p.val = (false, vertices_313) then 22 else
  if p.val = (false, vertices_89) then 0 else
  if p.val = (false, vertices_177) then 1 else
  if p.val = (false, vertices_721) then 24 else
  if p.val = (false, vertices_865) then 26 else
  if p.val = (true, vertices_102) then 18 else
  if p.val = (true, vertices_134) then 2 else
  if p.val = (true, vertices_262) then 3 else
  if p.val = (true, vertices_518) then 4 else
  if p.val = (true, vertices_290) then 5 else
  if p.val = (true, vertices_386) then 6 else
  if p.val = (true, vertices_140) then 7 else
  if p.val = (true, vertices_524) then 8 else
  if p.val = (true, vertices_580) then 9 else
  if p.val = (true, vertices_388) then 10 else
  if p.val = (true, vertices_152) then 11 else
  if p.val = (true, vertices_536) then 12 else
  if p.val = (true, vertices_392) then 13 else
  if p.val = (true, vertices_648) then 14 else
  if p.val = (true, vertices_400) then 15 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_89), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_177), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_134), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_262), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_518), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_290), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_386), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_140), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_524), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_580), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_388), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_152), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_536), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_392), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_648), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_400), by decide +kernel⟩
  | 16 => Sum.inl 0
  | 17 => Sum.inr ⟨(false, vertices_675), by decide +kernel⟩
  | 18 => Sum.inr ⟨(true, vertices_102), by decide +kernel⟩
  | 19 => Sum.inl 1
  | 20 => Sum.inr ⟨(false, vertices_333), by decide +kernel⟩
  | 21 => Sum.inl 2
  | 22 => Sum.inr ⟨(false, vertices_313), by decide +kernel⟩
  | 23 => Sum.inl 3
  | 24 => Sum.inr ⟨(false, vertices_721), by decide +kernel⟩
  | 25 => Sum.inl 4
  | 26 => Sum.inr ⟨(false, vertices_865), by decide +kernel⟩
  | 27 => Sum.inl 5
  | 28 => Sum.inl 6
  | 29 => Sum.inl 7
  | 30 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 3 4 6 7 434 162 1
cert_row_2 1 0 1 4 5 102
cert_row_4 2 0 1 2 6 8 654 134 2
cert_row_4 3 1 2 3 5 8 604 76 2
cert_rows
cert_pivot_2 7 4 0 1
cert_heightProof 4
cert_coverFacet 0 654
cert_cover_5 0 2 0 1 2 6 134 654 2
cert_coverFacet 1 358
cert_cover_5 1 1 0 1 4 7 102 358 3
cert_coverFacet 2 614
cert_cover_5 2 1 0 1 4 8 102 614 3
cert_coverFacet 3 390
cert_cover_2 3 1 0 6 7 134 390 3
cert_coverFacet 4 434
cert_cover_5 4 0 0 3 4 6 162 434 1
cert_coverFacet 5 604
cert_cover_5 5 3 1 2 3 5 76 604 2
cert_coverFacet 6 396
cert_cover_2 6 2 1 6 7 140 396 3
cert_coverFacet 7 408
cert_cover_2 7 3 2 6 7 152 408 3
cert_coverFacet 8 664
cert_cover_2 8 3 2 6 8 152 664 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0774

end
end BundlePart3

section BundlePart4
/- Source: ProjectionCertificates/R_m16e10q1_0775.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0775

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [279, 659, 611, 323, 653, 149, 837, 362, 306, 562, 188, 316, 780, 232, 968, 752, 19, 67, 259, 515, 21, 133, 261, 517, 145, 321, 577, 641, 50, 274, 530, 98, 290, 546, 322, 60, 140, 268, 524, 148, 276, 772, 104, 168, 296, 200, 328, 648, 776, 176, 304, 560, 656, 224, 608, 704, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_279, vertices_659, vertices_611, vertices_323, vertices_653, vertices_149, vertices_837, vertices_362, vertices_306, vertices_562, vertices_188, vertices_316, vertices_780, vertices_232, vertices_968, vertices_752] (by decide +kernel)
  polygons := literalFinset [vertices_19, vertices_67, vertices_259, vertices_515, vertices_21, vertices_133, vertices_261, vertices_517, vertices_145, vertices_321, vertices_577, vertices_641, vertices_50, vertices_274, vertices_530, vertices_98, vertices_290, vertices_546, vertices_322, vertices_60, vertices_140, vertices_268, vertices_524, vertices_148, vertices_276, vertices_772, vertices_104, vertices_168, vertices_296, vertices_200, vertices_328, vertices_648, vertices_776, vertices_176, vertices_304, vertices_560, vertices_656, vertices_224, vertices_608, vertices_704, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_279), (false, vertices_659), (false, vertices_611), (false, vertices_323), (false, vertices_653), (false, vertices_149), (false, vertices_837), (true, vertices_50), (true, vertices_290), (true, vertices_60), (true, vertices_268), (true, vertices_104), (true, vertices_168), (true, vertices_296), (true, vertices_200), (true, vertices_328), (true, vertices_776), (true, vertices_176), (true, vertices_304), (true, vertices_560), (true, vertices_224), (true, vertices_704)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 16 20 24 25 26 27 28 29 30
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_279) then 17 else
  if p.val = (false, vertices_659) then 18 else
  if p.val = (false, vertices_611) then 19 else
  if p.val = (false, vertices_323) then 0 else
  if p.val = (false, vertices_653) then 21 else
  if p.val = (false, vertices_149) then 1 else
  if p.val = (false, vertices_837) then 22 else
  if p.val = (true, vertices_50) then 2 else
  if p.val = (true, vertices_290) then 3 else
  if p.val = (true, vertices_60) then 23 else
  if p.val = (true, vertices_268) then 4 else
  if p.val = (true, vertices_104) then 5 else
  if p.val = (true, vertices_168) then 6 else
  if p.val = (true, vertices_296) then 7 else
  if p.val = (true, vertices_200) then 8 else
  if p.val = (true, vertices_328) then 9 else
  if p.val = (true, vertices_776) then 10 else
  if p.val = (true, vertices_176) then 11 else
  if p.val = (true, vertices_304) then 12 else
  if p.val = (true, vertices_560) then 13 else
  if p.val = (true, vertices_224) then 14 else
  if p.val = (true, vertices_704) then 15 else
  0
cert_priority
cert_nodeAtPriority_6 323 149 50 290 268 104 168 296 200 328 776 176 304 560 224 704 279 659 611 653 837 60
cert_priority_injective
cert_incidenceProof
cert_row_2 0 1 2 3 4 60
cert_row_4 1 0 2 4 5 7 362 98 1
cert_row_4 2 2 5 6 7 8 968 200 3
cert_row_4 3 3 4 5 6 8 752 176 2
cert_rows
cert_pivot_2 1 0 2 3
cert_heightProof 4
cert_coverFacet 0 362
cert_cover_5 0 1 0 2 4 5 98 362 1
cert_coverFacet 1 306
cert_cover_2 1 3 0 4 7 50 306 3
cert_coverFacet 2 562
cert_cover_2 2 3 0 4 8 50 562 3
cert_coverFacet 3 188
cert_cover_5 3 0 1 2 3 6 60 188 3
cert_coverFacet 4 316
cert_cover_5 4 0 1 2 3 7 60 316 3
cert_coverFacet 5 780
cert_cover_2 5 2 1 7 8 268 780 3
cert_coverFacet 6 232
cert_cover_2 6 4 2 5 6 104 232 3
cert_coverFacet 7 968
cert_cover_5 7 2 2 5 6 7 200 968 3
cert_coverFacet 8 752
cert_cover_5 8 3 3 4 5 6 176 752 2
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0775

end
end BundlePart4

section BundlePart5
/- Source: ProjectionCertificates/R_m16e10q1_0776.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0776

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [279, 535, 395, 675, 625, 433, 270, 526, 714, 124, 540, 460, 308, 356, 600, 992, 23, 131, 259, 515, 49, 273, 529, 161, 545, 385, 14, 262, 518, 138, 266, 522, 642, 28, 76, 268, 524, 52, 276, 532, 100, 292, 324, 88, 536, 200, 584, 392, 112, 304, 592, 352, 608, 416, 672, 448, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_279, vertices_535, vertices_395, vertices_675, vertices_625, vertices_433, vertices_270, vertices_526, vertices_714, vertices_124, vertices_540, vertices_460, vertices_308, vertices_356, vertices_600, vertices_992] (by decide +kernel)
  polygons := literalFinset [vertices_23, vertices_131, vertices_259, vertices_515, vertices_49, vertices_273, vertices_529, vertices_161, vertices_545, vertices_385, vertices_14, vertices_262, vertices_518, vertices_138, vertices_266, vertices_522, vertices_642, vertices_28, vertices_76, vertices_268, vertices_524, vertices_52, vertices_276, vertices_532, vertices_100, vertices_292, vertices_324, vertices_88, vertices_536, vertices_200, vertices_584, vertices_392, vertices_112, vertices_304, vertices_592, vertices_352, vertices_608, vertices_416, vertices_672, vertices_448, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_279), (false, vertices_535), (false, vertices_395), (false, vertices_675), (false, vertices_625), (false, vertices_433), (true, vertices_14), (true, vertices_522), (true, vertices_28), (true, vertices_76), (true, vertices_268), (true, vertices_524), (true, vertices_52), (true, vertices_100), (true, vertices_292), (true, vertices_324), (true, vertices_88), (true, vertices_536), (true, vertices_200), (true, vertices_584), (true, vertices_352), (true, vertices_448), (true, vertices_704)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 20 17 23 24 27 28 29 30 31
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_279) then 18 else
  if p.val = (false, vertices_535) then 19 else
  if p.val = (false, vertices_395) then 21 else
  if p.val = (false, vertices_675) then 22 else
  if p.val = (false, vertices_625) then 25 else
  if p.val = (false, vertices_433) then 26 else
  if p.val = (true, vertices_14) then 0 else
  if p.val = (true, vertices_522) then 1 else
  if p.val = (true, vertices_28) then 2 else
  if p.val = (true, vertices_76) then 3 else
  if p.val = (true, vertices_268) then 4 else
  if p.val = (true, vertices_524) then 5 else
  if p.val = (true, vertices_52) then 6 else
  if p.val = (true, vertices_100) then 7 else
  if p.val = (true, vertices_292) then 8 else
  if p.val = (true, vertices_324) then 9 else
  if p.val = (true, vertices_88) then 10 else
  if p.val = (true, vertices_536) then 11 else
  if p.val = (true, vertices_200) then 12 else
  if p.val = (true, vertices_584) then 13 else
  if p.val = (true, vertices_352) then 14 else
  if p.val = (true, vertices_448) then 15 else
  if p.val = (true, vertices_704) then 16 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_14), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_522), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_28), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_76), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_268), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_524), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_52), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_100), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_292), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_324), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_88), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_536), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_200), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_584), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_352), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_448), by decide +kernel⟩
  | 16 => Sum.inr ⟨(true, vertices_704), by decide +kernel⟩
  | 17 => Sum.inl 1
  | 18 => Sum.inr ⟨(false, vertices_279), by decide +kernel⟩
  | 19 => Sum.inr ⟨(false, vertices_535), by decide +kernel⟩
  | 20 => Sum.inl 0
  | 21 => Sum.inr ⟨(false, vertices_395), by decide +kernel⟩
  | 22 => Sum.inr ⟨(false, vertices_675), by decide +kernel⟩
  | 23 => Sum.inl 2
  | 24 => Sum.inl 3
  | 25 => Sum.inr ⟨(false, vertices_625), by decide +kernel⟩
  | 26 => Sum.inr ⟨(false, vertices_433), by decide +kernel⟩
  | 27 => Sum.inl 4
  | 28 => Sum.inl 5
  | 29 => Sum.inl 6
  | 30 => Sum.inl 7
  | 31 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 2 5 6 8 714 138 2
cert_row_4 1 1 2 3 4 5 124 28 3
cert_row_4 2 1 2 5 6 7 460 76 3
cert_row_4 3 4 5 6 7 8 992 352 2
cert_rows
cert_pivot_2 0 3 1 4
cert_heightProof 4
cert_coverFacet 0 270
cert_cover_2 0 1 0 2 7 14 270 3
cert_coverFacet 1 526
cert_cover_2 1 1 0 2 8 14 526 3
cert_coverFacet 2 714
cert_cover_5 2 0 0 2 5 6 138 714 2
cert_coverFacet 3 124
cert_cover_5 3 1 1 2 3 4 28 124 3
cert_coverFacet 4 540
cert_cover_2 4 2 1 3 8 28 540 3
cert_coverFacet 5 460
cert_cover_5 5 2 1 2 5 6 76 460 3
cert_coverFacet 6 308
cert_cover_2 6 3 1 4 7 52 308 3
cert_coverFacet 7 356
cert_cover_2 7 4 1 5 7 100 356 3
cert_coverFacet 8 600
cert_cover_2 8 3 2 5 8 88 600 3
cert_coverFacet 9 992
cert_cover_5 9 3 4 5 6 7 352 992 2
cert_coveringFacets_5
cert_coveringProof
cert_certificate 4 10
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0776

end
end BundlePart5

section BundlePart6
/- Source: ProjectionCertificates/R_m16e10q1_0777.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0777

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [391, 155, 531, 835, 601, 233, 449, 182, 310, 786, 620, 228, 804, 964, 184, 824, 19, 131, 259, 515, 25, 73, 137, 529, 193, 321, 577, 385, 54, 134, 262, 146, 274, 530, 770, 100, 164, 292, 548, 196, 580, 388, 772, 56, 152, 536, 104, 168, 552, 584, 176, 304, 784, 224, 800, 448, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_391, vertices_155, vertices_531, vertices_835, vertices_601, vertices_233, vertices_449, vertices_182, vertices_310, vertices_786, vertices_620, vertices_228, vertices_804, vertices_964, vertices_184, vertices_824] (by decide +kernel)
  polygons := literalFinset [vertices_19, vertices_131, vertices_259, vertices_515, vertices_25, vertices_73, vertices_137, vertices_529, vertices_193, vertices_321, vertices_577, vertices_385, vertices_54, vertices_134, vertices_262, vertices_146, vertices_274, vertices_530, vertices_770, vertices_100, vertices_164, vertices_292, vertices_548, vertices_196, vertices_580, vertices_388, vertices_772, vertices_56, vertices_152, vertices_536, vertices_104, vertices_168, vertices_552, vertices_584, vertices_176, vertices_304, vertices_784, vertices_224, vertices_800, vertices_448, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_391), (false, vertices_155), (false, vertices_531), (false, vertices_835), (false, vertices_601), (false, vertices_233), (false, vertices_449), (true, vertices_54), (true, vertices_274), (true, vertices_100), (true, vertices_164), (true, vertices_292), (true, vertices_548), (true, vertices_196), (true, vertices_580), (true, vertices_772), (true, vertices_56), (true, vertices_552), (true, vertices_176), (true, vertices_304), (true, vertices_784), (true, vertices_800)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 19 16 22 25 26 27 28 29 30
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_391) then 17 else
  if p.val = (false, vertices_155) then 20 else
  if p.val = (false, vertices_531) then 0 else
  if p.val = (false, vertices_835) then 21 else
  if p.val = (false, vertices_601) then 23 else
  if p.val = (false, vertices_233) then 24 else
  if p.val = (false, vertices_449) then 1 else
  if p.val = (true, vertices_54) then 18 else
  if p.val = (true, vertices_274) then 2 else
  if p.val = (true, vertices_100) then 3 else
  if p.val = (true, vertices_164) then 4 else
  if p.val = (true, vertices_292) then 5 else
  if p.val = (true, vertices_548) then 6 else
  if p.val = (true, vertices_196) then 7 else
  if p.val = (true, vertices_580) then 8 else
  if p.val = (true, vertices_772) then 9 else
  if p.val = (true, vertices_56) then 10 else
  if p.val = (true, vertices_552) then 11 else
  if p.val = (true, vertices_176) then 12 else
  if p.val = (true, vertices_304) then 13 else
  if p.val = (true, vertices_784) then 14 else
  if p.val = (true, vertices_800) then 15 else
  0
cert_priority
cert_nodeAtPriority_39 1 531 0 449 274 100 164 292 548 196 580 772 56 552 176 304 784 800 391 54 155 835 601 233
cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 1 3 4 54
cert_row_4 1 1 5 6 7 8 964 196 3
cert_row_4 2 1 2 4 5 8 620 100 1
cert_row_4 3 2 3 4 7 8 824 56 3
cert_rows
cert_pivot_2 0 6 1 2
cert_heightProof 4
cert_coverFacet 0 182
cert_cover_5 0 0 0 1 3 6 54 182 3
cert_coverFacet 1 310
cert_cover_5 1 0 0 1 3 7 54 310 3
cert_coverFacet 2 786
cert_cover_2 2 3 0 7 8 274 786 3
cert_coverFacet 3 620
cert_cover_5 3 2 1 2 4 5 100 620 1
cert_coverFacet 4 228
cert_cover_2 4 4 1 5 6 100 228 3
cert_coverFacet 5 804
cert_cover_2 5 4 1 7 8 292 804 3
cert_coverFacet 6 964
cert_cover_5 6 1 1 5 6 7 196 964 3
cert_coverFacet 7 184
cert_cover_2 7 3 2 4 6 56 184 3
cert_coverFacet 8 824
cert_cover_5 8 3 2 3 4 7 56 824 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0777

end
end BundlePart6

section BundlePart7
/- Source: ProjectionCertificates/R_m16e10q1_0778.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0778

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [583, 339, 803, 181, 85, 549, 313, 714, 450, 898, 604, 668, 932, 184, 344, 488, 67, 259, 515, 21, 37, 69, 517, 49, 81, 273, 289, 545, 194, 322, 578, 386, 642, 770, 540, 84, 148, 164, 548, 580, 644, 56, 88, 152, 280, 168, 296, 200, 328, 584, 648, 176, 336, 416, 800, 448, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_583, vertices_339, vertices_803, vertices_181, vertices_85, vertices_549, vertices_313, vertices_714, vertices_450, vertices_898, vertices_604, vertices_668, vertices_932, vertices_184, vertices_344, vertices_488] (by decide +kernel)
  polygons := literalFinset [vertices_67, vertices_259, vertices_515, vertices_21, vertices_37, vertices_69, vertices_517, vertices_49, vertices_81, vertices_273, vertices_289, vertices_545, vertices_194, vertices_322, vertices_578, vertices_386, vertices_642, vertices_770, vertices_540, vertices_84, vertices_148, vertices_164, vertices_548, vertices_580, vertices_644, vertices_56, vertices_88, vertices_152, vertices_280, vertices_168, vertices_296, vertices_200, vertices_328, vertices_584, vertices_648, vertices_176, vertices_336, vertices_416, vertices_800, vertices_448, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_583), (false, vertices_339), (false, vertices_803), (false, vertices_181), (false, vertices_85), (false, vertices_549), (false, vertices_313), (true, vertices_194), (true, vertices_386), (true, vertices_642), (true, vertices_540), (true, vertices_644), (true, vertices_88), (true, vertices_152), (true, vertices_168), (true, vertices_200), (true, vertices_328), (true, vertices_584), (true, vertices_648), (true, vertices_416), (true, vertices_448), (true, vertices_896)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 16 20 23 25 26 27 28 29 30
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_583) then 17 else
  if p.val = (false, vertices_339) then 18 else
  if p.val = (false, vertices_803) then 19 else
  if p.val = (false, vertices_181) then 21 else
  if p.val = (false, vertices_85) then 0 else
  if p.val = (false, vertices_549) then 1 else
  if p.val = (false, vertices_313) then 24 else
  if p.val = (true, vertices_194) then 2 else
  if p.val = (true, vertices_386) then 3 else
  if p.val = (true, vertices_642) then 4 else
  if p.val = (true, vertices_540) then 22 else
  if p.val = (true, vertices_644) then 5 else
  if p.val = (true, vertices_88) then 6 else
  if p.val = (true, vertices_152) then 7 else
  if p.val = (true, vertices_168) then 8 else
  if p.val = (true, vertices_200) then 9 else
  if p.val = (true, vertices_328) then 10 else
  if p.val = (true, vertices_584) then 11 else
  if p.val = (true, vertices_648) then 12 else
  if p.val = (true, vertices_416) then 13 else
  if p.val = (true, vertices_448) then 14 else
  if p.val = (true, vertices_896) then 15 else
  0
cert_priority
cert_nodeAtPriority_60 85 549 194 386 642 644 88 152 168 200 328 584 648 416 448 896 583 339 803 181 540 313
cert_priority_injective
cert_incidenceProof
cert_row_2 0 1 2 3 8 540
cert_row_4 1 0 2 5 6 8 714 194 1
cert_row_4 2 1 4 6 7 8 932 164 3
cert_row_4 3 2 4 5 6 7 488 168 2
cert_rows
cert_pivot_2 3 0 1 2
cert_heightProof 4
cert_coverFacet 0 714
cert_cover_5 0 1 0 2 5 6 194 714 1
cert_coverFacet 1 450
cert_cover_2 1 5 0 6 7 194 450 3
cert_coverFacet 2 898
cert_cover_2 2 6 0 7 8 386 898 3
cert_coverFacet 3 604
cert_cover_5 3 0 1 2 3 5 540 604 3
cert_coverFacet 4 668
cert_cover_5 4 0 1 2 3 6 540 668 3
cert_coverFacet 5 932
cert_cover_5 5 2 1 4 6 7 164 932 3
cert_coverFacet 6 184
cert_cover_2 6 3 2 4 6 56 184 3
cert_coverFacet 7 344
cert_cover_2 7 3 2 5 7 88 344 3
cert_coverFacet 8 488
cert_cover_5 8 3 2 4 5 6 168 488 2
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0778

end
end BundlePart7

section BundlePart8
/- Source: ProjectionCertificates/R_m16e10q1_0779.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0779

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [403, 421, 601, 281, 809, 689, 598, 358, 390, 646, 346, 658, 236, 716, 360, 680, 25, 265, 521, 145, 273, 529, 161, 289, 545, 385, 70, 134, 262, 518, 82, 146, 274, 530, 322, 386, 642, 204, 100, 164, 292, 580, 388, 644, 88, 280, 104, 168, 296, 552, 328, 584, 648, 592, 656, 352, 672]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_403, vertices_421, vertices_601, vertices_281, vertices_809, vertices_689, vertices_598, vertices_358, vertices_390, vertices_646, vertices_346, vertices_658, vertices_236, vertices_716, vertices_360, vertices_680] (by decide +kernel)
  polygons := literalFinset [vertices_25, vertices_265, vertices_521, vertices_145, vertices_273, vertices_529, vertices_161, vertices_289, vertices_545, vertices_385, vertices_70, vertices_134, vertices_262, vertices_518, vertices_82, vertices_146, vertices_274, vertices_530, vertices_322, vertices_386, vertices_642, vertices_204, vertices_100, vertices_164, vertices_292, vertices_580, vertices_388, vertices_644, vertices_88, vertices_280, vertices_104, vertices_168, vertices_296, vertices_552, vertices_328, vertices_584, vertices_648, vertices_592, vertices_656, vertices_352, vertices_672] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_403), (false, vertices_421), (false, vertices_601), (false, vertices_281), (false, vertices_809), (false, vertices_689), (true, vertices_70), (true, vertices_134), (true, vertices_262), (true, vertices_518), (true, vertices_82), (true, vertices_530), (true, vertices_322), (true, vertices_642), (true, vertices_204), (true, vertices_100), (true, vertices_580), (true, vertices_644), (true, vertices_104), (true, vertices_168), (true, vertices_328), (true, vertices_648), (true, vertices_352)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 17 19 22 25 27 28 29 30 31
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_403) then 18 else
  if p.val = (false, vertices_421) then 20 else
  if p.val = (false, vertices_601) then 23 else
  if p.val = (false, vertices_281) then 0 else
  if p.val = (false, vertices_809) then 24 else
  if p.val = (false, vertices_689) then 26 else
  if p.val = (true, vertices_70) then 1 else
  if p.val = (true, vertices_134) then 2 else
  if p.val = (true, vertices_262) then 3 else
  if p.val = (true, vertices_518) then 4 else
  if p.val = (true, vertices_82) then 5 else
  if p.val = (true, vertices_530) then 6 else
  if p.val = (true, vertices_322) then 7 else
  if p.val = (true, vertices_642) then 8 else
  if p.val = (true, vertices_204) then 21 else
  if p.val = (true, vertices_100) then 9 else
  if p.val = (true, vertices_580) then 10 else
  if p.val = (true, vertices_644) then 11 else
  if p.val = (true, vertices_104) then 12 else
  if p.val = (true, vertices_168) then 13 else
  if p.val = (true, vertices_328) then 14 else
  if p.val = (true, vertices_648) then 15 else
  if p.val = (true, vertices_352) then 16 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_281), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_70), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_134), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_262), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_518), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_82), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_530), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_322), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_642), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_100), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_580), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_644), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_104), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_168), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_328), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_648), by decide +kernel⟩
  | 16 => Sum.inr ⟨(true, vertices_352), by decide +kernel⟩
  | 17 => Sum.inl 0
  | 18 => Sum.inr ⟨(false, vertices_403), by decide +kernel⟩
  | 19 => Sum.inl 1
  | 20 => Sum.inr ⟨(false, vertices_421), by decide +kernel⟩
  | 21 => Sum.inr ⟨(true, vertices_204), by decide +kernel⟩
  | 22 => Sum.inl 2
  | 23 => Sum.inr ⟨(false, vertices_601), by decide +kernel⟩
  | 24 => Sum.inr ⟨(false, vertices_809), by decide +kernel⟩
  | 25 => Sum.inl 3
  | 26 => Sum.inr ⟨(false, vertices_689), by decide +kernel⟩
  | 27 => Sum.inl 4
  | 28 => Sum.inl 5
  | 29 => Sum.inl 6
  | 30 => Sum.inl 7
  | 31 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 1 2 5 6 204
cert_row_4 1 0 1 3 5 8 598 70 2
cert_row_4 2 0 1 4 5 7 358 70 2
cert_row_4 3 0 2 3 5 7 346 82 1
cert_rows
cert_pivot_2 6 8 1 0
cert_heightProof 4
cert_coverFacet 0 598
cert_cover_5 0 1 0 1 3 5 70 598 2
cert_coverFacet 1 358
cert_cover_5 1 2 0 1 4 5 70 358 2
cert_coverFacet 2 390
cert_cover_2 2 1 0 6 7 134 390 3
cert_coverFacet 3 646
cert_cover_2 3 1 0 6 8 134 646 3
cert_coverFacet 4 346
cert_cover_5 4 3 0 2 3 5 82 346 1
cert_coverFacet 5 658
cert_cover_2 5 3 0 6 8 146 658 3
cert_coverFacet 6 236
cert_cover_5 6 0 1 2 4 5 204 236 2
cert_coverFacet 7 716
cert_cover_5 7 0 1 2 5 8 204 716 3
cert_coverFacet 8 360
cert_cover_2 8 4 2 5 7 104 360 3
cert_coverFacet 9 680
cert_cover_2 9 4 2 6 8 168 680 3
cert_coveringFacets_5
cert_coveringProof
cert_certificate 4 10
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0779

end
end BundlePart8

section BundlePart9
/- Source: ProjectionCertificates/R_m16e10q1_0780.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0780

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [899, 333, 229, 389, 689, 865, 398, 186, 282, 850, 658, 572, 604, 172, 612, 344, 69, 133, 261, 97, 161, 545, 321, 385, 641, 769, 26, 138, 266, 146, 274, 530, 386, 642, 770, 540, 44, 76, 140, 268, 100, 164, 548, 580, 388, 56, 88, 280, 168, 328, 176, 560, 336, 592, 656, 608, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_899, vertices_333, vertices_229, vertices_389, vertices_689, vertices_865, vertices_398, vertices_186, vertices_282, vertices_850, vertices_658, vertices_572, vertices_604, vertices_172, vertices_612, vertices_344] (by decide +kernel)
  polygons := literalFinset [vertices_69, vertices_133, vertices_261, vertices_97, vertices_161, vertices_545, vertices_321, vertices_385, vertices_641, vertices_769, vertices_26, vertices_138, vertices_266, vertices_146, vertices_274, vertices_530, vertices_386, vertices_642, vertices_770, vertices_540, vertices_44, vertices_76, vertices_140, vertices_268, vertices_100, vertices_164, vertices_548, vertices_580, vertices_388, vertices_56, vertices_88, vertices_280, vertices_168, vertices_328, vertices_176, vertices_560, vertices_336, vertices_592, vertices_656, vertices_608, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_899), (false, vertices_333), (false, vertices_229), (false, vertices_389), (false, vertices_689), (false, vertices_865), (true, vertices_26), (true, vertices_138), (true, vertices_266), (true, vertices_146), (true, vertices_274), (true, vertices_530), (true, vertices_540), (true, vertices_44), (true, vertices_140), (true, vertices_548), (true, vertices_580), (true, vertices_56), (true, vertices_88), (true, vertices_280), (true, vertices_168), (true, vertices_336), (true, vertices_592)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 17 19 23 24 26 28 29 30 31
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_899) then 18 else
  if p.val = (false, vertices_333) then 20 else
  if p.val = (false, vertices_229) then 21 else
  if p.val = (false, vertices_389) then 0 else
  if p.val = (false, vertices_689) then 25 else
  if p.val = (false, vertices_865) then 27 else
  if p.val = (true, vertices_26) then 1 else
  if p.val = (true, vertices_138) then 2 else
  if p.val = (true, vertices_266) then 3 else
  if p.val = (true, vertices_146) then 4 else
  if p.val = (true, vertices_274) then 5 else
  if p.val = (true, vertices_530) then 6 else
  if p.val = (true, vertices_540) then 22 else
  if p.val = (true, vertices_44) then 7 else
  if p.val = (true, vertices_140) then 8 else
  if p.val = (true, vertices_548) then 9 else
  if p.val = (true, vertices_580) then 10 else
  if p.val = (true, vertices_56) then 11 else
  if p.val = (true, vertices_88) then 12 else
  if p.val = (true, vertices_280) then 13 else
  if p.val = (true, vertices_168) then 14 else
  if p.val = (true, vertices_336) then 15 else
  if p.val = (true, vertices_592) then 16 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_389), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_26), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_138), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_266), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_146), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_274), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_530), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_44), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_140), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_548), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_580), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_56), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_88), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_280), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_168), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_336), by decide +kernel⟩
  | 16 => Sum.inr ⟨(true, vertices_592), by decide +kernel⟩
  | 17 => Sum.inl 0
  | 18 => Sum.inr ⟨(false, vertices_899), by decide +kernel⟩
  | 19 => Sum.inl 1
  | 20 => Sum.inr ⟨(false, vertices_333), by decide +kernel⟩
  | 21 => Sum.inr ⟨(false, vertices_229), by decide +kernel⟩
  | 22 => Sum.inr ⟨(true, vertices_540), by decide +kernel⟩
  | 23 => Sum.inl 2
  | 24 => Sum.inl 3
  | 25 => Sum.inr ⟨(false, vertices_689), by decide +kernel⟩
  | 26 => Sum.inl 4
  | 27 => Sum.inr ⟨(false, vertices_865), by decide +kernel⟩
  | 28 => Sum.inl 5
  | 29 => Sum.inl 6
  | 30 => Sum.inl 7
  | 31 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 2 3 4 6 186 26 3
cert_row_4 1 0 1 2 6 7 398 138 1
cert_row_2 2 1 2 3 8 540
cert_row_4 3 0 3 5 7 8 850 274 2
cert_rows
cert_pivot_2 4 6 1 0
cert_heightProof 4
cert_coverFacet 0 398
cert_cover_5 0 1 0 1 2 6 138 398 1
cert_coverFacet 1 186
cert_cover_5 1 0 0 2 3 4 26 186 3
cert_coverFacet 2 282
cert_cover_2 2 2 0 3 7 26 282 3
cert_coverFacet 3 850
cert_cover_5 3 3 0 3 5 7 274 850 2
cert_coverFacet 4 658
cert_cover_2 4 3 0 6 8 146 658 3
cert_coverFacet 5 572
cert_cover_5 5 2 1 2 3 4 540 572 3
cert_coverFacet 6 604
cert_cover_5 6 2 1 2 3 5 540 604 3
cert_coverFacet 7 172
cert_cover_2 7 2 1 4 6 44 172 3
cert_coverFacet 8 612
cert_cover_2 8 4 1 5 8 100 612 3
cert_coverFacet 9 344
cert_cover_2 9 3 2 5 7 88 344 3
cert_coveringFacets_5
cert_coveringProof
cert_certificate 4 10
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0780

end
end BundlePart9

section BundlePart10
/- Source: ProjectionCertificates/R_m16e10q1_0781.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0781

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [271, 525, 677, 453, 617, 329, 241, 542, 902, 282, 626, 306, 930, 472, 600, 432, 13, 133, 261, 517, 73, 265, 521, 97, 161, 545, 193, 321, 14, 262, 518, 26, 266, 50, 274, 530, 290, 546, 898, 524, 388, 644, 88, 280, 536, 328, 584, 112, 176, 304, 208, 592, 400, 608, 416, 672, 448]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_271, vertices_525, vertices_677, vertices_453, vertices_617, vertices_329, vertices_241, vertices_542, vertices_902, vertices_282, vertices_626, vertices_306, vertices_930, vertices_472, vertices_600, vertices_432] (by decide +kernel)
  polygons := literalFinset [vertices_13, vertices_133, vertices_261, vertices_517, vertices_73, vertices_265, vertices_521, vertices_97, vertices_161, vertices_545, vertices_193, vertices_321, vertices_14, vertices_262, vertices_518, vertices_26, vertices_266, vertices_50, vertices_274, vertices_530, vertices_290, vertices_546, vertices_898, vertices_524, vertices_388, vertices_644, vertices_88, vertices_280, vertices_536, vertices_328, vertices_584, vertices_112, vertices_176, vertices_304, vertices_208, vertices_592, vertices_400, vertices_608, vertices_416, vertices_672, vertices_448] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_271), (false, vertices_525), (false, vertices_677), (false, vertices_453), (false, vertices_617), (false, vertices_329), (false, vertices_241), (true, vertices_518), (true, vertices_26), (true, vertices_50), (true, vertices_274), (true, vertices_530), (true, vertices_290), (true, vertices_546), (true, vertices_898), (true, vertices_88), (true, vertices_280), (true, vertices_536), (true, vertices_304), (true, vertices_592), (true, vertices_400), (true, vertices_416)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 16 19 22 24 26 27 28 29 30
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_271) then 17 else
  if p.val = (false, vertices_525) then 0 else
  if p.val = (false, vertices_677) then 20 else
  if p.val = (false, vertices_453) then 21 else
  if p.val = (false, vertices_617) then 23 else
  if p.val = (false, vertices_329) then 1 else
  if p.val = (false, vertices_241) then 25 else
  if p.val = (true, vertices_518) then 2 else
  if p.val = (true, vertices_26) then 3 else
  if p.val = (true, vertices_50) then 4 else
  if p.val = (true, vertices_274) then 5 else
  if p.val = (true, vertices_530) then 6 else
  if p.val = (true, vertices_290) then 7 else
  if p.val = (true, vertices_546) then 8 else
  if p.val = (true, vertices_898) then 18 else
  if p.val = (true, vertices_88) then 9 else
  if p.val = (true, vertices_280) then 10 else
  if p.val = (true, vertices_536) then 11 else
  if p.val = (true, vertices_304) then 12 else
  if p.val = (true, vertices_592) then 13 else
  if p.val = (true, vertices_400) then 14 else
  if p.val = (true, vertices_416) then 15 else
  0
cert_priority
cert_nodeAtPriority_50 1 525 0 329 518 26 50 274 530 290 546 88 280 536 304 592 400 416 271 898 677 453 617 241
cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 2 3 8 542 14 3
cert_row_4 1 0 3 4 5 8 626 50 3
cert_row_2 2 0 6 7 8 898
cert_row_4 3 2 3 5 6 7 472 88 3
cert_rows
cert_pivot_2 1 4 0 2
cert_heightProof 4
cert_coverFacet 0 542
cert_cover_5 0 0 0 1 2 3 14 542 3
cert_coverFacet 1 902
cert_cover_5 1 2 0 1 6 7 262 902 2
cert_coverFacet 2 282
cert_cover_2 2 2 0 3 7 26 282 3
cert_coverFacet 3 626
cert_cover_5 3 1 0 3 4 5 50 626 3
cert_coverFacet 4 306
cert_cover_2 4 3 0 4 7 50 306 3
cert_coverFacet 5 930
cert_cover_5 5 2 0 4 6 7 290 930 2
cert_coverFacet 6 472
cert_cover_5 6 3 2 3 5 6 88 472 3
cert_coverFacet 7 600
cert_cover_2 7 3 2 5 8 88 600 3
cert_coverFacet 8 432
cert_cover_2 8 4 3 6 7 176 432 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0781

end
end BundlePart10

section BundlePart11
/- Source: ProjectionCertificates/R_m16e10q1_0782.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0782

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [659, 613, 421, 901, 601, 241, 286, 558, 774, 538, 466, 898, 300, 344, 488, 616, 37, 389, 517, 81, 145, 529, 97, 161, 577, 641, 14, 262, 518, 26, 522, 146, 274, 530, 386, 642, 770, 44, 268, 292, 548, 772, 88, 280, 536, 104, 296, 552, 328, 584, 208, 336, 224, 608, 416, 448, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_659, vertices_613, vertices_421, vertices_901, vertices_601, vertices_241, vertices_286, vertices_558, vertices_774, vertices_538, vertices_466, vertices_898, vertices_300, vertices_344, vertices_488, vertices_616] (by decide +kernel)
  polygons := literalFinset [vertices_37, vertices_389, vertices_517, vertices_81, vertices_145, vertices_529, vertices_97, vertices_161, vertices_577, vertices_641, vertices_14, vertices_262, vertices_518, vertices_26, vertices_522, vertices_146, vertices_274, vertices_530, vertices_386, vertices_642, vertices_770, vertices_44, vertices_268, vertices_292, vertices_548, vertices_772, vertices_88, vertices_280, vertices_536, vertices_104, vertices_296, vertices_552, vertices_328, vertices_584, vertices_208, vertices_336, vertices_224, vertices_608, vertices_416, vertices_448, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_659), (false, vertices_613), (false, vertices_421), (false, vertices_901), (false, vertices_601), (false, vertices_241), (true, vertices_14), (true, vertices_262), (true, vertices_518), (true, vertices_26), (true, vertices_522), (true, vertices_274), (true, vertices_386), (true, vertices_770), (true, vertices_44), (true, vertices_268), (true, vertices_280), (true, vertices_104), (true, vertices_296), (true, vertices_552), (true, vertices_328), (true, vertices_336), (true, vertices_448)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 17 19 23 25 27 28 29 30 31
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_659) then 18 else
  if p.val = (false, vertices_613) then 20 else
  if p.val = (false, vertices_421) then 21 else
  if p.val = (false, vertices_901) then 22 else
  if p.val = (false, vertices_601) then 24 else
  if p.val = (false, vertices_241) then 26 else
  if p.val = (true, vertices_14) then 0 else
  if p.val = (true, vertices_262) then 1 else
  if p.val = (true, vertices_518) then 2 else
  if p.val = (true, vertices_26) then 3 else
  if p.val = (true, vertices_522) then 4 else
  if p.val = (true, vertices_274) then 5 else
  if p.val = (true, vertices_386) then 6 else
  if p.val = (true, vertices_770) then 7 else
  if p.val = (true, vertices_44) then 8 else
  if p.val = (true, vertices_268) then 9 else
  if p.val = (true, vertices_280) then 10 else
  if p.val = (true, vertices_104) then 11 else
  if p.val = (true, vertices_296) then 12 else
  if p.val = (true, vertices_552) then 13 else
  if p.val = (true, vertices_328) then 14 else
  if p.val = (true, vertices_336) then 15 else
  if p.val = (true, vertices_448) then 16 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_14), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_262), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_518), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_26), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_522), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_274), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_386), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_770), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_44), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_268), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_280), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_104), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_296), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_552), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_328), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_336), by decide +kernel⟩
  | 16 => Sum.inr ⟨(true, vertices_448), by decide +kernel⟩
  | 17 => Sum.inl 0
  | 18 => Sum.inr ⟨(false, vertices_659), by decide +kernel⟩
  | 19 => Sum.inl 1
  | 20 => Sum.inr ⟨(false, vertices_613), by decide +kernel⟩
  | 21 => Sum.inr ⟨(false, vertices_421), by decide +kernel⟩
  | 22 => Sum.inr ⟨(false, vertices_901), by decide +kernel⟩
  | 23 => Sum.inl 2
  | 24 => Sum.inr ⟨(false, vertices_601), by decide +kernel⟩
  | 25 => Sum.inl 3
  | 26 => Sum.inr ⟨(false, vertices_241), by decide +kernel⟩
  | 27 => Sum.inl 4
  | 28 => Sum.inl 5
  | 29 => Sum.inl 6
  | 30 => Sum.inl 7
  | 31 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 2 4 8 558 14 3
cert_row_4 1 0 1 2 3 7 286 14 3
cert_row_4 2 0 3 5 6 7 466 146 2
cert_row_4 3 2 4 5 6 7 488 104 3
cert_rows
cert_pivot_2 8 1 0 2
cert_heightProof 4
cert_coverFacet 0 286
cert_cover_5 0 1 0 1 2 3 14 286 3
cert_coverFacet 1 558
cert_cover_5 1 0 0 1 2 4 14 558 3
cert_coverFacet 2 774
cert_cover_2 2 1 0 7 8 262 774 3
cert_coverFacet 3 538
cert_cover_2 3 2 0 3 8 26 538 3
cert_coverFacet 4 466
cert_cover_5 4 2 0 3 5 6 146 466 2
cert_coverFacet 5 898
cert_cover_2 5 6 0 7 8 386 898 3
cert_coverFacet 6 300
cert_cover_2 6 2 1 4 7 44 300 3
cert_coverFacet 7 344
cert_cover_2 7 3 2 5 7 88 344 3
cert_coverFacet 8 488
cert_cover_5 8 3 2 4 5 6 104 488 3
cert_coverFacet 9 616
cert_cover_2 9 4 2 5 8 104 616 3
cert_coveringFacets_5
cert_coveringProof
cert_certificate 4 10
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0782

end
end BundlePart11

section BundlePart12
/- Source: ProjectionCertificates/R_m16e10q1_0783.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0783

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [835, 541, 309, 709, 325, 57, 809, 454, 234, 618, 434, 802, 404, 660, 184, 728, 21, 69, 261, 517, 25, 41, 521, 49, 289, 321, 577, 769, 106, 162, 290, 546, 194, 322, 578, 386, 770, 148, 276, 532, 196, 324, 388, 644, 56, 152, 536, 168, 552, 200, 584, 176, 304, 400, 656, 800, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_835, vertices_541, vertices_309, vertices_709, vertices_325, vertices_57, vertices_809, vertices_454, vertices_234, vertices_618, vertices_434, vertices_802, vertices_404, vertices_660, vertices_184, vertices_728] (by decide +kernel)
  polygons := literalFinset [vertices_21, vertices_69, vertices_261, vertices_517, vertices_25, vertices_41, vertices_521, vertices_49, vertices_289, vertices_321, vertices_577, vertices_769, vertices_106, vertices_162, vertices_290, vertices_546, vertices_194, vertices_322, vertices_578, vertices_386, vertices_770, vertices_148, vertices_276, vertices_532, vertices_196, vertices_324, vertices_388, vertices_644, vertices_56, vertices_152, vertices_536, vertices_168, vertices_552, vertices_200, vertices_584, vertices_176, vertices_304, vertices_400, vertices_656, vertices_800, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_835), (false, vertices_541), (false, vertices_309), (false, vertices_709), (false, vertices_325), (false, vertices_57), (false, vertices_809), (true, vertices_106), (true, vertices_162), (true, vertices_290), (true, vertices_546), (true, vertices_194), (true, vertices_386), (true, vertices_148), (true, vertices_388), (true, vertices_152), (true, vertices_168), (true, vertices_200), (true, vertices_584), (true, vertices_176), (true, vertices_400), (true, vertices_656)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 16 19 23 25 26 27 28 29 30
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_835) then 17 else
  if p.val = (false, vertices_541) then 20 else
  if p.val = (false, vertices_309) then 21 else
  if p.val = (false, vertices_709) then 22 else
  if p.val = (false, vertices_325) then 0 else
  if p.val = (false, vertices_57) then 1 else
  if p.val = (false, vertices_809) then 24 else
  if p.val = (true, vertices_106) then 18 else
  if p.val = (true, vertices_162) then 2 else
  if p.val = (true, vertices_290) then 3 else
  if p.val = (true, vertices_546) then 4 else
  if p.val = (true, vertices_194) then 5 else
  if p.val = (true, vertices_386) then 6 else
  if p.val = (true, vertices_148) then 7 else
  if p.val = (true, vertices_388) then 8 else
  if p.val = (true, vertices_152) then 9 else
  if p.val = (true, vertices_168) then 10 else
  if p.val = (true, vertices_200) then 11 else
  if p.val = (true, vertices_584) then 12 else
  if p.val = (true, vertices_176) then 13 else
  if p.val = (true, vertices_400) then 14 else
  if p.val = (true, vertices_656) then 15 else
  0
cert_priority
cert_nodeAtPriority_5 0 325 1 57 162 290 546 194 386 148 388 152 168 200 584 176 400 656 835 106 541 309 709 809
cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 5 6 7 454 194 1
cert_row_4 1 0 3 4 6 7 434 162 1
cert_row_2 2 0 2 4 5 106
cert_row_4 3 2 3 5 6 8 728 152 2
cert_rows
cert_pivot_2 1 7 0 2
cert_heightProof 4
cert_coverFacet 0 454
cert_cover_5 0 0 0 1 5 6 194 454 1
cert_coverFacet 1 234
cert_cover_5 1 2 0 2 4 6 106 234 3
cert_coverFacet 2 618
cert_cover_5 2 2 0 2 4 8 106 618 3
cert_coverFacet 3 434
cert_cover_5 3 1 0 3 4 6 162 434 1
cert_coverFacet 4 802
cert_cover_2 4 4 0 7 8 290 802 3
cert_coverFacet 5 404
cert_cover_2 5 3 1 6 7 148 404 3
cert_coverFacet 6 660
cert_cover_2 6 3 1 6 8 148 660 3
cert_coverFacet 7 184
cert_cover_2 7 3 2 4 6 56 184 3
cert_coverFacet 8 728
cert_cover_5 8 3 2 3 5 6 152 728 2
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0783

end
end BundlePart12

section BundlePart13
/- Source: ProjectionCertificates/R_m16e10q1_0784.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0784

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [171, 267, 355, 781, 649, 241, 961, 158, 286, 178, 818, 716, 628, 212, 788, 864, 11, 35, 259, 137, 265, 521, 97, 161, 193, 321, 641, 769, 30, 138, 266, 50, 146, 274, 162, 290, 140, 268, 524, 84, 148, 276, 532, 196, 580, 772, 648, 112, 176, 560, 208, 784, 352, 608, 800, 704, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_171, vertices_267, vertices_355, vertices_781, vertices_649, vertices_241, vertices_961, vertices_158, vertices_286, vertices_178, vertices_818, vertices_716, vertices_628, vertices_212, vertices_788, vertices_864] (by decide +kernel)
  polygons := literalFinset [vertices_11, vertices_35, vertices_259, vertices_137, vertices_265, vertices_521, vertices_97, vertices_161, vertices_193, vertices_321, vertices_641, vertices_769, vertices_30, vertices_138, vertices_266, vertices_50, vertices_146, vertices_274, vertices_162, vertices_290, vertices_140, vertices_268, vertices_524, vertices_84, vertices_148, vertices_276, vertices_532, vertices_196, vertices_580, vertices_772, vertices_648, vertices_112, vertices_176, vertices_560, vertices_208, vertices_784, vertices_352, vertices_608, vertices_800, vertices_704, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_171), (false, vertices_267), (false, vertices_355), (false, vertices_781), (false, vertices_649), (false, vertices_241), (false, vertices_961), (true, vertices_30), (true, vertices_50), (true, vertices_146), (true, vertices_274), (true, vertices_140), (true, vertices_84), (true, vertices_148), (true, vertices_276), (true, vertices_532), (true, vertices_196), (true, vertices_580), (true, vertices_560), (true, vertices_784), (true, vertices_608), (true, vertices_800)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 16 20 22 23 25 26 28 29 30
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_171) then 17 else
  if p.val = (false, vertices_267) then 0 else
  if p.val = (false, vertices_355) then 18 else
  if p.val = (false, vertices_781) then 21 else
  if p.val = (false, vertices_649) then 1 else
  if p.val = (false, vertices_241) then 24 else
  if p.val = (false, vertices_961) then 27 else
  if p.val = (true, vertices_30) then 19 else
  if p.val = (true, vertices_50) then 2 else
  if p.val = (true, vertices_146) then 3 else
  if p.val = (true, vertices_274) then 4 else
  if p.val = (true, vertices_140) then 5 else
  if p.val = (true, vertices_84) then 6 else
  if p.val = (true, vertices_148) then 7 else
  if p.val = (true, vertices_276) then 8 else
  if p.val = (true, vertices_532) then 9 else
  if p.val = (true, vertices_196) then 10 else
  if p.val = (true, vertices_580) then 11 else
  if p.val = (true, vertices_560) then 12 else
  if p.val = (true, vertices_784) then 13 else
  if p.val = (true, vertices_608) then 14 else
  if p.val = (true, vertices_800) then 15 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_267), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_649), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_50), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_146), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_274), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_140), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_84), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_148), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_276), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_532), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_196), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_580), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_560), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_784), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_608), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_800), by decide +kernel⟩
  | 16 => Sum.inl 0
  | 17 => Sum.inr ⟨(false, vertices_171), by decide +kernel⟩
  | 18 => Sum.inr ⟨(false, vertices_355), by decide +kernel⟩
  | 19 => Sum.inr ⟨(true, vertices_30), by decide +kernel⟩
  | 20 => Sum.inl 1
  | 21 => Sum.inr ⟨(false, vertices_781), by decide +kernel⟩
  | 22 => Sum.inl 2
  | 23 => Sum.inl 3
  | 24 => Sum.inr ⟨(false, vertices_241), by decide +kernel⟩
  | 25 => Sum.inl 4
  | 26 => Sum.inl 5
  | 27 => Sum.inr ⟨(false, vertices_961), by decide +kernel⟩
  | 28 => Sum.inl 6
  | 29 => Sum.inl 7
  | 30 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 3 4 7 8 818 50 3
cert_row_2 1 0 1 2 3 30
cert_row_4 2 1 2 5 6 8 716 140 2
cert_row_4 3 1 3 4 5 8 628 84 2
cert_rows
cert_pivot_2 7 0 2 1
cert_heightProof 4
cert_coverFacet 0 158
cert_cover_5 0 1 0 1 2 6 30 158 3
cert_coverFacet 1 286
cert_cover_5 1 1 0 1 2 7 30 286 3
cert_coverFacet 2 178
cert_cover_2 2 3 0 4 6 50 178 3
cert_coverFacet 3 818
cert_cover_5 3 0 0 3 4 7 50 818 3
cert_coverFacet 4 716
cert_cover_5 4 2 1 2 5 6 140 716 2
cert_coverFacet 5 628
cert_cover_5 5 3 1 3 4 5 84 628 2
cert_coverFacet 6 212
cert_cover_2 6 3 1 5 6 84 212 3
cert_coverFacet 7 788
cert_cover_2 7 3 1 7 8 276 788 3
cert_coverFacet 8 864
cert_cover_2 8 5 4 7 8 352 864 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0784

end
end BundlePart13

section BundlePart14
/- Source: ProjectionCertificates/R_m16e10q1_0785.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0785

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [451, 565, 85, 837, 217, 793, 393, 678, 426, 818, 706, 834, 124, 236, 708, 312, 21, 69, 517, 25, 137, 265, 81, 529, 193, 321, 385, 769, 162, 290, 546, 194, 322, 578, 386, 642, 770, 108, 52, 84, 164, 548, 196, 580, 644, 56, 88, 280, 168, 296, 200, 392, 304, 560, 784, 704, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_451, vertices_565, vertices_85, vertices_837, vertices_217, vertices_793, vertices_393, vertices_678, vertices_426, vertices_818, vertices_706, vertices_834, vertices_124, vertices_236, vertices_708, vertices_312] (by decide +kernel)
  polygons := literalFinset [vertices_21, vertices_69, vertices_517, vertices_25, vertices_137, vertices_265, vertices_81, vertices_529, vertices_193, vertices_321, vertices_385, vertices_769, vertices_162, vertices_290, vertices_546, vertices_194, vertices_322, vertices_578, vertices_386, vertices_642, vertices_770, vertices_108, vertices_52, vertices_84, vertices_164, vertices_548, vertices_196, vertices_580, vertices_644, vertices_56, vertices_88, vertices_280, vertices_168, vertices_296, vertices_200, vertices_392, vertices_304, vertices_560, vertices_784, vertices_704, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_451), (false, vertices_565), (false, vertices_85), (false, vertices_837), (false, vertices_217), (false, vertices_793), (false, vertices_393), (true, vertices_162), (true, vertices_290), (true, vertices_546), (true, vertices_578), (true, vertices_642), (true, vertices_770), (true, vertices_108), (true, vertices_164), (true, vertices_196), (true, vertices_644), (true, vertices_56), (true, vertices_168), (true, vertices_296), (true, vertices_304), (true, vertices_704)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 16 18 22 25 26 27 28 29 30
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_451) then 17 else
  if p.val = (false, vertices_565) then 19 else
  if p.val = (false, vertices_85) then 0 else
  if p.val = (false, vertices_837) then 20 else
  if p.val = (false, vertices_217) then 23 else
  if p.val = (false, vertices_793) then 24 else
  if p.val = (false, vertices_393) then 1 else
  if p.val = (true, vertices_162) then 2 else
  if p.val = (true, vertices_290) then 3 else
  if p.val = (true, vertices_546) then 4 else
  if p.val = (true, vertices_578) then 5 else
  if p.val = (true, vertices_642) then 6 else
  if p.val = (true, vertices_770) then 7 else
  if p.val = (true, vertices_108) then 21 else
  if p.val = (true, vertices_164) then 8 else
  if p.val = (true, vertices_196) then 9 else
  if p.val = (true, vertices_644) then 10 else
  if p.val = (true, vertices_56) then 11 else
  if p.val = (true, vertices_168) then 12 else
  if p.val = (true, vertices_296) then 13 else
  if p.val = (true, vertices_304) then 14 else
  if p.val = (true, vertices_704) then 15 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_85), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_393), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_162), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_290), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_546), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_578), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_642), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_770), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_164), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_196), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_644), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_56), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_168), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_296), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_304), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_704), by decide +kernel⟩
  | 16 => Sum.inl 0
  | 17 => Sum.inr ⟨(false, vertices_451), by decide +kernel⟩
  | 18 => Sum.inl 1
  | 19 => Sum.inr ⟨(false, vertices_565), by decide +kernel⟩
  | 20 => Sum.inr ⟨(false, vertices_837), by decide +kernel⟩
  | 21 => Sum.inr ⟨(true, vertices_108), by decide +kernel⟩
  | 22 => Sum.inl 2
  | 23 => Sum.inr ⟨(false, vertices_217), by decide +kernel⟩
  | 24 => Sum.inr ⟨(false, vertices_793), by decide +kernel⟩
  | 25 => Sum.inl 3
  | 26 => Sum.inl 4
  | 27 => Sum.inl 5
  | 28 => Sum.inl 6
  | 29 => Sum.inl 7
  | 30 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 1 2 4 5 108
cert_row_4 1 0 1 4 6 8 678 162 1
cert_row_4 2 0 2 4 6 7 426 162 1
cert_row_4 3 0 3 4 7 8 818 290 1
cert_rows
cert_pivot_2 5 1 2 0
cert_heightProof 4
cert_coverFacet 0 678
cert_cover_5 0 1 0 1 4 6 162 678 1
cert_coverFacet 1 426
cert_cover_5 1 2 0 2 4 6 162 426 1
cert_coverFacet 2 818
cert_cover_5 2 3 0 3 4 7 290 818 1
cert_coverFacet 3 706
cert_cover_2 3 5 0 6 8 194 706 3
cert_coverFacet 4 834
cert_cover_2 4 5 0 7 8 322 834 3
cert_coverFacet 5 124
cert_cover_5 5 0 1 2 3 4 108 124 2
cert_coverFacet 6 236
cert_cover_5 6 0 1 2 4 6 108 236 3
cert_coverFacet 7 708
cert_cover_2 7 5 1 6 8 196 708 3
cert_coverFacet 8 312
cert_cover_2 8 3 2 4 7 56 312 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0785

end
end BundlePart14

section BundlePart15
/- Source: ProjectionCertificates/R_m16e10q1_0786.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0786

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [27, 331, 563, 771, 453, 217, 913, 302, 58, 930, 572, 604, 332, 740, 420, 720, 11, 19, 259, 515, 25, 73, 145, 529, 193, 321, 385, 769, 26, 42, 266, 50, 290, 546, 770, 540, 44, 76, 268, 164, 292, 548, 196, 324, 580, 388, 56, 88, 328, 560, 208, 592, 656, 416, 672, 704, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_27, vertices_331, vertices_563, vertices_771, vertices_453, vertices_217, vertices_913, vertices_302, vertices_58, vertices_930, vertices_572, vertices_604, vertices_332, vertices_740, vertices_420, vertices_720] (by decide +kernel)
  polygons := literalFinset [vertices_11, vertices_19, vertices_259, vertices_515, vertices_25, vertices_73, vertices_145, vertices_529, vertices_193, vertices_321, vertices_385, vertices_769, vertices_26, vertices_42, vertices_266, vertices_50, vertices_290, vertices_546, vertices_770, vertices_540, vertices_44, vertices_76, vertices_268, vertices_164, vertices_292, vertices_548, vertices_196, vertices_324, vertices_580, vertices_388, vertices_56, vertices_88, vertices_328, vertices_560, vertices_208, vertices_592, vertices_656, vertices_416, vertices_672, vertices_704, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_27), (false, vertices_331), (false, vertices_563), (false, vertices_771), (false, vertices_453), (false, vertices_217), (false, vertices_913), (true, vertices_42), (true, vertices_290), (true, vertices_540), (true, vertices_44), (true, vertices_76), (true, vertices_268), (true, vertices_164), (true, vertices_292), (true, vertices_548), (true, vertices_580), (true, vertices_56), (true, vertices_592), (true, vertices_416), (true, vertices_672), (true, vertices_704)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 16 19 22 24 26 27 28 29 30
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_27) then 0 else
  if p.val = (false, vertices_331) then 17 else
  if p.val = (false, vertices_563) then 18 else
  if p.val = (false, vertices_771) then 1 else
  if p.val = (false, vertices_453) then 20 else
  if p.val = (false, vertices_217) then 23 else
  if p.val = (false, vertices_913) then 25 else
  if p.val = (true, vertices_42) then 2 else
  if p.val = (true, vertices_290) then 3 else
  if p.val = (true, vertices_540) then 21 else
  if p.val = (true, vertices_44) then 4 else
  if p.val = (true, vertices_76) then 5 else
  if p.val = (true, vertices_268) then 6 else
  if p.val = (true, vertices_164) then 7 else
  if p.val = (true, vertices_292) then 8 else
  if p.val = (true, vertices_548) then 9 else
  if p.val = (true, vertices_580) then 10 else
  if p.val = (true, vertices_56) then 11 else
  if p.val = (true, vertices_592) then 12 else
  if p.val = (true, vertices_416) then 13 else
  if p.val = (true, vertices_672) then 14 else
  if p.val = (true, vertices_704) then 15 else
  0
cert_priority
cert_nodeAtPriority_61 0 27 1 771 42 290 44 76 268 164 292 548 580 56 592 416 672 704 331 563 453 540 217 913
cert_priority_injective
cert_incidenceProof
cert_row_2 0 1 2 3 8 540
cert_row_4 1 0 1 2 4 7 302 42 1
cert_row_4 2 0 4 6 7 8 930 290 2
cert_row_4 3 1 4 5 6 8 740 164 2
cert_rows
cert_pivot_2 3 2 0 1
cert_heightProof 4
cert_coverFacet 0 302
cert_cover_5 0 1 0 1 2 4 42 302 1
cert_coverFacet 1 58
cert_cover_2 1 2 0 3 4 26 58 3
cert_coverFacet 2 930
cert_cover_5 2 2 0 4 6 7 290 930 2
cert_coverFacet 3 572
cert_cover_5 3 0 1 2 3 4 540 572 3
cert_coverFacet 4 604
cert_cover_5 4 0 1 2 3 5 540 604 3
cert_coverFacet 5 332
cert_cover_2 5 2 1 5 7 76 332 3
cert_coverFacet 6 740
cert_cover_5 6 3 1 4 5 6 164 740 2
cert_coverFacet 7 420
cert_cover_2 7 4 1 6 7 164 420 3
cert_coverFacet 8 720
cert_cover_2 8 5 3 6 8 208 720 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0786

end
end BundlePart15

section BundlePart16
/- Source: ProjectionCertificates/R_m16e10q1_0787.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0787

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [551, 283, 539, 355, 625, 465, 654, 270, 294, 220, 284, 404, 932, 600, 744, 480, 27, 35, 259, 515, 81, 273, 529, 97, 545, 321, 14, 38, 262, 518, 266, 522, 290, 28, 140, 268, 148, 276, 292, 548, 388, 644, 88, 280, 536, 200, 584, 648, 208, 592, 400, 224, 352, 608, 416, 672, 448]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_551, vertices_283, vertices_539, vertices_355, vertices_625, vertices_465, vertices_654, vertices_270, vertices_294, vertices_220, vertices_284, vertices_404, vertices_932, vertices_600, vertices_744, vertices_480] (by decide +kernel)
  polygons := literalFinset [vertices_27, vertices_35, vertices_259, vertices_515, vertices_81, vertices_273, vertices_529, vertices_97, vertices_545, vertices_321, vertices_14, vertices_38, vertices_262, vertices_518, vertices_266, vertices_522, vertices_290, vertices_28, vertices_140, vertices_268, vertices_148, vertices_276, vertices_292, vertices_548, vertices_388, vertices_644, vertices_88, vertices_280, vertices_536, vertices_200, vertices_584, vertices_648, vertices_208, vertices_592, vertices_400, vertices_224, vertices_352, vertices_608, vertices_416, vertices_672, vertices_448] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_551), (false, vertices_283), (false, vertices_539), (false, vertices_355), (false, vertices_625), (false, vertices_465), (true, vertices_14), (true, vertices_262), (true, vertices_28), (true, vertices_140), (true, vertices_268), (true, vertices_148), (true, vertices_276), (true, vertices_292), (true, vertices_388), (true, vertices_644), (true, vertices_88), (true, vertices_200), (true, vertices_584), (true, vertices_648), (true, vertices_224), (true, vertices_416), (true, vertices_672)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 19 17 23 24 27 28 29 30 31
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_551) then 18 else
  if p.val = (false, vertices_283) then 20 else
  if p.val = (false, vertices_539) then 21 else
  if p.val = (false, vertices_355) then 22 else
  if p.val = (false, vertices_625) then 25 else
  if p.val = (false, vertices_465) then 26 else
  if p.val = (true, vertices_14) then 0 else
  if p.val = (true, vertices_262) then 1 else
  if p.val = (true, vertices_28) then 2 else
  if p.val = (true, vertices_140) then 3 else
  if p.val = (true, vertices_268) then 4 else
  if p.val = (true, vertices_148) then 5 else
  if p.val = (true, vertices_276) then 6 else
  if p.val = (true, vertices_292) then 7 else
  if p.val = (true, vertices_388) then 8 else
  if p.val = (true, vertices_644) then 9 else
  if p.val = (true, vertices_88) then 10 else
  if p.val = (true, vertices_200) then 11 else
  if p.val = (true, vertices_584) then 12 else
  if p.val = (true, vertices_648) then 13 else
  if p.val = (true, vertices_224) then 14 else
  if p.val = (true, vertices_416) then 15 else
  if p.val = (true, vertices_672) then 16 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_14), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_262), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_28), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_140), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_268), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_148), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_276), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_292), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_388), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_644), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_88), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_200), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_584), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_648), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_224), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_416), by decide +kernel⟩
  | 16 => Sum.inr ⟨(true, vertices_672), by decide +kernel⟩
  | 17 => Sum.inl 1
  | 18 => Sum.inr ⟨(false, vertices_551), by decide +kernel⟩
  | 19 => Sum.inl 0
  | 20 => Sum.inr ⟨(false, vertices_283), by decide +kernel⟩
  | 21 => Sum.inr ⟨(false, vertices_539), by decide +kernel⟩
  | 22 => Sum.inr ⟨(false, vertices_355), by decide +kernel⟩
  | 23 => Sum.inl 2
  | 24 => Sum.inl 3
  | 25 => Sum.inr ⟨(false, vertices_625), by decide +kernel⟩
  | 26 => Sum.inr ⟨(false, vertices_465), by decide +kernel⟩
  | 27 => Sum.inl 4
  | 28 => Sum.inl 5
  | 29 => Sum.inl 6
  | 30 => Sum.inl 7
  | 31 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 2 6 8 654 14 3
cert_row_4 1 1 2 3 5 6 220 28 3
cert_row_4 2 1 4 6 7 8 932 292 2
cert_row_4 3 2 4 5 6 8 744 200 1
cert_rows
cert_pivot_2 0 3 1 2
cert_heightProof 4
cert_coverFacet 0 654
cert_cover_5 0 0 0 1 2 6 14 654 3
cert_coverFacet 1 270
cert_cover_2 1 1 0 2 7 14 270 3
cert_coverFacet 2 294
cert_cover_2 2 1 0 4 7 38 294 3
cert_coverFacet 3 220
cert_cover_5 3 1 1 2 3 5 28 220 3
cert_coverFacet 4 284
cert_cover_2 4 2 1 3 7 28 284 3
cert_coverFacet 5 404
cert_cover_2 5 3 1 6 7 148 404 3
cert_coverFacet 6 932
cert_cover_5 6 2 1 4 6 7 292 932 2
cert_coverFacet 7 600
cert_cover_2 7 3 2 5 8 88 600 3
cert_coverFacet 8 744
cert_cover_5 8 3 2 4 5 6 200 744 1
cert_coverFacet 9 480
cert_cover_2 9 5 4 6 7 224 480 3
cert_coveringFacets_5
cert_coveringProof
cert_certificate 4 10
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0787

end
end BundlePart16

section BundlePart17
/- Source: ProjectionCertificates/R_m16e10q1_0788.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0788

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [391, 555, 139, 835, 653, 597, 325, 170, 434, 802, 372, 404, 660, 248, 728, 872, 11, 131, 259, 515, 69, 133, 261, 517, 137, 521, 321, 577, 42, 138, 162, 290, 546, 386, 770, 84, 148, 276, 532, 324, 388, 644, 216, 104, 168, 552, 584, 648, 112, 176, 304, 592, 400, 656, 352, 800, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_391, vertices_555, vertices_139, vertices_835, vertices_653, vertices_597, vertices_325, vertices_170, vertices_434, vertices_802, vertices_372, vertices_404, vertices_660, vertices_248, vertices_728, vertices_872] (by decide +kernel)
  polygons := literalFinset [vertices_11, vertices_131, vertices_259, vertices_515, vertices_69, vertices_133, vertices_261, vertices_517, vertices_137, vertices_521, vertices_321, vertices_577, vertices_42, vertices_138, vertices_162, vertices_290, vertices_546, vertices_386, vertices_770, vertices_84, vertices_148, vertices_276, vertices_532, vertices_324, vertices_388, vertices_644, vertices_216, vertices_104, vertices_168, vertices_552, vertices_584, vertices_648, vertices_112, vertices_176, vertices_304, vertices_592, vertices_400, vertices_656, vertices_352, vertices_800, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_391), (false, vertices_555), (false, vertices_139), (false, vertices_835), (false, vertices_653), (false, vertices_597), (false, vertices_325), (true, vertices_162), (true, vertices_290), (true, vertices_148), (true, vertices_276), (true, vertices_216), (true, vertices_104), (true, vertices_168), (true, vertices_584), (true, vertices_112), (true, vertices_176), (true, vertices_304), (true, vertices_400), (true, vertices_656), (true, vertices_352), (true, vertices_800)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 16 20 23 25 26 27 28 29 30
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_391) then 17 else
  if p.val = (false, vertices_555) then 18 else
  if p.val = (false, vertices_139) then 0 else
  if p.val = (false, vertices_835) then 19 else
  if p.val = (false, vertices_653) then 21 else
  if p.val = (false, vertices_597) then 22 else
  if p.val = (false, vertices_325) then 1 else
  if p.val = (true, vertices_162) then 2 else
  if p.val = (true, vertices_290) then 3 else
  if p.val = (true, vertices_148) then 4 else
  if p.val = (true, vertices_276) then 5 else
  if p.val = (true, vertices_216) then 24 else
  if p.val = (true, vertices_104) then 6 else
  if p.val = (true, vertices_168) then 7 else
  if p.val = (true, vertices_584) then 8 else
  if p.val = (true, vertices_112) then 9 else
  if p.val = (true, vertices_176) then 10 else
  if p.val = (true, vertices_304) then 11 else
  if p.val = (true, vertices_400) then 12 else
  if p.val = (true, vertices_656) then 13 else
  if p.val = (true, vertices_352) then 14 else
  if p.val = (true, vertices_800) then 15 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_139), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_325), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_162), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_290), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_148), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_276), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_104), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_168), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_584), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_112), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_176), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_304), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_400), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_656), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_352), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_800), by decide +kernel⟩
  | 16 => Sum.inl 0
  | 17 => Sum.inr ⟨(false, vertices_391), by decide +kernel⟩
  | 18 => Sum.inr ⟨(false, vertices_555), by decide +kernel⟩
  | 19 => Sum.inr ⟨(false, vertices_835), by decide +kernel⟩
  | 20 => Sum.inl 1
  | 21 => Sum.inr ⟨(false, vertices_653), by decide +kernel⟩
  | 22 => Sum.inr ⟨(false, vertices_597), by decide +kernel⟩
  | 23 => Sum.inl 2
  | 24 => Sum.inr ⟨(true, vertices_216), by decide +kernel⟩
  | 25 => Sum.inl 3
  | 26 => Sum.inl 4
  | 27 => Sum.inl 5
  | 28 => Sum.inl 6
  | 29 => Sum.inl 7
  | 30 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 3 4 6 7 434 162 1
cert_row_2 1 2 3 5 6 216
cert_row_4 2 1 3 4 5 7 372 84 2
cert_row_4 3 2 4 5 7 8 872 104 3
cert_rows
cert_pivot_2 0 6 1 2
cert_heightProof 4
cert_coverFacet 0 170
cert_cover_2 0 2 0 4 6 42 170 3
cert_coverFacet 1 434
cert_cover_5 1 0 0 3 4 6 162 434 1
cert_coverFacet 2 802
cert_cover_2 2 4 0 7 8 290 802 3
cert_coverFacet 3 372
cert_cover_5 3 2 1 3 4 5 84 372 2
cert_coverFacet 4 404
cert_cover_2 4 3 1 6 7 148 404 3
cert_coverFacet 5 660
cert_cover_2 5 3 1 6 8 148 660 3
cert_coverFacet 6 248
cert_cover_5 6 1 2 3 4 5 216 248 2
cert_coverFacet 7 728
cert_cover_5 7 1 2 3 5 8 216 728 3
cert_coverFacet 8 872
cert_cover_5 8 3 2 4 5 7 104 872 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0788

end
end BundlePart17

section BundlePart18
/- Source: ProjectionCertificates/R_m16e10q1_0789.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0789

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [675, 341, 789, 709, 569, 217, 169, 358, 426, 466, 610, 706, 812, 612, 408, 792, 277, 69, 517, 25, 41, 137, 81, 529, 161, 545, 193, 641, 98, 162, 290, 546, 194, 322, 578, 386, 642, 100, 292, 548, 324, 580, 772, 152, 280, 536, 168, 296, 552, 392, 776, 208, 336, 400, 784, 608, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_675, vertices_341, vertices_789, vertices_709, vertices_569, vertices_217, vertices_169, vertices_358, vertices_426, vertices_466, vertices_610, vertices_706, vertices_812, vertices_612, vertices_408, vertices_792] (by decide +kernel)
  polygons := literalFinset [vertices_277, vertices_69, vertices_517, vertices_25, vertices_41, vertices_137, vertices_81, vertices_529, vertices_161, vertices_545, vertices_193, vertices_641, vertices_98, vertices_162, vertices_290, vertices_546, vertices_194, vertices_322, vertices_578, vertices_386, vertices_642, vertices_100, vertices_292, vertices_548, vertices_324, vertices_580, vertices_772, vertices_152, vertices_280, vertices_536, vertices_168, vertices_296, vertices_552, vertices_392, vertices_776, vertices_208, vertices_336, vertices_400, vertices_784, vertices_608, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_675), (false, vertices_341), (false, vertices_789), (false, vertices_709), (false, vertices_569), (false, vertices_217), (false, vertices_169), (true, vertices_98), (true, vertices_290), (true, vertices_194), (true, vertices_322), (true, vertices_578), (true, vertices_386), (true, vertices_100), (true, vertices_292), (true, vertices_548), (true, vertices_280), (true, vertices_296), (true, vertices_392), (true, vertices_776), (true, vertices_400), (true, vertices_608)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 16 18 22 25 26 27 28 29 30
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_675) then 17 else
  if p.val = (false, vertices_341) then 19 else
  if p.val = (false, vertices_789) then 20 else
  if p.val = (false, vertices_709) then 21 else
  if p.val = (false, vertices_569) then 23 else
  if p.val = (false, vertices_217) then 24 else
  if p.val = (false, vertices_169) then 0 else
  if p.val = (true, vertices_98) then 1 else
  if p.val = (true, vertices_290) then 2 else
  if p.val = (true, vertices_194) then 3 else
  if p.val = (true, vertices_322) then 4 else
  if p.val = (true, vertices_578) then 5 else
  if p.val = (true, vertices_386) then 6 else
  if p.val = (true, vertices_100) then 7 else
  if p.val = (true, vertices_292) then 8 else
  if p.val = (true, vertices_548) then 9 else
  if p.val = (true, vertices_280) then 10 else
  if p.val = (true, vertices_296) then 11 else
  if p.val = (true, vertices_392) then 12 else
  if p.val = (true, vertices_776) then 13 else
  if p.val = (true, vertices_400) then 14 else
  if p.val = (true, vertices_608) then 15 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_169), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_98), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_290), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_194), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_322), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_578), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_386), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_100), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_292), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_548), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_280), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_296), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_392), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_776), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_400), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_608), by decide +kernel⟩
  | 16 => Sum.inl 0
  | 17 => Sum.inr ⟨(false, vertices_675), by decide +kernel⟩
  | 18 => Sum.inl 1
  | 19 => Sum.inr ⟨(false, vertices_341), by decide +kernel⟩
  | 20 => Sum.inr ⟨(false, vertices_789), by decide +kernel⟩
  | 21 => Sum.inr ⟨(false, vertices_709), by decide +kernel⟩
  | 22 => Sum.inl 2
  | 23 => Sum.inr ⟨(false, vertices_569), by decide +kernel⟩
  | 24 => Sum.inr ⟨(false, vertices_217), by decide +kernel⟩
  | 25 => Sum.inl 3
  | 26 => Sum.inl 4
  | 27 => Sum.inl 5
  | 28 => Sum.inl 6
  | 29 => Sum.inl 7
  | 30 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 3 5 6 7 466 194 1
cert_row_4 1 0 1 4 5 7 358 98 1
cert_row_4 2 0 2 4 6 7 426 162 1
cert_row_4 3 1 2 4 7 8 812 292 1
cert_rows
cert_pivot_2 3 5 0 1
cert_heightProof 4
cert_coverFacet 0 358
cert_cover_5 0 1 0 1 4 5 98 358 1
cert_coverFacet 1 426
cert_cover_5 1 2 0 2 4 6 162 426 1
cert_coverFacet 2 466
cert_cover_5 2 0 0 3 5 6 194 466 1
cert_coverFacet 3 610
cert_cover_2 3 4 0 5 8 98 610 3
cert_coverFacet 4 706
cert_cover_2 4 5 0 6 8 194 706 3
cert_coverFacet 5 812
cert_cover_5 5 3 1 2 4 7 292 812 1
cert_coverFacet 6 612
cert_cover_2 6 4 1 5 8 100 612 3
cert_coverFacet 7 408
cert_cover_2 7 3 2 6 7 152 408 3
cert_coverFacet 8 792
cert_cover_2 8 3 2 7 8 280 792 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0789

end
end BundlePart18

section BundlePart19
/- Source: ProjectionCertificates/R_m16e10q1_0790.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0790

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [835, 309, 597, 325, 57, 665, 809, 454, 234, 618, 434, 802, 716, 404, 660, 184, 21, 69, 261, 25, 41, 521, 49, 529, 289, 321, 577, 769, 106, 162, 290, 546, 194, 322, 578, 386, 770, 148, 276, 532, 196, 324, 580, 388, 644, 56, 152, 168, 552, 200, 584, 648, 176, 304, 400, 656, 800]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_835, vertices_309, vertices_597, vertices_325, vertices_57, vertices_665, vertices_809, vertices_454, vertices_234, vertices_618, vertices_434, vertices_802, vertices_716, vertices_404, vertices_660, vertices_184] (by decide +kernel)
  polygons := literalFinset [vertices_21, vertices_69, vertices_261, vertices_25, vertices_41, vertices_521, vertices_49, vertices_529, vertices_289, vertices_321, vertices_577, vertices_769, vertices_106, vertices_162, vertices_290, vertices_546, vertices_194, vertices_322, vertices_578, vertices_386, vertices_770, vertices_148, vertices_276, vertices_532, vertices_196, vertices_324, vertices_580, vertices_388, vertices_644, vertices_56, vertices_152, vertices_168, vertices_552, vertices_200, vertices_584, vertices_648, vertices_176, vertices_304, vertices_400, vertices_656, vertices_800] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_835), (false, vertices_309), (false, vertices_597), (false, vertices_325), (false, vertices_57), (false, vertices_665), (false, vertices_809), (true, vertices_106), (true, vertices_162), (true, vertices_290), (true, vertices_546), (true, vertices_194), (true, vertices_386), (true, vertices_148), (true, vertices_196), (true, vertices_388), (true, vertices_644), (true, vertices_168), (true, vertices_200), (true, vertices_584), (true, vertices_176), (true, vertices_400)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 16 19 22 25 26 27 28 29 30
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_835) then 17 else
  if p.val = (false, vertices_309) then 20 else
  if p.val = (false, vertices_597) then 21 else
  if p.val = (false, vertices_325) then 0 else
  if p.val = (false, vertices_57) then 1 else
  if p.val = (false, vertices_665) then 23 else
  if p.val = (false, vertices_809) then 24 else
  if p.val = (true, vertices_106) then 18 else
  if p.val = (true, vertices_162) then 2 else
  if p.val = (true, vertices_290) then 3 else
  if p.val = (true, vertices_546) then 4 else
  if p.val = (true, vertices_194) then 5 else
  if p.val = (true, vertices_386) then 6 else
  if p.val = (true, vertices_148) then 7 else
  if p.val = (true, vertices_196) then 8 else
  if p.val = (true, vertices_388) then 9 else
  if p.val = (true, vertices_644) then 10 else
  if p.val = (true, vertices_168) then 11 else
  if p.val = (true, vertices_200) then 12 else
  if p.val = (true, vertices_584) then 13 else
  if p.val = (true, vertices_176) then 14 else
  if p.val = (true, vertices_400) then 15 else
  0
cert_priority
cert_nodeAtPriority_39 0 325 1 57 162 290 546 194 386 148 196 388 644 168 200 584 176 400 835 106 309 597 665 809
cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 3 4 6 7 434 162 1
cert_row_2 1 0 2 4 5 106
cert_row_4 2 0 1 5 6 7 454 194 1
cert_row_4 3 1 2 5 6 8 716 196 1
cert_rows
cert_pivot_2 3 4 0 1
cert_heightProof 4
cert_coverFacet 0 454
cert_cover_5 0 2 0 1 5 6 194 454 1
cert_coverFacet 1 234
cert_cover_5 1 1 0 2 4 6 106 234 3
cert_coverFacet 2 618
cert_cover_5 2 1 0 2 4 8 106 618 3
cert_coverFacet 3 434
cert_cover_5 3 0 0 3 4 6 162 434 1
cert_coverFacet 4 802
cert_cover_2 4 4 0 7 8 290 802 3
cert_coverFacet 5 716
cert_cover_5 5 3 1 2 5 6 196 716 1
cert_coverFacet 6 404
cert_cover_2 6 3 1 6 7 148 404 3
cert_coverFacet 7 660
cert_cover_2 7 3 1 6 8 148 660 3
cert_coverFacet 8 184
cert_cover_2 8 3 2 4 6 56 184 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0790

end
end BundlePart19

section BundlePart20
/- Source: ProjectionCertificates/R_m16e10q1_0791.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0791

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [295, 551, 331, 579, 397, 709, 217, 370, 738, 820, 900, 696, 344, 792, 904, 240, 39, 67, 259, 515, 133, 261, 517, 73, 137, 265, 193, 577, 98, 290, 546, 322, 578, 292, 548, 388, 644, 772, 88, 152, 280, 536, 328, 392, 648, 776, 112, 176, 304, 560, 208, 336, 784, 224, 672, 704, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_295, vertices_551, vertices_331, vertices_579, vertices_397, vertices_709, vertices_217, vertices_370, vertices_738, vertices_820, vertices_900, vertices_696, vertices_344, vertices_792, vertices_904, vertices_240] (by decide +kernel)
  polygons := literalFinset [vertices_39, vertices_67, vertices_259, vertices_515, vertices_133, vertices_261, vertices_517, vertices_73, vertices_137, vertices_265, vertices_193, vertices_577, vertices_98, vertices_290, vertices_546, vertices_322, vertices_578, vertices_292, vertices_548, vertices_388, vertices_644, vertices_772, vertices_88, vertices_152, vertices_280, vertices_536, vertices_328, vertices_392, vertices_648, vertices_776, vertices_112, vertices_176, vertices_304, vertices_560, vertices_208, vertices_336, vertices_784, vertices_224, vertices_672, vertices_704, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_295), (false, vertices_551), (false, vertices_331), (false, vertices_579), (false, vertices_397), (false, vertices_709), (false, vertices_217), (true, vertices_98), (true, vertices_772), (true, vertices_280), (true, vertices_536), (true, vertices_648), (true, vertices_776), (true, vertices_112), (true, vertices_176), (true, vertices_304), (true, vertices_560), (true, vertices_336), (true, vertices_784), (true, vertices_224), (true, vertices_672), (true, vertices_896)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 16 20 23 25 26 27 28 29 30
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_295) then 17 else
  if p.val = (false, vertices_551) then 18 else
  if p.val = (false, vertices_331) then 19 else
  if p.val = (false, vertices_579) then 0 else
  if p.val = (false, vertices_397) then 21 else
  if p.val = (false, vertices_709) then 22 else
  if p.val = (false, vertices_217) then 24 else
  if p.val = (true, vertices_98) then 1 else
  if p.val = (true, vertices_772) then 2 else
  if p.val = (true, vertices_280) then 3 else
  if p.val = (true, vertices_536) then 4 else
  if p.val = (true, vertices_648) then 5 else
  if p.val = (true, vertices_776) then 6 else
  if p.val = (true, vertices_112) then 7 else
  if p.val = (true, vertices_176) then 8 else
  if p.val = (true, vertices_304) then 9 else
  if p.val = (true, vertices_560) then 10 else
  if p.val = (true, vertices_336) then 11 else
  if p.val = (true, vertices_784) then 12 else
  if p.val = (true, vertices_224) then 13 else
  if p.val = (true, vertices_672) then 14 else
  if p.val = (true, vertices_896) then 15 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_579), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_98), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_772), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_280), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_536), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_648), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_776), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_112), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_176), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_304), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_560), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_336), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_784), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_224), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_672), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_896), by decide +kernel⟩
  | 16 => Sum.inl 0
  | 17 => Sum.inr ⟨(false, vertices_295), by decide +kernel⟩
  | 18 => Sum.inr ⟨(false, vertices_551), by decide +kernel⟩
  | 19 => Sum.inr ⟨(false, vertices_331), by decide +kernel⟩
  | 20 => Sum.inl 1
  | 21 => Sum.inr ⟨(false, vertices_397), by decide +kernel⟩
  | 22 => Sum.inr ⟨(false, vertices_709), by decide +kernel⟩
  | 23 => Sum.inl 2
  | 24 => Sum.inr ⟨(false, vertices_217), by decide +kernel⟩
  | 25 => Sum.inl 3
  | 26 => Sum.inl 4
  | 27 => Sum.inl 5
  | 28 => Sum.inl 6
  | 29 => Sum.inl 7
  | 30 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 1 3 4 7 8 820 292 1
cert_row_4 1 0 3 4 5 7 370 98 1
cert_row_4 2 0 4 5 6 8 738 98 3
cert_row_4 3 2 3 4 6 8 696 152 2
cert_rows
cert_pivot_2 1 7 0 2
cert_heightProof 4
cert_coverFacet 0 370
cert_cover_5 0 1 0 3 4 5 98 370 1
cert_coverFacet 1 738
cert_cover_5 1 2 0 4 5 6 98 738 3
cert_coverFacet 2 820
cert_cover_5 2 0 1 3 4 7 292 820 1
cert_coverFacet 3 900
cert_cover_2 3 6 1 7 8 388 900 3
cert_coverFacet 4 696
cert_cover_5 4 3 2 3 4 6 152 696 2
cert_coverFacet 5 344
cert_cover_2 5 3 2 5 7 88 344 3
cert_coverFacet 6 792
cert_cover_2 6 3 2 7 8 280 792 3
cert_coverFacet 7 904
cert_cover_2 7 6 2 7 8 392 904 3
cert_coverFacet 8 240
cert_cover_2 8 4 3 5 6 112 240 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0791

end
end BundlePart20

section BundlePart21
/- Source: ProjectionCertificates/R_m16e10q1_0792.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0792

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [331, 787, 611, 565, 433, 353, 206, 650, 778, 706, 364, 428, 180, 724, 612, 920, 67, 259, 515, 49, 273, 529, 97, 289, 545, 321, 74, 138, 266, 522, 194, 578, 642, 770, 300, 76, 140, 52, 148, 532, 100, 164, 548, 196, 580, 328, 392, 648, 776, 176, 400, 656, 784, 352, 608, 416, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_331, vertices_787, vertices_611, vertices_565, vertices_433, vertices_353, vertices_206, vertices_650, vertices_778, vertices_706, vertices_364, vertices_428, vertices_180, vertices_724, vertices_612, vertices_920] (by decide +kernel)
  polygons := literalFinset [vertices_67, vertices_259, vertices_515, vertices_49, vertices_273, vertices_529, vertices_97, vertices_289, vertices_545, vertices_321, vertices_74, vertices_138, vertices_266, vertices_522, vertices_194, vertices_578, vertices_642, vertices_770, vertices_300, vertices_76, vertices_140, vertices_52, vertices_148, vertices_532, vertices_100, vertices_164, vertices_548, vertices_196, vertices_580, vertices_328, vertices_392, vertices_648, vertices_776, vertices_176, vertices_400, vertices_656, vertices_784, vertices_352, vertices_608, vertices_416, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_331), (false, vertices_787), (false, vertices_611), (false, vertices_565), (false, vertices_433), (false, vertices_353), (true, vertices_138), (true, vertices_522), (true, vertices_194), (true, vertices_642), (true, vertices_300), (true, vertices_76), (true, vertices_140), (true, vertices_148), (true, vertices_100), (true, vertices_164), (true, vertices_196), (true, vertices_580), (true, vertices_392), (true, vertices_648), (true, vertices_776), (true, vertices_656), (true, vertices_704)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 17 21 24 25 27 28 29 30 31
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_331) then 18 else
  if p.val = (false, vertices_787) then 19 else
  if p.val = (false, vertices_611) then 20 else
  if p.val = (false, vertices_565) then 22 else
  if p.val = (false, vertices_433) then 26 else
  if p.val = (false, vertices_353) then 0 else
  if p.val = (true, vertices_138) then 1 else
  if p.val = (true, vertices_522) then 2 else
  if p.val = (true, vertices_194) then 3 else
  if p.val = (true, vertices_642) then 4 else
  if p.val = (true, vertices_300) then 23 else
  if p.val = (true, vertices_76) then 5 else
  if p.val = (true, vertices_140) then 6 else
  if p.val = (true, vertices_148) then 7 else
  if p.val = (true, vertices_100) then 8 else
  if p.val = (true, vertices_164) then 9 else
  if p.val = (true, vertices_196) then 10 else
  if p.val = (true, vertices_580) then 11 else
  if p.val = (true, vertices_392) then 12 else
  if p.val = (true, vertices_648) then 13 else
  if p.val = (true, vertices_776) then 14 else
  if p.val = (true, vertices_656) then 15 else
  if p.val = (true, vertices_704) then 16 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_353), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_138), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_522), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_194), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_642), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_76), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_140), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_148), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_100), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_164), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_196), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_580), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_392), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_648), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_776), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_656), by decide +kernel⟩
  | 16 => Sum.inr ⟨(true, vertices_704), by decide +kernel⟩
  | 17 => Sum.inl 0
  | 18 => Sum.inr ⟨(false, vertices_331), by decide +kernel⟩
  | 19 => Sum.inr ⟨(false, vertices_787), by decide +kernel⟩
  | 20 => Sum.inr ⟨(false, vertices_611), by decide +kernel⟩
  | 21 => Sum.inl 1
  | 22 => Sum.inr ⟨(false, vertices_565), by decide +kernel⟩
  | 23 => Sum.inr ⟨(true, vertices_300), by decide +kernel⟩
  | 24 => Sum.inl 2
  | 25 => Sum.inl 3
  | 26 => Sum.inr ⟨(false, vertices_433), by decide +kernel⟩
  | 27 => Sum.inl 4
  | 28 => Sum.inl 5
  | 29 => Sum.inl 6
  | 30 => Sum.inl 7
  | 31 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 1 2 4 7 300
cert_row_4 1 0 1 2 5 6 206 74 1
cert_row_4 2 1 3 5 6 8 724 148 2
cert_row_4 3 2 3 6 7 8 920 392 1
cert_rows
cert_pivot_2 4 0 1 2
cert_heightProof 4
cert_coverFacet 0 206
cert_cover_5 0 1 0 1 2 5 74 206 1
cert_coverFacet 1 650
cert_cover_2 1 2 0 6 8 138 650 3
cert_coverFacet 2 778
cert_cover_2 2 2 0 7 8 266 778 3
cert_coverFacet 3 706
cert_cover_2 3 5 0 6 8 194 706 3
cert_coverFacet 4 364
cert_cover_5 4 0 1 2 4 5 300 364 3
cert_coverFacet 5 428
cert_cover_5 5 0 1 2 4 6 300 428 3
cert_coverFacet 6 180
cert_cover_2 6 3 1 4 6 52 180 3
cert_coverFacet 7 724
cert_cover_5 7 2 1 3 5 6 148 724 2
cert_coverFacet 8 612
cert_cover_2 8 4 1 5 8 100 612 3
cert_coverFacet 9 920
cert_cover_5 9 3 2 3 6 7 392 920 1
cert_coveringFacets_5
cert_coveringProof
cert_certificate 4 10
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0792

end
end BundlePart21

section BundlePart22
/- Source: ProjectionCertificates/R_m16e10q1_0793.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0793

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [391, 555, 659, 291, 301, 525, 709, 370, 562, 402, 220, 412, 588, 344, 872, 752, 35, 131, 259, 515, 13, 133, 261, 517, 41, 521, 289, 641, 50, 146, 274, 530, 290, 546, 386, 156, 76, 268, 524, 196, 580, 388, 88, 280, 296, 552, 328, 584, 112, 560, 208, 336, 400, 656, 352, 608, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_391, vertices_555, vertices_659, vertices_291, vertices_301, vertices_525, vertices_709, vertices_370, vertices_562, vertices_402, vertices_220, vertices_412, vertices_588, vertices_344, vertices_872, vertices_752] (by decide +kernel)
  polygons := literalFinset [vertices_35, vertices_131, vertices_259, vertices_515, vertices_13, vertices_133, vertices_261, vertices_517, vertices_41, vertices_521, vertices_289, vertices_641, vertices_50, vertices_146, vertices_274, vertices_530, vertices_290, vertices_546, vertices_386, vertices_156, vertices_76, vertices_268, vertices_524, vertices_196, vertices_580, vertices_388, vertices_88, vertices_280, vertices_296, vertices_552, vertices_328, vertices_584, vertices_112, vertices_560, vertices_208, vertices_336, vertices_400, vertices_656, vertices_352, vertices_608, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_391), (false, vertices_555), (false, vertices_659), (false, vertices_291), (false, vertices_301), (false, vertices_525), (false, vertices_709), (true, vertices_50), (true, vertices_274), (true, vertices_156), (true, vertices_76), (true, vertices_88), (true, vertices_280), (true, vertices_328), (true, vertices_584), (true, vertices_112), (true, vertices_560), (true, vertices_208), (true, vertices_336), (true, vertices_400), (true, vertices_352), (true, vertices_608)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 16 20 24 25 26 27 28 29 30
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_391) then 17 else
  if p.val = (false, vertices_555) then 18 else
  if p.val = (false, vertices_659) then 19 else
  if p.val = (false, vertices_291) then 0 else
  if p.val = (false, vertices_301) then 21 else
  if p.val = (false, vertices_525) then 1 else
  if p.val = (false, vertices_709) then 22 else
  if p.val = (true, vertices_50) then 2 else
  if p.val = (true, vertices_274) then 3 else
  if p.val = (true, vertices_156) then 23 else
  if p.val = (true, vertices_76) then 4 else
  if p.val = (true, vertices_88) then 5 else
  if p.val = (true, vertices_280) then 6 else
  if p.val = (true, vertices_328) then 7 else
  if p.val = (true, vertices_584) then 8 else
  if p.val = (true, vertices_112) then 9 else
  if p.val = (true, vertices_560) then 10 else
  if p.val = (true, vertices_208) then 11 else
  if p.val = (true, vertices_336) then 12 else
  if p.val = (true, vertices_400) then 13 else
  if p.val = (true, vertices_352) then 14 else
  if p.val = (true, vertices_608) then 15 else
  0
cert_priority
cert_nodeAtPriority_6 291 525 50 274 76 88 280 328 584 112 560 208 336 400 352 608 391 555 659 301 709 156
cert_priority_injective
cert_incidenceProof
cert_row_2 0 1 2 3 6 156
cert_row_4 1 0 3 4 5 7 370 50 3
cert_row_4 2 2 4 5 7 8 872 296 2
cert_row_4 3 3 4 5 6 8 752 112 3
cert_rows
cert_pivot_2 1 0 2 3
cert_heightProof 4
cert_coverFacet 0 370
cert_cover_5 0 1 0 3 4 5 50 370 3
cert_coverFacet 1 562
cert_cover_2 1 3 0 4 8 50 562 3
cert_coverFacet 2 402
cert_cover_2 2 3 0 6 7 146 402 3
cert_coverFacet 3 220
cert_cover_5 3 0 1 2 3 5 156 220 3
cert_coverFacet 4 412
cert_cover_5 4 0 1 2 3 7 156 412 3
cert_coverFacet 5 588
cert_cover_2 5 2 1 5 8 76 588 3
cert_coverFacet 6 344
cert_cover_2 6 3 2 5 7 88 344 3
cert_coverFacet 7 872
cert_cover_5 7 2 2 4 5 7 296 872 2
cert_coverFacet 8 752
cert_cover_5 8 3 3 4 5 6 112 752 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0793

end
end BundlePart22

section BundlePart23
/- Source: ProjectionCertificates/R_m16e10q1_0794.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0794

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [835, 285, 53, 357, 569, 777, 737, 398, 218, 602, 778, 482, 156, 692, 420, 720, 21, 37, 261, 25, 265, 521, 49, 97, 545, 321, 577, 769, 90, 138, 266, 522, 194, 322, 578, 386, 770, 28, 140, 268, 52, 148, 164, 292, 388, 152, 536, 776, 560, 208, 592, 656, 224, 352, 416, 672, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_835, vertices_285, vertices_53, vertices_357, vertices_569, vertices_777, vertices_737, vertices_398, vertices_218, vertices_602, vertices_778, vertices_482, vertices_156, vertices_692, vertices_420, vertices_720] (by decide +kernel)
  polygons := literalFinset [vertices_21, vertices_37, vertices_261, vertices_25, vertices_265, vertices_521, vertices_49, vertices_97, vertices_545, vertices_321, vertices_577, vertices_769, vertices_90, vertices_138, vertices_266, vertices_522, vertices_194, vertices_322, vertices_578, vertices_386, vertices_770, vertices_28, vertices_140, vertices_268, vertices_52, vertices_148, vertices_164, vertices_292, vertices_388, vertices_152, vertices_536, vertices_776, vertices_560, vertices_208, vertices_592, vertices_656, vertices_224, vertices_352, vertices_416, vertices_672, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_835), (false, vertices_285), (false, vertices_53), (false, vertices_357), (false, vertices_569), (false, vertices_777), (false, vertices_737), (true, vertices_90), (true, vertices_138), (true, vertices_266), (true, vertices_522), (true, vertices_194), (true, vertices_386), (true, vertices_140), (true, vertices_148), (true, vertices_164), (true, vertices_388), (true, vertices_152), (true, vertices_208), (true, vertices_592), (true, vertices_656), (true, vertices_416)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 16 19 22 24 25 27 28 29 30
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_835) then 17 else
  if p.val = (false, vertices_285) then 20 else
  if p.val = (false, vertices_53) then 0 else
  if p.val = (false, vertices_357) then 21 else
  if p.val = (false, vertices_569) then 23 else
  if p.val = (false, vertices_777) then 1 else
  if p.val = (false, vertices_737) then 26 else
  if p.val = (true, vertices_90) then 18 else
  if p.val = (true, vertices_138) then 2 else
  if p.val = (true, vertices_266) then 3 else
  if p.val = (true, vertices_522) then 4 else
  if p.val = (true, vertices_194) then 5 else
  if p.val = (true, vertices_386) then 6 else
  if p.val = (true, vertices_140) then 7 else
  if p.val = (true, vertices_148) then 8 else
  if p.val = (true, vertices_164) then 9 else
  if p.val = (true, vertices_388) then 10 else
  if p.val = (true, vertices_152) then 11 else
  if p.val = (true, vertices_208) then 12 else
  if p.val = (true, vertices_592) then 13 else
  if p.val = (true, vertices_656) then 14 else
  if p.val = (true, vertices_416) then 15 else
  0
cert_priority
cert_nodeAtPriority_24 1 53 0 777 138 266 522 194 386 140 148 164 388 152 208 592 656 416 835 90 285 357 569 737
cert_priority_injective
cert_incidenceProof
cert_row_4 0 1 3 4 6 8 692 52 3
cert_row_2 1 0 2 3 5 90
cert_row_4 2 0 1 2 6 7 398 138 1
cert_row_4 3 0 4 5 6 7 482 194 1
cert_rows
cert_pivot_2 8 3 1 0
cert_heightProof 4
cert_coverFacet 0 398
cert_cover_5 0 2 0 1 2 6 138 398 1
cert_coverFacet 1 218
cert_cover_5 1 1 0 2 3 6 90 218 3
cert_coverFacet 2 602
cert_cover_5 2 1 0 2 3 8 90 602 3
cert_coverFacet 3 778
cert_cover_2 3 2 0 7 8 266 778 3
cert_coverFacet 4 482
cert_cover_5 4 3 0 4 5 6 194 482 1
cert_coverFacet 5 156
cert_cover_2 5 2 1 3 6 28 156 3
cert_coverFacet 6 692
cert_cover_5 6 0 1 3 4 6 52 692 3
cert_coverFacet 7 420
cert_cover_2 7 4 1 6 7 164 420 3
cert_coverFacet 8 720
cert_cover_2 8 5 3 6 8 208 720 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0794

end
end BundlePart23

section BundlePart24
/- Source: ProjectionCertificates/R_m16e10q1_0795.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0795

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [587, 653, 421, 837, 345, 393, 566, 662, 122, 154, 650, 866, 180, 804, 408, 496, 133, 261, 517, 73, 137, 265, 521, 321, 577, 385, 534, 26, 74, 138, 522, 50, 146, 98, 546, 578, 642, 52, 148, 164, 292, 548, 644, 772, 88, 152, 280, 392, 648, 112, 176, 336, 400, 352, 416, 800, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_587, vertices_653, vertices_421, vertices_837, vertices_345, vertices_393, vertices_566, vertices_662, vertices_122, vertices_154, vertices_650, vertices_866, vertices_180, vertices_804, vertices_408, vertices_496] (by decide +kernel)
  polygons := literalFinset [vertices_133, vertices_261, vertices_517, vertices_73, vertices_137, vertices_265, vertices_521, vertices_321, vertices_577, vertices_385, vertices_534, vertices_26, vertices_74, vertices_138, vertices_522, vertices_50, vertices_146, vertices_98, vertices_546, vertices_578, vertices_642, vertices_52, vertices_148, vertices_164, vertices_292, vertices_548, vertices_644, vertices_772, vertices_88, vertices_152, vertices_280, vertices_392, vertices_648, vertices_112, vertices_176, vertices_336, vertices_400, vertices_352, vertices_416, vertices_800, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_587), (false, vertices_653), (false, vertices_421), (false, vertices_837), (false, vertices_345), (false, vertices_393), (true, vertices_534), (true, vertices_26), (true, vertices_138), (true, vertices_50), (true, vertices_146), (true, vertices_98), (true, vertices_546), (true, vertices_642), (true, vertices_52), (true, vertices_148), (true, vertices_548), (true, vertices_152), (true, vertices_112), (true, vertices_176), (true, vertices_400), (true, vertices_352), (true, vertices_800)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 17 20 24 26 27 28 29 30 31
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_587) then 18 else
  if p.val = (false, vertices_653) then 21 else
  if p.val = (false, vertices_421) then 22 else
  if p.val = (false, vertices_837) then 23 else
  if p.val = (false, vertices_345) then 25 else
  if p.val = (false, vertices_393) then 0 else
  if p.val = (true, vertices_534) then 19 else
  if p.val = (true, vertices_26) then 1 else
  if p.val = (true, vertices_138) then 2 else
  if p.val = (true, vertices_50) then 3 else
  if p.val = (true, vertices_146) then 4 else
  if p.val = (true, vertices_98) then 5 else
  if p.val = (true, vertices_546) then 6 else
  if p.val = (true, vertices_642) then 7 else
  if p.val = (true, vertices_52) then 8 else
  if p.val = (true, vertices_148) then 9 else
  if p.val = (true, vertices_548) then 10 else
  if p.val = (true, vertices_152) then 11 else
  if p.val = (true, vertices_112) then 12 else
  if p.val = (true, vertices_176) then 13 else
  if p.val = (true, vertices_400) then 14 else
  if p.val = (true, vertices_352) then 15 else
  if p.val = (true, vertices_800) then 16 else
  0
cert_priority
cert_nodeAtPriority_63 393 26 138 50 146 98 546 642 52 148 548 152 112 176 400 352 800 587 534 653 421 837 345
cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 1 3 8 534
cert_row_4 1 0 2 3 4 5 122 26 3
cert_row_4 2 0 4 5 7 8 866 98 3
cert_row_4 3 3 4 5 6 7 496 112 3
cert_rows
cert_pivot_2 1 2 0 3
cert_heightProof 4
cert_coverFacet 0 566
cert_cover_5 0 0 0 1 3 4 534 566 3
cert_coverFacet 1 662
cert_cover_5 1 0 0 1 3 6 534 662 3
cert_coverFacet 2 122
cert_cover_5 2 1 0 2 3 4 26 122 3
cert_coverFacet 3 154
cert_cover_2 3 2 0 3 6 26 154 3
cert_coverFacet 4 650
cert_cover_2 4 2 0 6 8 138 650 3
cert_coverFacet 5 866
cert_cover_5 5 2 0 4 5 7 98 866 3
cert_coverFacet 6 180
cert_cover_2 6 3 1 4 6 52 180 3
cert_coverFacet 7 804
cert_cover_2 7 4 1 7 8 292 804 3
cert_coverFacet 8 408
cert_cover_2 8 3 2 6 7 152 408 3
cert_coverFacet 9 496
cert_cover_5 9 3 3 4 5 6 112 496 3
cert_coveringFacets_5
cert_coveringProof
cert_certificate 4 10
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0795

end
end BundlePart24

section BundlePart25
/- Source: ProjectionCertificates/R_m16e10q1_0796.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0796

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [155, 555, 163, 613, 601, 465, 225, 806, 394, 778, 482, 668, 908, 372, 596, 404, 11, 35, 131, 25, 521, 81, 145, 97, 161, 545, 193, 577, 138, 266, 522, 162, 290, 546, 386, 770, 652, 84, 148, 276, 532, 100, 292, 548, 580, 388, 772, 152, 536, 392, 776, 336, 592, 400, 224, 352, 448]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_155, vertices_555, vertices_163, vertices_613, vertices_601, vertices_465, vertices_225, vertices_806, vertices_394, vertices_778, vertices_482, vertices_668, vertices_908, vertices_372, vertices_596, vertices_404] (by decide +kernel)
  polygons := literalFinset [vertices_11, vertices_35, vertices_131, vertices_25, vertices_521, vertices_81, vertices_145, vertices_97, vertices_161, vertices_545, vertices_193, vertices_577, vertices_138, vertices_266, vertices_522, vertices_162, vertices_290, vertices_546, vertices_386, vertices_770, vertices_652, vertices_84, vertices_148, vertices_276, vertices_532, vertices_100, vertices_292, vertices_548, vertices_580, vertices_388, vertices_772, vertices_152, vertices_536, vertices_392, vertices_776, vertices_336, vertices_592, vertices_400, vertices_224, vertices_352, vertices_448] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_155), (false, vertices_555), (false, vertices_163), (false, vertices_613), (false, vertices_601), (false, vertices_465), (false, vertices_225), (true, vertices_266), (true, vertices_290), (true, vertices_386), (true, vertices_770), (true, vertices_652), (true, vertices_84), (true, vertices_148), (true, vertices_276), (true, vertices_532), (true, vertices_292), (true, vertices_388), (true, vertices_772), (true, vertices_392), (true, vertices_776), (true, vertices_352)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 16 19 22 24 26 27 28 29 30
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_155) then 17 else
  if p.val = (false, vertices_555) then 18 else
  if p.val = (false, vertices_163) then 0 else
  if p.val = (false, vertices_613) then 20 else
  if p.val = (false, vertices_601) then 23 else
  if p.val = (false, vertices_465) then 25 else
  if p.val = (false, vertices_225) then 1 else
  if p.val = (true, vertices_266) then 2 else
  if p.val = (true, vertices_290) then 3 else
  if p.val = (true, vertices_386) then 4 else
  if p.val = (true, vertices_770) then 5 else
  if p.val = (true, vertices_652) then 21 else
  if p.val = (true, vertices_84) then 6 else
  if p.val = (true, vertices_148) then 7 else
  if p.val = (true, vertices_276) then 8 else
  if p.val = (true, vertices_532) then 9 else
  if p.val = (true, vertices_292) then 10 else
  if p.val = (true, vertices_388) then 11 else
  if p.val = (true, vertices_772) then 12 else
  if p.val = (true, vertices_392) then 13 else
  if p.val = (true, vertices_776) then 14 else
  if p.val = (true, vertices_352) then 15 else
  0
cert_priority
cert_nodeAtPriority_61 0 163 1 225 266 290 386 770 84 148 276 532 292 388 772 392 776 352 155 555 613 652 601 465
cert_priority_injective
cert_incidenceProof
cert_row_2 0 1 2 6 8 652
cert_row_4 1 0 1 4 7 8 806 290 1
cert_row_4 2 0 4 5 6 7 482 162 2
cert_row_4 3 1 3 4 5 7 372 84 2
cert_rows
cert_pivot_2 2 8 0 1
cert_heightProof 4
cert_coverFacet 0 806
cert_cover_5 0 1 0 1 4 7 290 806 1
cert_coverFacet 1 394
cert_cover_2 1 2 0 6 7 138 394 3
cert_coverFacet 2 778
cert_cover_2 2 2 0 7 8 266 778 3
cert_coverFacet 3 482
cert_cover_5 3 2 0 4 5 6 162 482 2
cert_coverFacet 4 668
cert_cover_5 4 0 1 2 3 6 652 668 2
cert_coverFacet 5 908
cert_cover_5 5 0 1 2 6 7 652 908 3
cert_coverFacet 6 372
cert_cover_5 6 3 1 3 4 5 84 372 2
cert_coverFacet 7 596
cert_cover_2 7 3 1 5 8 84 596 3
cert_coverFacet 8 404
cert_cover_2 8 3 1 6 7 148 404 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0796

end
end BundlePart25

section BundlePart26
/- Source: ProjectionCertificates/R_m16e10q1_0797.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0797

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [403, 45, 653, 309, 389, 617, 689, 454, 218, 602, 786, 866, 364, 204, 664, 816, 13, 37, 133, 261, 41, 521, 49, 145, 273, 545, 385, 641, 90, 146, 274, 530, 194, 322, 578, 386, 770, 44, 76, 140, 292, 196, 324, 388, 152, 536, 104, 200, 584, 648, 304, 560, 656, 784, 352, 608, 800]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_403, vertices_45, vertices_653, vertices_309, vertices_389, vertices_617, vertices_689, vertices_454, vertices_218, vertices_602, vertices_786, vertices_866, vertices_364, vertices_204, vertices_664, vertices_816] (by decide +kernel)
  polygons := literalFinset [vertices_13, vertices_37, vertices_133, vertices_261, vertices_41, vertices_521, vertices_49, vertices_145, vertices_273, vertices_545, vertices_385, vertices_641, vertices_90, vertices_146, vertices_274, vertices_530, vertices_194, vertices_322, vertices_578, vertices_386, vertices_770, vertices_44, vertices_76, vertices_140, vertices_292, vertices_196, vertices_324, vertices_388, vertices_152, vertices_536, vertices_104, vertices_200, vertices_584, vertices_648, vertices_304, vertices_560, vertices_656, vertices_784, vertices_352, vertices_608, vertices_800] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_403), (false, vertices_45), (false, vertices_653), (false, vertices_309), (false, vertices_389), (false, vertices_617), (false, vertices_689), (true, vertices_90), (true, vertices_530), (true, vertices_194), (true, vertices_322), (true, vertices_578), (true, vertices_770), (true, vertices_76), (true, vertices_196), (true, vertices_324), (true, vertices_152), (true, vertices_536), (true, vertices_200), (true, vertices_784), (true, vertices_352), (true, vertices_800)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 16 19 22 24 26 27 28 29 30
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_403) then 17 else
  if p.val = (false, vertices_45) then 0 else
  if p.val = (false, vertices_653) then 20 else
  if p.val = (false, vertices_309) then 21 else
  if p.val = (false, vertices_389) then 1 else
  if p.val = (false, vertices_617) then 23 else
  if p.val = (false, vertices_689) then 25 else
  if p.val = (true, vertices_90) then 18 else
  if p.val = (true, vertices_530) then 2 else
  if p.val = (true, vertices_194) then 3 else
  if p.val = (true, vertices_322) then 4 else
  if p.val = (true, vertices_578) then 5 else
  if p.val = (true, vertices_770) then 6 else
  if p.val = (true, vertices_76) then 7 else
  if p.val = (true, vertices_196) then 8 else
  if p.val = (true, vertices_324) then 9 else
  if p.val = (true, vertices_152) then 10 else
  if p.val = (true, vertices_536) then 11 else
  if p.val = (true, vertices_200) then 12 else
  if p.val = (true, vertices_784) then 13 else
  if p.val = (true, vertices_352) then 14 else
  if p.val = (true, vertices_800) then 15 else
  0
cert_priority
cert_nodeAtPriority_50 1 45 0 389 530 194 322 578 770 76 196 324 152 536 200 784 352 800 403 90 653 309 617 689
cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 2 3 5 90
cert_row_4 1 0 1 5 6 7 454 194 1
cert_row_4 2 0 4 5 7 8 866 322 1
cert_row_4 3 1 2 4 5 7 364 44 3
cert_rows
cert_pivot_2 3 6 0 1
cert_heightProof 4
cert_coverFacet 0 454
cert_cover_5 0 1 0 1 5 6 194 454 1
cert_coverFacet 1 218
cert_cover_5 1 0 0 2 3 6 90 218 3
cert_coverFacet 2 602
cert_cover_5 2 0 0 2 3 8 90 602 3
cert_coverFacet 3 786
cert_cover_2 3 3 0 7 8 274 786 3
cert_coverFacet 4 866
cert_cover_5 4 2 0 4 5 7 322 866 1
cert_coverFacet 5 364
cert_cover_5 5 3 1 2 4 5 44 364 3
cert_coverFacet 6 204
cert_cover_2 6 2 1 5 6 76 204 3
cert_coverFacet 7 664
cert_cover_2 7 3 2 6 8 152 664 3
cert_coverFacet 8 816
cert_cover_2 8 4 3 7 8 304 816 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0797

end
end BundlePart26

section BundlePart27
/- Source: ProjectionCertificates/R_m16e10q1_0798.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0798

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [271, 539, 675, 291, 525, 421, 709, 282, 370, 562, 220, 412, 588, 632, 464, 992, 11, 35, 259, 515, 13, 133, 261, 517, 521, 161, 289, 641, 26, 266, 50, 274, 530, 290, 546, 156, 76, 268, 524, 196, 580, 388, 88, 280, 536, 584, 112, 560, 208, 336, 400, 352, 608, 416, 672, 448, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_271, vertices_539, vertices_675, vertices_291, vertices_525, vertices_421, vertices_709, vertices_282, vertices_370, vertices_562, vertices_220, vertices_412, vertices_588, vertices_632, vertices_464, vertices_992] (by decide +kernel)
  polygons := literalFinset [vertices_11, vertices_35, vertices_259, vertices_515, vertices_13, vertices_133, vertices_261, vertices_517, vertices_521, vertices_161, vertices_289, vertices_641, vertices_26, vertices_266, vertices_50, vertices_274, vertices_530, vertices_290, vertices_546, vertices_156, vertices_76, vertices_268, vertices_524, vertices_196, vertices_580, vertices_388, vertices_88, vertices_280, vertices_536, vertices_584, vertices_112, vertices_560, vertices_208, vertices_336, vertices_400, vertices_352, vertices_608, vertices_416, vertices_672, vertices_448, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_271), (false, vertices_539), (false, vertices_675), (false, vertices_291), (false, vertices_525), (false, vertices_421), (false, vertices_709), (true, vertices_50), (true, vertices_274), (true, vertices_156), (true, vertices_76), (true, vertices_88), (true, vertices_280), (true, vertices_584), (true, vertices_112), (true, vertices_560), (true, vertices_208), (true, vertices_336), (true, vertices_400), (true, vertices_352), (true, vertices_608), (true, vertices_448)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 16 22 20 25 26 27 28 29 30
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_271) then 17 else
  if p.val = (false, vertices_539) then 18 else
  if p.val = (false, vertices_675) then 19 else
  if p.val = (false, vertices_291) then 0 else
  if p.val = (false, vertices_525) then 1 else
  if p.val = (false, vertices_421) then 23 else
  if p.val = (false, vertices_709) then 24 else
  if p.val = (true, vertices_50) then 2 else
  if p.val = (true, vertices_274) then 3 else
  if p.val = (true, vertices_156) then 21 else
  if p.val = (true, vertices_76) then 4 else
  if p.val = (true, vertices_88) then 5 else
  if p.val = (true, vertices_280) then 6 else
  if p.val = (true, vertices_584) then 7 else
  if p.val = (true, vertices_112) then 8 else
  if p.val = (true, vertices_560) then 9 else
  if p.val = (true, vertices_208) then 10 else
  if p.val = (true, vertices_336) then 11 else
  if p.val = (true, vertices_400) then 12 else
  if p.val = (true, vertices_352) then 13 else
  if p.val = (true, vertices_608) then 14 else
  if p.val = (true, vertices_448) then 15 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_291), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_525), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_50), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_274), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_76), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_88), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_280), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_584), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_112), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_560), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_208), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_336), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_400), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_352), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_608), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_448), by decide +kernel⟩
  | 16 => Sum.inl 0
  | 17 => Sum.inr ⟨(false, vertices_271), by decide +kernel⟩
  | 18 => Sum.inr ⟨(false, vertices_539), by decide +kernel⟩
  | 19 => Sum.inr ⟨(false, vertices_675), by decide +kernel⟩
  | 20 => Sum.inl 2
  | 21 => Sum.inr ⟨(true, vertices_156), by decide +kernel⟩
  | 22 => Sum.inl 1
  | 23 => Sum.inr ⟨(false, vertices_421), by decide +kernel⟩
  | 24 => Sum.inr ⟨(false, vertices_709), by decide +kernel⟩
  | 25 => Sum.inl 3
  | 26 => Sum.inl 4
  | 27 => Sum.inl 5
  | 28 => Sum.inl 6
  | 29 => Sum.inl 7
  | 30 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 1 2 3 6 156
cert_row_4 1 0 3 4 5 7 370 50 3
cert_row_4 2 2 3 4 5 8 632 88 2
cert_row_4 3 4 5 6 7 8 992 352 2
cert_rows
cert_pivot_2 1 0 2 4
cert_heightProof 4
cert_coverFacet 0 282
cert_cover_2 0 2 0 3 7 26 282 3
cert_coverFacet 1 370
cert_cover_5 1 1 0 3 4 5 50 370 3
cert_coverFacet 2 562
cert_cover_2 2 3 0 4 8 50 562 3
cert_coverFacet 3 220
cert_cover_5 3 0 1 2 3 5 156 220 3
cert_coverFacet 4 412
cert_cover_5 4 0 1 2 3 7 156 412 3
cert_coverFacet 5 588
cert_cover_2 5 2 1 5 8 76 588 3
cert_coverFacet 6 632
cert_cover_5 6 2 2 3 4 5 88 632 2
cert_coverFacet 7 464
cert_cover_2 7 5 3 6 7 208 464 3
cert_coverFacet 8 992
cert_cover_5 8 3 4 5 6 7 352 992 2
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0798

end
end BundlePart27

section BundlePart28
/- Source: ProjectionCertificates/R_m16e10q1_0799.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0799

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [899, 285, 653, 565, 457, 785, 310, 714, 242, 594, 786, 418, 364, 620, 624, 480, 13, 21, 517, 137, 265, 273, 529, 385, 641, 769, 50, 82, 274, 530, 162, 290, 194, 578, 386, 642, 770, 108, 268, 524, 52, 276, 292, 548, 200, 328, 584, 648, 112, 560, 592, 784, 224, 352, 608, 416, 448]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_899, vertices_285, vertices_653, vertices_565, vertices_457, vertices_785, vertices_310, vertices_714, vertices_242, vertices_594, vertices_786, vertices_418, vertices_364, vertices_620, vertices_624, vertices_480] (by decide +kernel)
  polygons := literalFinset [vertices_13, vertices_21, vertices_517, vertices_137, vertices_265, vertices_273, vertices_529, vertices_385, vertices_641, vertices_769, vertices_50, vertices_82, vertices_274, vertices_530, vertices_162, vertices_290, vertices_194, vertices_578, vertices_386, vertices_642, vertices_770, vertices_108, vertices_268, vertices_524, vertices_52, vertices_276, vertices_292, vertices_548, vertices_200, vertices_328, vertices_584, vertices_648, vertices_112, vertices_560, vertices_592, vertices_784, vertices_224, vertices_352, vertices_608, vertices_416, vertices_448] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_899), (false, vertices_285), (false, vertices_653), (false, vertices_565), (false, vertices_457), (false, vertices_785), (true, vertices_50), (true, vertices_82), (true, vertices_274), (true, vertices_530), (true, vertices_162), (true, vertices_290), (true, vertices_194), (true, vertices_578), (true, vertices_108), (true, vertices_292), (true, vertices_584), (true, vertices_112), (true, vertices_592), (true, vertices_224), (true, vertices_352), (true, vertices_608), (true, vertices_416)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 17 22 25 19 27 28 29 30 31
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_899) then 18 else
  if p.val = (false, vertices_285) then 20 else
  if p.val = (false, vertices_653) then 23 else
  if p.val = (false, vertices_565) then 21 else
  if p.val = (false, vertices_457) then 26 else
  if p.val = (false, vertices_785) then 0 else
  if p.val = (true, vertices_50) then 1 else
  if p.val = (true, vertices_82) then 2 else
  if p.val = (true, vertices_274) then 3 else
  if p.val = (true, vertices_530) then 4 else
  if p.val = (true, vertices_162) then 5 else
  if p.val = (true, vertices_290) then 6 else
  if p.val = (true, vertices_194) then 7 else
  if p.val = (true, vertices_578) then 8 else
  if p.val = (true, vertices_108) then 24 else
  if p.val = (true, vertices_292) then 9 else
  if p.val = (true, vertices_584) then 10 else
  if p.val = (true, vertices_112) then 11 else
  if p.val = (true, vertices_592) then 12 else
  if p.val = (true, vertices_224) then 13 else
  if p.val = (true, vertices_352) then 14 else
  if p.val = (true, vertices_608) then 15 else
  if p.val = (true, vertices_416) then 16 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_785), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_50), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_82), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_274), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_530), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_162), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_290), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_194), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_578), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_292), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_584), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_112), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_592), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_224), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_352), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_608), by decide +kernel⟩
  | 16 => Sum.inr ⟨(true, vertices_416), by decide +kernel⟩
  | 17 => Sum.inl 0
  | 18 => Sum.inr ⟨(false, vertices_899), by decide +kernel⟩
  | 19 => Sum.inl 3
  | 20 => Sum.inr ⟨(false, vertices_285), by decide +kernel⟩
  | 21 => Sum.inr ⟨(false, vertices_565), by decide +kernel⟩
  | 22 => Sum.inl 1
  | 23 => Sum.inr ⟨(false, vertices_653), by decide +kernel⟩
  | 24 => Sum.inr ⟨(true, vertices_108), by decide +kernel⟩
  | 25 => Sum.inl 2
  | 26 => Sum.inr ⟨(false, vertices_457), by decide +kernel⟩
  | 27 => Sum.inl 4
  | 28 => Sum.inl 5
  | 29 => Sum.inl 6
  | 30 => Sum.inl 7
  | 31 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 3 4 7 310 50 1
cert_row_2 1 1 2 4 5 108
cert_row_4 2 0 2 5 6 8 714 194 1
cert_row_4 3 0 3 4 5 6 242 50 3
cert_rows
cert_pivot_2 7 1 2 0
cert_heightProof 4
cert_coverFacet 0 310
cert_cover_5 0 0 0 1 3 4 50 310 1
cert_coverFacet 1 714
cert_cover_5 1 2 0 2 5 6 194 714 1
cert_coverFacet 2 242
cert_cover_5 2 3 0 3 4 5 50 242 3
cert_coverFacet 3 594
cert_cover_2 3 3 0 5 8 82 594 3
cert_coverFacet 4 786
cert_cover_2 4 3 0 7 8 274 786 3
cert_coverFacet 5 418
cert_cover_2 5 4 0 6 7 162 418 3
cert_coverFacet 6 364
cert_cover_5 6 1 1 2 4 7 108 364 3
cert_coverFacet 7 620
cert_cover_5 7 1 1 2 4 8 108 620 3
cert_coverFacet 8 624
cert_cover_2 8 4 3 5 8 112 624 3
cert_coverFacet 9 480
cert_cover_2 9 5 4 6 7 224 480 3
cert_coveringFacets_5
cert_coveringProof
cert_certificate 4 10
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0799

end
end BundlePart28

section BundlePart29
/- Source: ProjectionCertificates/R_m16e10q1_0800.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0800

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [327, 307, 563, 707, 681, 481, 286, 598, 188, 556, 332, 588, 564, 408, 968, 432, 51, 67, 259, 515, 161, 289, 545, 193, 321, 641, 22, 70, 262, 274, 530, 578, 28, 44, 76, 268, 524, 52, 532, 548, 324, 580, 152, 280, 168, 552, 328, 584, 392, 648, 176, 304, 560, 400, 416, 448, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_327, vertices_307, vertices_563, vertices_707, vertices_681, vertices_481, vertices_286, vertices_598, vertices_188, vertices_556, vertices_332, vertices_588, vertices_564, vertices_408, vertices_968, vertices_432] (by decide +kernel)
  polygons := literalFinset [vertices_51, vertices_67, vertices_259, vertices_515, vertices_161, vertices_289, vertices_545, vertices_193, vertices_321, vertices_641, vertices_22, vertices_70, vertices_262, vertices_274, vertices_530, vertices_578, vertices_28, vertices_44, vertices_76, vertices_268, vertices_524, vertices_52, vertices_532, vertices_548, vertices_324, vertices_580, vertices_152, vertices_280, vertices_168, vertices_552, vertices_328, vertices_584, vertices_392, vertices_648, vertices_176, vertices_304, vertices_560, vertices_400, vertices_416, vertices_448, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_327), (false, vertices_307), (false, vertices_563), (false, vertices_707), (false, vertices_681), (false, vertices_481), (true, vertices_22), (true, vertices_28), (true, vertices_44), (true, vertices_76), (true, vertices_268), (true, vertices_524), (true, vertices_52), (true, vertices_532), (true, vertices_548), (true, vertices_580), (true, vertices_152), (true, vertices_280), (true, vertices_328), (true, vertices_584), (true, vertices_392), (true, vertices_176), (true, vertices_400)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 19 17 23 25 26 28 29 30 31
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_327) then 18 else
  if p.val = (false, vertices_307) then 20 else
  if p.val = (false, vertices_563) then 21 else
  if p.val = (false, vertices_707) then 22 else
  if p.val = (false, vertices_681) then 24 else
  if p.val = (false, vertices_481) then 27 else
  if p.val = (true, vertices_22) then 0 else
  if p.val = (true, vertices_28) then 1 else
  if p.val = (true, vertices_44) then 2 else
  if p.val = (true, vertices_76) then 3 else
  if p.val = (true, vertices_268) then 4 else
  if p.val = (true, vertices_524) then 5 else
  if p.val = (true, vertices_52) then 6 else
  if p.val = (true, vertices_532) then 7 else
  if p.val = (true, vertices_548) then 8 else
  if p.val = (true, vertices_580) then 9 else
  if p.val = (true, vertices_152) then 10 else
  if p.val = (true, vertices_280) then 11 else
  if p.val = (true, vertices_328) then 12 else
  if p.val = (true, vertices_584) then 13 else
  if p.val = (true, vertices_392) then 14 else
  if p.val = (true, vertices_176) then 15 else
  if p.val = (true, vertices_400) then 16 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_22), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_28), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_44), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_76), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_268), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_524), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_52), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_532), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_548), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_580), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_152), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_280), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_328), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_584), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_392), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_176), by decide +kernel⟩
  | 16 => Sum.inr ⟨(true, vertices_400), by decide +kernel⟩
  | 17 => Sum.inl 1
  | 18 => Sum.inr ⟨(false, vertices_327), by decide +kernel⟩
  | 19 => Sum.inl 0
  | 20 => Sum.inr ⟨(false, vertices_307), by decide +kernel⟩
  | 21 => Sum.inr ⟨(false, vertices_563), by decide +kernel⟩
  | 22 => Sum.inr ⟨(false, vertices_707), by decide +kernel⟩
  | 23 => Sum.inl 2
  | 24 => Sum.inr ⟨(false, vertices_681), by decide +kernel⟩
  | 25 => Sum.inl 3
  | 26 => Sum.inl 4
  | 27 => Sum.inr ⟨(false, vertices_481), by decide +kernel⟩
  | 28 => Sum.inl 5
  | 29 => Sum.inl 6
  | 30 => Sum.inl 7
  | 31 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 1 2 3 4 6 188 28 3
cert_row_4 1 2 5 6 7 8 968 328 2
cert_row_4 2 0 1 2 3 7 286 22 2
cert_row_4 3 0 1 3 5 8 598 22 3
cert_rows
cert_pivot_2 4 6 2 0
cert_heightProof 4
cert_coverFacet 0 286
cert_cover_5 0 2 0 1 2 3 22 286 2
cert_coverFacet 1 598
cert_cover_5 1 3 0 1 3 5 22 598 3
cert_coverFacet 2 188
cert_cover_5 2 0 1 2 3 4 28 188 3
cert_coverFacet 3 556
cert_cover_2 3 2 1 4 8 44 556 3
cert_coverFacet 4 332
cert_cover_2 4 2 1 5 7 76 332 3
cert_coverFacet 5 588
cert_cover_2 5 2 1 5 8 76 588 3
cert_coverFacet 6 564
cert_cover_2 6 3 1 4 8 52 564 3
cert_coverFacet 7 408
cert_cover_2 7 3 2 6 7 152 408 3
cert_coverFacet 8 968
cert_cover_5 8 1 2 5 6 7 328 968 2
cert_coverFacet 9 432
cert_cover_2 9 4 3 6 7 176 432 3
cert_coveringFacets_5
cert_coveringProof
cert_certificate 4 10
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0800

end
end BundlePart29

-- Public target certificates; internal witness data stays private.
namespace Nonrational.TerminalVerification
open Papers.RationalityTen.ChirotopeDensity.FiniteProjection
open Nonrational.TerminalData
set_option maxRecDepth 100000
set_option maxHeartbeats 0

public theorem projection_4653 : Certifies 4653 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0771.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_4654 : Certifies 4654 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0772.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_4655 : Certifies 4655 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0773.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_4656 : Certifies 4656 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0774.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_4657 : Certifies 4657 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0775.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_4658 : Certifies 4658 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0776.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_4659 : Certifies 4659 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0777.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_4660 : Certifies 4660 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0778.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_4661 : Certifies 4661 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0779.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_4662 : Certifies 4662 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0780.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_4663 : Certifies 4663 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0781.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_4664 : Certifies 4664 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0782.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_4665 : Certifies 4665 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0783.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_4666 : Certifies 4666 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0784.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_4667 : Certifies 4667 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0785.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_4668 : Certifies 4668 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0786.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_4669 : Certifies 4669 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0787.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_4670 : Certifies 4670 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0788.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_4671 : Certifies 4671 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0789.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_4672 : Certifies 4672 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0790.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_4673 : Certifies 4673 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0791.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_4674 : Certifies 4674 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0792.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_4675 : Certifies 4675 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0793.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_4676 : Certifies 4676 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0794.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_4677 : Certifies 4677 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0795.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_4678 : Certifies 4678 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0796.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_4679 : Certifies 4679 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0797.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_4680 : Certifies 4680 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0798.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_4681 : Certifies 4681 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0799.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_4682 : Certifies 4682 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0800.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem certified_B154 (j : Fin 30) :
    Certifies (4653 + j.val) := by
  fin_cases j
  · exact projection_4653
  · exact projection_4654
  · exact projection_4655
  · exact projection_4656
  · exact projection_4657
  · exact projection_4658
  · exact projection_4659
  · exact projection_4660
  · exact projection_4661
  · exact projection_4662
  · exact projection_4663
  · exact projection_4664
  · exact projection_4665
  · exact projection_4666
  · exact projection_4667
  · exact projection_4668
  · exact projection_4669
  · exact projection_4670
  · exact projection_4671
  · exact projection_4672
  · exact projection_4673
  · exact projection_4674
  · exact projection_4675
  · exact projection_4676
  · exact projection_4677
  · exact projection_4678
  · exact projection_4679
  · exact projection_4680
  · exact projection_4681
  · exact projection_4682

end Nonrational.TerminalVerification
-- Explicit facial frame witnesses, with lexical vector tracking.
