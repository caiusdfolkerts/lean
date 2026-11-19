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
/- Source: ProjectionCertificates/R_m15e10q1_0395.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0395

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [675, 805, 217, 793, 425, 657, 214, 662, 358, 550, 458, 418, 844, 596, 600, 25, 137, 265, 145, 529, 161, 289, 545, 641, 769, 150, 38, 70, 518, 162, 290, 546, 194, 322, 386, 642, 84, 532, 292, 548, 324, 580, 772, 88, 536, 200, 328, 584, 392, 776, 208, 592, 656, 416]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_675, vertices_805, vertices_217, vertices_793, vertices_425, vertices_657, vertices_214, vertices_662, vertices_358, vertices_550, vertices_458, vertices_418, vertices_844, vertices_596, vertices_600] (by decide +kernel)
  polygons := literalFinset [vertices_25, vertices_137, vertices_265, vertices_145, vertices_529, vertices_161, vertices_289, vertices_545, vertices_641, vertices_769, vertices_150, vertices_38, vertices_70, vertices_518, vertices_162, vertices_290, vertices_546, vertices_194, vertices_322, vertices_386, vertices_642, vertices_84, vertices_532, vertices_292, vertices_548, vertices_324, vertices_580, vertices_772, vertices_88, vertices_536, vertices_200, vertices_328, vertices_584, vertices_392, vertices_776, vertices_208, vertices_592, vertices_656, vertices_416] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_675), (false, vertices_805), (false, vertices_217), (false, vertices_793), (false, vertices_425), (false, vertices_657), (true, vertices_150), (true, vertices_38), (true, vertices_70), (true, vertices_518), (true, vertices_290), (true, vertices_194), (true, vertices_322), (true, vertices_386), (true, vertices_84), (true, vertices_532), (true, vertices_324), (true, vertices_580), (true, vertices_328), (true, vertices_584), (true, vertices_592)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 18 20 24 25 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_675) then 16 else
  if p.val = (false, vertices_805) then 19 else
  if p.val = (false, vertices_217) then 21 else
  if p.val = (false, vertices_793) then 22 else
  if p.val = (false, vertices_425) then 23 else
  if p.val = (false, vertices_657) then 0 else
  if p.val = (true, vertices_150) then 17 else
  if p.val = (true, vertices_38) then 1 else
  if p.val = (true, vertices_70) then 2 else
  if p.val = (true, vertices_518) then 3 else
  if p.val = (true, vertices_290) then 4 else
  if p.val = (true, vertices_194) then 5 else
  if p.val = (true, vertices_322) then 6 else
  if p.val = (true, vertices_386) then 7 else
  if p.val = (true, vertices_84) then 8 else
  if p.val = (true, vertices_532) then 9 else
  if p.val = (true, vertices_324) then 10 else
  if p.val = (true, vertices_580) then 11 else
  if p.val = (true, vertices_328) then 12 else
  if p.val = (true, vertices_584) then 13 else
  if p.val = (true, vertices_592) then 14 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_657), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_38), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_70), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_518), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_290), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_194), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_322), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_386), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_84), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_532), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_324), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_580), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_328), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_584), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_592), by decide +kernel⟩
  | 15 => Sum.inl 0
  | 16 => Sum.inr ⟨(false, vertices_675), by decide +kernel⟩
  | 17 => Sum.inr ⟨(true, vertices_150), by decide +kernel⟩
  | 18 => Sum.inl 1
  | 19 => Sum.inr ⟨(false, vertices_805), by decide +kernel⟩
  | 20 => Sum.inl 2
  | 21 => Sum.inr ⟨(false, vertices_217), by decide +kernel⟩
  | 22 => Sum.inr ⟨(false, vertices_793), by decide +kernel⟩
  | 23 => Sum.inr ⟨(false, vertices_425), by decide +kernel⟩
  | 24 => Sum.inl 3
  | 25 => Sum.inl 4
  | 26 => Sum.inl 5
  | 27 => Sum.inl 6
  | 28 => Sum.inl 7
  | 29 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 1 3 6 150
cert_row_4 1 0 1 4 5 7 358 38 3
cert_row_4 2 0 2 5 6 7 458 194 1
cert_row_4 3 1 2 5 7 8 844 324 1
cert_rows
cert_pivot_2 3 4 0 1
cert_heightProof 4
cert_coverFacet 0 214
cert_cover_5 0 0 0 1 3 5 150 214 3
cert_coverFacet 1 662
cert_cover_5 1 0 0 1 3 8 150 662 3
cert_coverFacet 2 358
cert_cover_5 2 1 0 1 4 5 38 358 3
cert_coverFacet 3 550
cert_cover_2 3 1 0 4 8 38 550 3
cert_coverFacet 4 458
cert_cover_5 4 2 0 2 5 6 194 458 1
cert_coverFacet 5 418
cert_cover_2 5 4 0 6 7 162 418 3
cert_coverFacet 6 844
cert_cover_5 6 3 1 2 5 7 324 844 1
cert_coverFacet 7 596
cert_cover_2 7 3 1 5 8 84 596 3
cert_coverFacet 8 600
cert_cover_2 8 3 2 5 8 88 600 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0395

end
end BundlePart0

section BundlePart1
/- Source: ProjectionCertificates/R_m15e10q1_0396.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0396

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [787, 613, 409, 721, 481, 801, 158, 558, 710, 282, 810, 658, 364, 204, 456, 145, 273, 529, 97, 289, 545, 193, 577, 385, 769, 14, 134, 518, 26, 554, 266, 146, 274, 530, 642, 770, 44, 76, 140, 100, 548, 196, 580, 152, 280, 296, 200, 328, 392, 656, 352, 800, 448, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_787, vertices_613, vertices_409, vertices_721, vertices_481, vertices_801, vertices_158, vertices_558, vertices_710, vertices_282, vertices_810, vertices_658, vertices_364, vertices_204, vertices_456] (by decide +kernel)
  polygons := literalFinset [vertices_145, vertices_273, vertices_529, vertices_97, vertices_289, vertices_545, vertices_193, vertices_577, vertices_385, vertices_769, vertices_14, vertices_134, vertices_518, vertices_26, vertices_554, vertices_266, vertices_146, vertices_274, vertices_530, vertices_642, vertices_770, vertices_44, vertices_76, vertices_140, vertices_100, vertices_548, vertices_196, vertices_580, vertices_152, vertices_280, vertices_296, vertices_200, vertices_328, vertices_392, vertices_656, vertices_352, vertices_800, vertices_448, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_787), (false, vertices_613), (false, vertices_409), (false, vertices_721), (false, vertices_481), (false, vertices_801), (true, vertices_14), (true, vertices_134), (true, vertices_518), (true, vertices_26), (true, vertices_554), (true, vertices_266), (true, vertices_146), (true, vertices_642), (true, vertices_44), (true, vertices_76), (true, vertices_140), (true, vertices_196), (true, vertices_296), (true, vertices_200), (true, vertices_328)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 18 20 22 24 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_787) then 16 else
  if p.val = (false, vertices_613) then 19 else
  if p.val = (false, vertices_409) then 21 else
  if p.val = (false, vertices_721) then 23 else
  if p.val = (false, vertices_481) then 25 else
  if p.val = (false, vertices_801) then 0 else
  if p.val = (true, vertices_14) then 1 else
  if p.val = (true, vertices_134) then 2 else
  if p.val = (true, vertices_518) then 3 else
  if p.val = (true, vertices_26) then 4 else
  if p.val = (true, vertices_554) then 17 else
  if p.val = (true, vertices_266) then 5 else
  if p.val = (true, vertices_146) then 6 else
  if p.val = (true, vertices_642) then 7 else
  if p.val = (true, vertices_44) then 8 else
  if p.val = (true, vertices_76) then 9 else
  if p.val = (true, vertices_140) then 10 else
  if p.val = (true, vertices_196) then 11 else
  if p.val = (true, vertices_296) then 12 else
  if p.val = (true, vertices_200) then 13 else
  if p.val = (true, vertices_328) then 14 else
  0
cert_priority
cert_nodeAtPriority_13 801 14 134 518 26 266 146 642 44 76 140 196 296 200 328 787 554 613 409 721 481
cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 2 3 6 158 14 3
cert_row_4 1 0 1 5 6 8 710 134 2
cert_row_2 2 0 2 4 8 554
cert_row_4 3 1 2 4 5 7 364 44 3
cert_rows
cert_pivot_2 3 6 0 1
cert_heightProof 4
cert_coverFacet 0 158
cert_cover_5 0 0 0 1 2 3 14 158 3
cert_coverFacet 1 558
cert_cover_5 1 2 0 1 2 4 14 558 3
cert_coverFacet 2 710
cert_cover_5 2 1 0 1 5 6 134 710 2
cert_coverFacet 3 282
cert_cover_2 3 2 0 3 7 26 282 3
cert_coverFacet 4 810
cert_cover_5 4 2 0 2 4 7 554 810 3
cert_coverFacet 5 658
cert_cover_2 5 3 0 6 8 146 658 3
cert_coverFacet 6 364
cert_cover_5 6 3 1 2 4 5 44 364 3
cert_coverFacet 7 204
cert_cover_2 7 2 1 5 6 76 204 3
cert_coverFacet 8 456
cert_cover_2 8 5 2 6 7 200 456 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0396

end
end BundlePart1

section BundlePart2
/- Source: ProjectionCertificates/R_m15e10q1_0397.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0397

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [675, 597, 357, 901, 617, 417, 662, 570, 154, 362, 394, 418, 220, 460, 600, 69, 261, 517, 97, 161, 289, 545, 577, 385, 641, 26, 42, 138, 266, 146, 530, 162, 290, 546, 386, 642, 204, 84, 148, 532, 324, 388, 644, 88, 152, 536, 104, 552, 328, 584, 392, 592, 352, 416]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_675, vertices_597, vertices_357, vertices_901, vertices_617, vertices_417, vertices_662, vertices_570, vertices_154, vertices_362, vertices_394, vertices_418, vertices_220, vertices_460, vertices_600] (by decide +kernel)
  polygons := literalFinset [vertices_69, vertices_261, vertices_517, vertices_97, vertices_161, vertices_289, vertices_545, vertices_577, vertices_385, vertices_641, vertices_26, vertices_42, vertices_138, vertices_266, vertices_146, vertices_530, vertices_162, vertices_290, vertices_546, vertices_386, vertices_642, vertices_204, vertices_84, vertices_148, vertices_532, vertices_324, vertices_388, vertices_644, vertices_88, vertices_152, vertices_536, vertices_104, vertices_552, vertices_328, vertices_584, vertices_392, vertices_592, vertices_352, vertices_416] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_675), (false, vertices_597), (false, vertices_357), (false, vertices_901), (false, vertices_617), (false, vertices_417), (true, vertices_26), (true, vertices_42), (true, vertices_138), (true, vertices_266), (true, vertices_146), (true, vertices_530), (true, vertices_290), (true, vertices_386), (true, vertices_204), (true, vertices_148), (true, vertices_88), (true, vertices_152), (true, vertices_536), (true, vertices_328), (true, vertices_392)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 20 17 24 25 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_675) then 16 else
  if p.val = (false, vertices_597) then 21 else
  if p.val = (false, vertices_357) then 22 else
  if p.val = (false, vertices_901) then 23 else
  if p.val = (false, vertices_617) then 18 else
  if p.val = (false, vertices_417) then 0 else
  if p.val = (true, vertices_26) then 1 else
  if p.val = (true, vertices_42) then 2 else
  if p.val = (true, vertices_138) then 3 else
  if p.val = (true, vertices_266) then 4 else
  if p.val = (true, vertices_146) then 5 else
  if p.val = (true, vertices_530) then 6 else
  if p.val = (true, vertices_290) then 7 else
  if p.val = (true, vertices_386) then 8 else
  if p.val = (true, vertices_204) then 19 else
  if p.val = (true, vertices_148) then 9 else
  if p.val = (true, vertices_88) then 10 else
  if p.val = (true, vertices_152) then 11 else
  if p.val = (true, vertices_536) then 12 else
  if p.val = (true, vertices_328) then 13 else
  if p.val = (true, vertices_392) then 14 else
  0
cert_priority
cert_nodeAtPriority_43 417 1 26 2 42 138 266 146 530 290 386 148 88 152 536 328 392 675 617 204 597 357 901
cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 2 4 5 7 362 42 3
cert_row_2 1 1 2 5 6 204
cert_row_4 2 0 1 3 6 8 662 146 1
cert_row_4 3 0 2 3 4 8 570 26 3
cert_rows
cert_pivot_2 7 5 1 0
cert_heightProof 4
cert_coverFacet 0 662
cert_cover_5 0 2 0 1 3 6 146 662 1
cert_coverFacet 1 570
cert_cover_5 1 3 0 2 3 4 26 570 3
cert_coverFacet 2 154
cert_cover_2 2 2 0 3 6 26 154 3
cert_coverFacet 3 362
cert_cover_5 3 0 0 2 4 5 42 362 3
cert_coverFacet 4 394
cert_cover_2 4 2 0 6 7 138 394 3
cert_coverFacet 5 418
cert_cover_2 5 4 0 6 7 162 418 3
cert_coverFacet 6 220
cert_cover_5 6 1 1 2 3 5 204 220 2
cert_coverFacet 7 460
cert_cover_5 7 1 1 2 5 7 204 460 3
cert_coverFacet 8 600
cert_cover_2 8 3 2 5 8 88 600 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0397

end
end BundlePart2

section BundlePart3
/- Source: ProjectionCertificates/R_m15e10q1_0398.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0398

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [707, 301, 653, 597, 325, 457, 310, 186, 666, 850, 482, 60, 540, 340, 424, 13, 69, 261, 517, 137, 265, 193, 321, 577, 641, 154, 50, 274, 530, 162, 290, 194, 322, 578, 642, 28, 44, 524, 52, 84, 276, 532, 292, 324, 56, 536, 168, 296, 392, 648, 336, 592, 416, 448]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_707, vertices_301, vertices_653, vertices_597, vertices_325, vertices_457, vertices_310, vertices_186, vertices_666, vertices_850, vertices_482, vertices_60, vertices_540, vertices_340, vertices_424] (by decide +kernel)
  polygons := literalFinset [vertices_13, vertices_69, vertices_261, vertices_517, vertices_137, vertices_265, vertices_193, vertices_321, vertices_577, vertices_641, vertices_154, vertices_50, vertices_274, vertices_530, vertices_162, vertices_290, vertices_194, vertices_322, vertices_578, vertices_642, vertices_28, vertices_44, vertices_524, vertices_52, vertices_84, vertices_276, vertices_532, vertices_292, vertices_324, vertices_56, vertices_536, vertices_168, vertices_296, vertices_392, vertices_648, vertices_336, vertices_592, vertices_416, vertices_448] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_707), (false, vertices_301), (false, vertices_653), (false, vertices_597), (false, vertices_325), (false, vertices_457), (true, vertices_154), (true, vertices_50), (true, vertices_274), (true, vertices_530), (true, vertices_162), (true, vertices_290), (true, vertices_322), (true, vertices_28), (true, vertices_52), (true, vertices_276), (true, vertices_56), (true, vertices_536), (true, vertices_168), (true, vertices_336), (true, vertices_416)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 18 22 24 25 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_707) then 16 else
  if p.val = (false, vertices_301) then 19 else
  if p.val = (false, vertices_653) then 20 else
  if p.val = (false, vertices_597) then 21 else
  if p.val = (false, vertices_325) then 0 else
  if p.val = (false, vertices_457) then 23 else
  if p.val = (true, vertices_154) then 17 else
  if p.val = (true, vertices_50) then 1 else
  if p.val = (true, vertices_274) then 2 else
  if p.val = (true, vertices_530) then 3 else
  if p.val = (true, vertices_162) then 4 else
  if p.val = (true, vertices_290) then 5 else
  if p.val = (true, vertices_322) then 6 else
  if p.val = (true, vertices_28) then 7 else
  if p.val = (true, vertices_52) then 8 else
  if p.val = (true, vertices_276) then 9 else
  if p.val = (true, vertices_56) then 10 else
  if p.val = (true, vertices_536) then 11 else
  if p.val = (true, vertices_168) then 12 else
  if p.val = (true, vertices_336) then 13 else
  if p.val = (true, vertices_416) then 14 else
  0
cert_priority
cert_nodeAtPriority_51 325 50 274 530 162 290 322 28 52 276 56 536 168 336 416 707 154 301 653 597 457
cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 2 3 6 154
cert_row_4 1 0 1 3 4 7 310 50 1
cert_row_4 2 0 3 5 7 8 850 274 2
cert_row_4 3 0 4 5 6 7 482 162 2
cert_rows
cert_pivot_2 2 1 3 0
cert_heightProof 4
cert_coverFacet 0 310
cert_cover_5 0 1 0 1 3 4 50 310 1
cert_coverFacet 1 186
cert_cover_5 1 0 0 2 3 4 154 186 3
cert_coverFacet 2 666
cert_cover_5 2 0 0 2 3 8 154 666 3
cert_coverFacet 3 850
cert_cover_5 3 2 0 3 5 7 274 850 2
cert_coverFacet 4 482
cert_cover_5 4 3 0 4 5 6 162 482 2
cert_coverFacet 5 60
cert_cover_2 5 2 1 3 4 28 60 3
cert_coverFacet 6 540
cert_cover_2 6 2 1 3 8 28 540 3
cert_coverFacet 7 340
cert_cover_2 7 3 1 5 7 84 340 3
cert_coverFacet 8 424
cert_cover_2 8 4 2 6 7 168 424 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0398

end
end BundlePart3

section BundlePart4
/- Source: ProjectionCertificates/R_m15e10q1_0399.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0399

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [707, 901, 617, 817, 481, 150, 790, 646, 218, 602, 316, 156, 460, 568, 360, 97, 289, 545, 193, 577, 385, 641, 769, 22, 134, 518, 90, 146, 530, 194, 578, 642, 28, 140, 268, 148, 276, 388, 644, 772, 56, 152, 536, 104, 296, 552, 200, 328, 584, 304, 560, 784, 352, 448]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_707, vertices_901, vertices_617, vertices_817, vertices_481, vertices_150, vertices_790, vertices_646, vertices_218, vertices_602, vertices_316, vertices_156, vertices_460, vertices_568, vertices_360] (by decide +kernel)
  polygons := literalFinset [vertices_97, vertices_289, vertices_545, vertices_193, vertices_577, vertices_385, vertices_641, vertices_769, vertices_22, vertices_134, vertices_518, vertices_90, vertices_146, vertices_530, vertices_194, vertices_578, vertices_642, vertices_28, vertices_140, vertices_268, vertices_148, vertices_276, vertices_388, vertices_644, vertices_772, vertices_56, vertices_152, vertices_536, vertices_104, vertices_296, vertices_552, vertices_200, vertices_328, vertices_584, vertices_304, vertices_560, vertices_784, vertices_352, vertices_448] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_707), (false, vertices_901), (false, vertices_617), (false, vertices_817), (false, vertices_481), (true, vertices_22), (true, vertices_134), (true, vertices_518), (true, vertices_90), (true, vertices_146), (true, vertices_530), (true, vertices_28), (true, vertices_140), (true, vertices_268), (true, vertices_148), (true, vertices_276), (true, vertices_56), (true, vertices_152), (true, vertices_536), (true, vertices_296), (true, vertices_200), (true, vertices_328)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 16 19 21 23 25 27 28 29 30
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_707) then 17 else
  if p.val = (false, vertices_901) then 20 else
  if p.val = (false, vertices_617) then 22 else
  if p.val = (false, vertices_817) then 24 else
  if p.val = (false, vertices_481) then 26 else
  if p.val = (true, vertices_22) then 0 else
  if p.val = (true, vertices_134) then 1 else
  if p.val = (true, vertices_518) then 2 else
  if p.val = (true, vertices_90) then 18 else
  if p.val = (true, vertices_146) then 3 else
  if p.val = (true, vertices_530) then 4 else
  if p.val = (true, vertices_28) then 5 else
  if p.val = (true, vertices_140) then 6 else
  if p.val = (true, vertices_268) then 7 else
  if p.val = (true, vertices_148) then 8 else
  if p.val = (true, vertices_276) then 9 else
  if p.val = (true, vertices_56) then 10 else
  if p.val = (true, vertices_152) then 11 else
  if p.val = (true, vertices_536) then 12 else
  if p.val = (true, vertices_296) then 13 else
  if p.val = (true, vertices_200) then 14 else
  if p.val = (true, vertices_328) then 15 else
  0
cert_priority
cert_nodeAtPriority_64 22 134 518 146 530 28 140 268 148 276 56 152 536 296 200 328 707 90 901 617 817 481
cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 3 7 8 790 22 3
cert_row_2 1 0 2 3 5 90
cert_row_4 2 1 2 3 4 7 316 28 3
cert_row_4 3 1 2 5 6 7 460 140 2
cert_rows
cert_pivot_2 8 0 3 1
cert_heightProof 4
cert_coverFacet 0 150
cert_cover_2 0 1 0 3 6 22 150 3
cert_coverFacet 1 790
cert_cover_5 1 0 0 1 3 7 22 790 3
cert_coverFacet 2 646
cert_cover_2 2 1 0 6 8 134 646 3
cert_coverFacet 3 218
cert_cover_5 3 1 0 2 3 6 90 218 3
cert_coverFacet 4 602
cert_cover_5 4 1 0 2 3 8 90 602 3
cert_coverFacet 5 316
cert_cover_5 5 2 1 2 3 4 28 316 3
cert_coverFacet 6 156
cert_cover_2 6 2 1 3 6 28 156 3
cert_coverFacet 7 460
cert_cover_5 7 3 1 2 5 6 140 460 2
cert_coverFacet 8 568
cert_cover_2 8 3 2 4 8 56 568 3
cert_coverFacet 9 360
cert_cover_2 9 4 2 5 7 104 360 3
cert_coveringFacets_5
cert_coveringProof
cert_certificate 4 10
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0399

end
end BundlePart4

section BundlePart5
/- Source: ProjectionCertificates/R_m15e10q1_0401.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0401

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [403, 613, 793, 721, 481, 801, 110, 142, 710, 154, 282, 362, 450, 668, 812, 145, 273, 529, 97, 289, 545, 193, 577, 385, 769, 14, 70, 134, 26, 106, 138, 266, 146, 274, 194, 322, 386, 44, 140, 524, 100, 548, 580, 644, 152, 280, 536, 296, 776, 656, 352, 800, 448, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_403, vertices_613, vertices_793, vertices_721, vertices_481, vertices_801, vertices_110, vertices_142, vertices_710, vertices_154, vertices_282, vertices_362, vertices_450, vertices_668, vertices_812] (by decide +kernel)
  polygons := literalFinset [vertices_145, vertices_273, vertices_529, vertices_97, vertices_289, vertices_545, vertices_193, vertices_577, vertices_385, vertices_769, vertices_14, vertices_70, vertices_134, vertices_26, vertices_106, vertices_138, vertices_266, vertices_146, vertices_274, vertices_194, vertices_322, vertices_386, vertices_44, vertices_140, vertices_524, vertices_100, vertices_548, vertices_580, vertices_644, vertices_152, vertices_280, vertices_536, vertices_296, vertices_776, vertices_656, vertices_352, vertices_800, vertices_448, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_403), (false, vertices_613), (false, vertices_793), (false, vertices_721), (false, vertices_481), (false, vertices_801), (true, vertices_14), (true, vertices_70), (true, vertices_134), (true, vertices_26), (true, vertices_106), (true, vertices_138), (true, vertices_266), (true, vertices_194), (true, vertices_322), (true, vertices_44), (true, vertices_140), (true, vertices_524), (true, vertices_644), (true, vertices_152), (true, vertices_296)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 18 20 22 24 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_403) then 16 else
  if p.val = (false, vertices_613) then 19 else
  if p.val = (false, vertices_793) then 21 else
  if p.val = (false, vertices_721) then 23 else
  if p.val = (false, vertices_481) then 25 else
  if p.val = (false, vertices_801) then 0 else
  if p.val = (true, vertices_14) then 1 else
  if p.val = (true, vertices_70) then 2 else
  if p.val = (true, vertices_134) then 3 else
  if p.val = (true, vertices_26) then 4 else
  if p.val = (true, vertices_106) then 17 else
  if p.val = (true, vertices_138) then 5 else
  if p.val = (true, vertices_266) then 6 else
  if p.val = (true, vertices_194) then 7 else
  if p.val = (true, vertices_322) then 8 else
  if p.val = (true, vertices_44) then 9 else
  if p.val = (true, vertices_140) then 10 else
  if p.val = (true, vertices_524) then 11 else
  if p.val = (true, vertices_644) then 12 else
  if p.val = (true, vertices_152) then 13 else
  if p.val = (true, vertices_296) then 14 else
  0
cert_priority
cert_nodeAtPriority_13 801 14 70 134 26 138 266 194 322 44 140 524 644 152 296 403 106 613 793 721 481
cert_priority_injective
cert_incidenceProof
cert_row_4 0 1 2 3 6 8 668 140 2
cert_row_4 1 0 1 5 6 8 710 70 3
cert_row_2 2 0 2 4 5 106
cert_row_4 3 1 2 4 7 8 812 44 3
cert_rows
cert_pivot_2 3 6 0 1
cert_heightProof 4
cert_coverFacet 0 110
cert_cover_5 0 2 0 1 2 4 14 110 3
cert_coverFacet 1 142
cert_cover_2 1 1 0 2 6 14 142 3
cert_coverFacet 2 710
cert_cover_5 2 1 0 1 5 6 70 710 3
cert_coverFacet 3 154
cert_cover_2 3 2 0 3 6 26 154 3
cert_coverFacet 4 282
cert_cover_2 4 2 0 3 7 26 282 3
cert_coverFacet 5 362
cert_cover_5 5 2 0 2 4 7 106 362 3
cert_coverFacet 6 450
cert_cover_2 6 5 0 6 7 194 450 3
cert_coverFacet 7 668
cert_cover_5 7 0 1 2 3 6 140 668 2
cert_coverFacet 8 812
cert_cover_5 8 3 1 2 4 7 44 812 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0401

end
end BundlePart5

section BundlePart6
/- Source: ProjectionCertificates/R_m15e10q1_0402.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0402

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [419, 901, 601, 369, 785, 737, 94, 174, 342, 390, 618, 354, 796, 652, 680, 81, 273, 529, 97, 161, 289, 577, 385, 641, 769, 14, 86, 134, 262, 42, 74, 98, 162, 290, 322, 386, 28, 140, 524, 276, 388, 644, 772, 88, 536, 168, 552, 584, 648, 336, 784, 352, 608, 672]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_419, vertices_901, vertices_601, vertices_369, vertices_785, vertices_737, vertices_94, vertices_174, vertices_342, vertices_390, vertices_618, vertices_354, vertices_796, vertices_652, vertices_680] (by decide +kernel)
  polygons := literalFinset [vertices_81, vertices_273, vertices_529, vertices_97, vertices_161, vertices_289, vertices_577, vertices_385, vertices_641, vertices_769, vertices_14, vertices_86, vertices_134, vertices_262, vertices_42, vertices_74, vertices_98, vertices_162, vertices_290, vertices_322, vertices_386, vertices_28, vertices_140, vertices_524, vertices_276, vertices_388, vertices_644, vertices_772, vertices_88, vertices_536, vertices_168, vertices_552, vertices_584, vertices_648, vertices_336, vertices_784, vertices_352, vertices_608, vertices_672] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_419), (false, vertices_901), (false, vertices_601), (false, vertices_369), (false, vertices_785), (false, vertices_737), (true, vertices_14), (true, vertices_86), (true, vertices_134), (true, vertices_262), (true, vertices_42), (true, vertices_74), (true, vertices_98), (true, vertices_322), (true, vertices_28), (true, vertices_140), (true, vertices_524), (true, vertices_276), (true, vertices_168), (true, vertices_552), (true, vertices_648)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 18 20 22 24 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_419) then 16 else
  if p.val = (false, vertices_901) then 19 else
  if p.val = (false, vertices_601) then 21 else
  if p.val = (false, vertices_369) then 23 else
  if p.val = (false, vertices_785) then 0 else
  if p.val = (false, vertices_737) then 25 else
  if p.val = (true, vertices_14) then 1 else
  if p.val = (true, vertices_86) then 17 else
  if p.val = (true, vertices_134) then 2 else
  if p.val = (true, vertices_262) then 3 else
  if p.val = (true, vertices_42) then 4 else
  if p.val = (true, vertices_74) then 5 else
  if p.val = (true, vertices_98) then 6 else
  if p.val = (true, vertices_322) then 7 else
  if p.val = (true, vertices_28) then 8 else
  if p.val = (true, vertices_140) then 9 else
  if p.val = (true, vertices_524) then 10 else
  if p.val = (true, vertices_276) then 11 else
  if p.val = (true, vertices_168) then 12 else
  if p.val = (true, vertices_552) then 13 else
  if p.val = (true, vertices_648) then 14 else
  0
cert_priority
cert_nodeAtPriority_13 785 14 134 262 42 74 98 322 28 140 524 276 168 552 648 419 86 901 601 369 737
cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 2 4 6 174 14 3
cert_row_4 1 0 2 4 5 8 618 42 3
cert_row_2 2 0 1 3 5 86
cert_row_4 3 1 2 3 7 8 796 28 3
cert_rows
cert_pivot_2 6 4 0 1
cert_heightProof 4
cert_coverFacet 0 94
cert_cover_5 0 2 0 1 2 3 14 94 3
cert_coverFacet 1 174
cert_cover_5 1 0 0 1 2 4 14 174 3
cert_coverFacet 2 342
cert_cover_5 2 2 0 1 3 7 86 342 3
cert_coverFacet 3 390
cert_cover_2 3 1 0 6 7 134 390 3
cert_coverFacet 4 618
cert_cover_5 4 1 0 2 4 5 42 618 3
cert_coverFacet 5 354
cert_cover_2 5 4 0 5 7 98 354 3
cert_coverFacet 6 796
cert_cover_5 6 3 1 2 3 7 28 796 3
cert_coverFacet 7 652
cert_cover_2 7 2 1 6 8 140 652 3
cert_coverFacet 8 680
cert_cover_2 8 4 2 6 8 168 680 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0402

end
end BundlePart6

section BundlePart7
/- Source: ProjectionCertificates/R_m15e10q1_0403.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0403

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [803, 597, 313, 89, 617, 913, 662, 230, 614, 426, 898, 92, 412, 204, 232, 25, 41, 73, 81, 273, 529, 289, 545, 577, 769, 102, 134, 518, 162, 290, 546, 386, 642, 770, 28, 76, 140, 84, 148, 532, 196, 580, 88, 280, 104, 168, 296, 200, 392, 400, 656, 224, 608, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_803, vertices_597, vertices_313, vertices_89, vertices_617, vertices_913, vertices_662, vertices_230, vertices_614, vertices_426, vertices_898, vertices_92, vertices_412, vertices_204, vertices_232] (by decide +kernel)
  polygons := literalFinset [vertices_25, vertices_41, vertices_73, vertices_81, vertices_273, vertices_529, vertices_289, vertices_545, vertices_577, vertices_769, vertices_102, vertices_134, vertices_518, vertices_162, vertices_290, vertices_546, vertices_386, vertices_642, vertices_770, vertices_28, vertices_76, vertices_140, vertices_84, vertices_148, vertices_532, vertices_196, vertices_580, vertices_88, vertices_280, vertices_104, vertices_168, vertices_296, vertices_200, vertices_392, vertices_400, vertices_656, vertices_224, vertices_608, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_803), (false, vertices_597), (false, vertices_313), (false, vertices_89), (false, vertices_617), (false, vertices_913), (true, vertices_102), (true, vertices_134), (true, vertices_518), (true, vertices_162), (true, vertices_386), (true, vertices_642), (true, vertices_28), (true, vertices_76), (true, vertices_140), (true, vertices_148), (true, vertices_196), (true, vertices_168), (true, vertices_200), (true, vertices_392), (true, vertices_224)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 18 20 23 25 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_803) then 16 else
  if p.val = (false, vertices_597) then 19 else
  if p.val = (false, vertices_313) then 21 else
  if p.val = (false, vertices_89) then 0 else
  if p.val = (false, vertices_617) then 22 else
  if p.val = (false, vertices_913) then 24 else
  if p.val = (true, vertices_102) then 17 else
  if p.val = (true, vertices_134) then 1 else
  if p.val = (true, vertices_518) then 2 else
  if p.val = (true, vertices_162) then 3 else
  if p.val = (true, vertices_386) then 4 else
  if p.val = (true, vertices_642) then 5 else
  if p.val = (true, vertices_28) then 6 else
  if p.val = (true, vertices_76) then 7 else
  if p.val = (true, vertices_140) then 8 else
  if p.val = (true, vertices_148) then 9 else
  if p.val = (true, vertices_196) then 10 else
  if p.val = (true, vertices_168) then 11 else
  if p.val = (true, vertices_200) then 12 else
  if p.val = (true, vertices_392) then 13 else
  if p.val = (true, vertices_224) then 14 else
  0
cert_priority
cert_nodeAtPriority_31 89 134 518 162 386 642 28 76 140 148 196 168 200 392 224 803 102 597 313 617 913
cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 1 4 5 102
cert_row_4 1 0 1 3 6 8 662 134 2
cert_row_4 2 0 2 4 6 7 426 162 1
cert_row_4 3 1 2 3 6 7 412 28 3
cert_rows
cert_pivot_2 5 8 0 1
cert_heightProof 4
cert_coverFacet 0 662
cert_cover_5 0 1 0 1 3 6 134 662 2
cert_coverFacet 1 230
cert_cover_5 1 0 0 1 4 6 102 230 3
cert_coverFacet 2 614
cert_cover_5 2 0 0 1 4 8 102 614 3
cert_coverFacet 3 426
cert_cover_5 3 2 0 2 4 6 162 426 1
cert_coverFacet 4 898
cert_cover_2 4 6 0 7 8 386 898 3
cert_coverFacet 5 92
cert_cover_2 5 2 1 3 5 28 92 3
cert_coverFacet 6 412
cert_cover_5 6 3 1 2 3 6 28 412 3
cert_coverFacet 7 204
cert_cover_2 7 2 1 5 6 76 204 3
cert_coverFacet 8 232
cert_cover_2 8 4 2 5 6 104 232 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0403

end
end BundlePart7

section BundlePart8
/- Source: ProjectionCertificates/R_m15e10q1_0404.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0404

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [395, 61, 153, 809, 625, 913, 206, 334, 722, 866, 898, 156, 300, 244, 356, 25, 41, 137, 265, 49, 145, 529, 545, 385, 769, 78, 138, 266, 194, 322, 578, 386, 642, 770, 28, 44, 140, 268, 52, 148, 100, 292, 196, 324, 152, 296, 112, 208, 592, 656, 352, 608, 800, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_395, vertices_61, vertices_153, vertices_809, vertices_625, vertices_913, vertices_206, vertices_334, vertices_722, vertices_866, vertices_898, vertices_156, vertices_300, vertices_244, vertices_356] (by decide +kernel)
  polygons := literalFinset [vertices_25, vertices_41, vertices_137, vertices_265, vertices_49, vertices_145, vertices_529, vertices_545, vertices_385, vertices_769, vertices_78, vertices_138, vertices_266, vertices_194, vertices_322, vertices_578, vertices_386, vertices_642, vertices_770, vertices_28, vertices_44, vertices_140, vertices_268, vertices_52, vertices_148, vertices_100, vertices_292, vertices_196, vertices_324, vertices_152, vertices_296, vertices_112, vertices_208, vertices_592, vertices_656, vertices_352, vertices_608, vertices_800, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_395), (false, vertices_61), (false, vertices_153), (false, vertices_809), (false, vertices_625), (false, vertices_913), (true, vertices_78), (true, vertices_194), (true, vertices_322), (true, vertices_578), (true, vertices_642), (true, vertices_770), (true, vertices_140), (true, vertices_268), (true, vertices_148), (true, vertices_100), (true, vertices_292), (true, vertices_196), (true, vertices_324), (true, vertices_208), (true, vertices_352)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 18 20 22 25 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_395) then 16 else
  if p.val = (false, vertices_61) then 19 else
  if p.val = (false, vertices_153) then 0 else
  if p.val = (false, vertices_809) then 21 else
  if p.val = (false, vertices_625) then 23 else
  if p.val = (false, vertices_913) then 24 else
  if p.val = (true, vertices_78) then 17 else
  if p.val = (true, vertices_194) then 1 else
  if p.val = (true, vertices_322) then 2 else
  if p.val = (true, vertices_578) then 3 else
  if p.val = (true, vertices_642) then 4 else
  if p.val = (true, vertices_770) then 5 else
  if p.val = (true, vertices_140) then 6 else
  if p.val = (true, vertices_268) then 7 else
  if p.val = (true, vertices_148) then 8 else
  if p.val = (true, vertices_100) then 9 else
  if p.val = (true, vertices_292) then 10 else
  if p.val = (true, vertices_196) then 11 else
  if p.val = (true, vertices_324) then 12 else
  if p.val = (true, vertices_208) then 13 else
  if p.val = (true, vertices_352) then 14 else
  0
cert_priority
cert_nodeAtPriority_40 153 194 322 578 642 770 140 268 148 100 292 196 324 208 352 395 78 61 809 625 913
cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 1 2 5 78
cert_row_4 1 0 4 5 7 8 866 322 1
cert_row_4 2 0 3 5 6 8 722 194 1
cert_row_4 3 1 3 4 5 6 244 52 3
cert_rows
cert_pivot_2 2 7 0 1
cert_heightProof 4
cert_coverFacet 0 206
cert_cover_5 0 0 0 1 2 6 78 206 3
cert_coverFacet 1 334
cert_cover_5 1 0 0 1 2 7 78 334 3
cert_coverFacet 2 722
cert_cover_5 2 2 0 3 5 6 194 722 1
cert_coverFacet 3 866
cert_cover_5 3 1 0 4 5 7 322 866 1
cert_coverFacet 4 898
cert_cover_2 4 6 0 7 8 386 898 3
cert_coverFacet 5 156
cert_cover_2 5 2 1 3 6 28 156 3
cert_coverFacet 6 300
cert_cover_2 6 2 1 4 7 44 300 3
cert_coverFacet 7 244
cert_cover_5 7 3 1 3 4 5 52 244 3
cert_coverFacet 8 356
cert_cover_2 8 4 1 5 7 100 356 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0404

end
end BundlePart8

section BundlePart9
/- Source: ProjectionCertificates/R_m15e10q1_0405.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0405

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [707, 837, 681, 817, 481, 94, 790, 582, 218, 658, 316, 460, 568, 664, 424, 161, 289, 545, 193, 321, 577, 641, 769, 22, 70, 518, 90, 146, 530, 194, 578, 642, 28, 76, 268, 276, 324, 580, 772, 56, 152, 536, 168, 296, 552, 200, 392, 648, 304, 560, 656, 784, 416, 448]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_707, vertices_837, vertices_681, vertices_817, vertices_481, vertices_94, vertices_790, vertices_582, vertices_218, vertices_658, vertices_316, vertices_460, vertices_568, vertices_664, vertices_424] (by decide +kernel)
  polygons := literalFinset [vertices_161, vertices_289, vertices_545, vertices_193, vertices_321, vertices_577, vertices_641, vertices_769, vertices_22, vertices_70, vertices_518, vertices_90, vertices_146, vertices_530, vertices_194, vertices_578, vertices_642, vertices_28, vertices_76, vertices_268, vertices_276, vertices_324, vertices_580, vertices_772, vertices_56, vertices_152, vertices_536, vertices_168, vertices_296, vertices_552, vertices_200, vertices_392, vertices_648, vertices_304, vertices_560, vertices_656, vertices_784, vertices_416, vertices_448] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_707), (false, vertices_837), (false, vertices_681), (false, vertices_817), (false, vertices_481), (true, vertices_22), (true, vertices_70), (true, vertices_518), (true, vertices_90), (true, vertices_146), (true, vertices_530), (true, vertices_28), (true, vertices_76), (true, vertices_268), (true, vertices_276), (true, vertices_56), (true, vertices_152), (true, vertices_536), (true, vertices_296), (true, vertices_200), (true, vertices_392), (true, vertices_656)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 16 19 21 23 25 27 28 29 30
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_707) then 17 else
  if p.val = (false, vertices_837) then 20 else
  if p.val = (false, vertices_681) then 22 else
  if p.val = (false, vertices_817) then 24 else
  if p.val = (false, vertices_481) then 26 else
  if p.val = (true, vertices_22) then 0 else
  if p.val = (true, vertices_70) then 1 else
  if p.val = (true, vertices_518) then 2 else
  if p.val = (true, vertices_90) then 18 else
  if p.val = (true, vertices_146) then 3 else
  if p.val = (true, vertices_530) then 4 else
  if p.val = (true, vertices_28) then 5 else
  if p.val = (true, vertices_76) then 6 else
  if p.val = (true, vertices_268) then 7 else
  if p.val = (true, vertices_276) then 8 else
  if p.val = (true, vertices_56) then 9 else
  if p.val = (true, vertices_152) then 10 else
  if p.val = (true, vertices_536) then 11 else
  if p.val = (true, vertices_296) then 12 else
  if p.val = (true, vertices_200) then 13 else
  if p.val = (true, vertices_392) then 14 else
  if p.val = (true, vertices_656) then 15 else
  0
cert_priority
cert_nodeAtPriority_64 22 70 518 146 530 28 76 268 276 56 152 536 296 200 392 656 707 90 837 681 817 481
cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 3 7 8 790 22 3
cert_row_2 1 0 2 3 5 90
cert_row_4 2 1 2 3 4 7 316 28 3
cert_row_4 3 1 2 5 6 7 460 76 3
cert_rows
cert_pivot_2 8 0 3 1
cert_heightProof 4
cert_coverFacet 0 94
cert_cover_5 0 1 0 1 2 3 22 94 2
cert_coverFacet 1 790
cert_cover_5 1 0 0 1 3 7 22 790 3
cert_coverFacet 2 582
cert_cover_2 2 1 0 5 8 70 582 3
cert_coverFacet 3 218
cert_cover_5 3 1 0 2 3 6 90 218 3
cert_coverFacet 4 658
cert_cover_2 4 3 0 6 8 146 658 3
cert_coverFacet 5 316
cert_cover_5 5 2 1 2 3 4 28 316 3
cert_coverFacet 6 460
cert_cover_5 6 3 1 2 5 6 76 460 3
cert_coverFacet 7 568
cert_cover_2 7 3 2 4 8 56 568 3
cert_coverFacet 8 664
cert_cover_2 8 3 2 6 8 152 664 3
cert_coverFacet 9 424
cert_cover_2 9 4 2 6 7 168 424 3
cert_coveringFacets_5
cert_coveringProof
cert_certificate 4 10
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0405

end
end BundlePart9

section BundlePart10
/- Source: ProjectionCertificates/R_m15e10q1_0406.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0406

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [803, 597, 313, 89, 617, 913, 662, 230, 614, 426, 898, 468, 344, 232, 456, 25, 41, 73, 81, 273, 529, 289, 545, 577, 769, 102, 134, 518, 162, 290, 546, 386, 642, 770, 84, 148, 532, 196, 580, 88, 280, 104, 168, 296, 200, 328, 392, 336, 400, 656, 224, 608, 448, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_803, vertices_597, vertices_313, vertices_89, vertices_617, vertices_913, vertices_662, vertices_230, vertices_614, vertices_426, vertices_898, vertices_468, vertices_344, vertices_232, vertices_456] (by decide +kernel)
  polygons := literalFinset [vertices_25, vertices_41, vertices_73, vertices_81, vertices_273, vertices_529, vertices_289, vertices_545, vertices_577, vertices_769, vertices_102, vertices_134, vertices_518, vertices_162, vertices_290, vertices_546, vertices_386, vertices_642, vertices_770, vertices_84, vertices_148, vertices_532, vertices_196, vertices_580, vertices_88, vertices_280, vertices_104, vertices_168, vertices_296, vertices_200, vertices_328, vertices_392, vertices_336, vertices_400, vertices_656, vertices_224, vertices_608, vertices_448, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_803), (false, vertices_597), (false, vertices_313), (false, vertices_89), (false, vertices_617), (false, vertices_913), (true, vertices_102), (true, vertices_134), (true, vertices_518), (true, vertices_162), (true, vertices_386), (true, vertices_642), (true, vertices_148), (true, vertices_196), (true, vertices_168), (true, vertices_200), (true, vertices_328), (true, vertices_392), (true, vertices_336), (true, vertices_224), (true, vertices_448)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 18 20 23 25 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_803) then 16 else
  if p.val = (false, vertices_597) then 19 else
  if p.val = (false, vertices_313) then 21 else
  if p.val = (false, vertices_89) then 0 else
  if p.val = (false, vertices_617) then 22 else
  if p.val = (false, vertices_913) then 24 else
  if p.val = (true, vertices_102) then 17 else
  if p.val = (true, vertices_134) then 1 else
  if p.val = (true, vertices_518) then 2 else
  if p.val = (true, vertices_162) then 3 else
  if p.val = (true, vertices_386) then 4 else
  if p.val = (true, vertices_642) then 5 else
  if p.val = (true, vertices_148) then 6 else
  if p.val = (true, vertices_196) then 7 else
  if p.val = (true, vertices_168) then 8 else
  if p.val = (true, vertices_200) then 9 else
  if p.val = (true, vertices_328) then 10 else
  if p.val = (true, vertices_392) then 11 else
  if p.val = (true, vertices_336) then 12 else
  if p.val = (true, vertices_224) then 13 else
  if p.val = (true, vertices_448) then 14 else
  0
cert_priority
cert_nodeAtPriority_31 89 134 518 162 386 642 148 196 168 200 328 392 336 224 448 803 102 597 313 617 913
cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 3 6 8 662 134 2
cert_row_4 1 0 2 4 6 7 426 162 1
cert_row_2 2 0 1 4 5 102
cert_row_4 3 1 3 5 6 7 468 84 3
cert_rows
cert_pivot_2 8 2 0 1
cert_heightProof 4
cert_coverFacet 0 662
cert_cover_5 0 0 0 1 3 6 134 662 2
cert_coverFacet 1 230
cert_cover_5 1 2 0 1 4 6 102 230 3
cert_coverFacet 2 614
cert_cover_5 2 2 0 1 4 8 102 614 3
cert_coverFacet 3 426
cert_cover_5 3 1 0 2 4 6 162 426 1
cert_coverFacet 4 898
cert_cover_2 4 6 0 7 8 386 898 3
cert_coverFacet 5 468
cert_cover_5 5 3 1 3 5 6 84 468 3
cert_coverFacet 6 344
cert_cover_2 6 3 2 5 7 88 344 3
cert_coverFacet 7 232
cert_cover_2 7 4 2 5 6 104 232 3
cert_coverFacet 8 456
cert_cover_2 8 5 2 6 7 200 456 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0406

end
end BundlePart10

section BundlePart11
/- Source: ProjectionCertificates/R_m15e10q1_0407.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0407

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [707, 781, 229, 293, 645, 313, 617, 902, 794, 626, 210, 402, 372, 468, 568, 37, 133, 261, 517, 41, 265, 521, 97, 289, 193, 577, 641, 82, 146, 274, 530, 194, 578, 386, 642, 770, 340, 100, 292, 196, 388, 644, 772, 56, 280, 536, 552, 776, 112, 304, 560, 208, 400, 608]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_707, vertices_781, vertices_229, vertices_293, vertices_645, vertices_313, vertices_617, vertices_902, vertices_794, vertices_626, vertices_210, vertices_402, vertices_372, vertices_468, vertices_568] (by decide +kernel)
  polygons := literalFinset [vertices_37, vertices_133, vertices_261, vertices_517, vertices_41, vertices_265, vertices_521, vertices_97, vertices_289, vertices_193, vertices_577, vertices_641, vertices_82, vertices_146, vertices_274, vertices_530, vertices_194, vertices_578, vertices_386, vertices_642, vertices_770, vertices_340, vertices_100, vertices_292, vertices_196, vertices_388, vertices_644, vertices_772, vertices_56, vertices_280, vertices_536, vertices_552, vertices_776, vertices_112, vertices_304, vertices_560, vertices_208, vertices_400, vertices_608] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_707), (false, vertices_781), (false, vertices_229), (false, vertices_293), (false, vertices_645), (false, vertices_313), (false, vertices_617), (true, vertices_82), (true, vertices_146), (true, vertices_274), (true, vertices_530), (true, vertices_386), (true, vertices_770), (true, vertices_340), (true, vertices_388), (true, vertices_536), (true, vertices_112), (true, vertices_560), (true, vertices_208), (true, vertices_400)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 14 16 20 23 24 25 26 27 28
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_707) then 15 else
  if p.val = (false, vertices_781) then 17 else
  if p.val = (false, vertices_229) then 18 else
  if p.val = (false, vertices_293) then 0 else
  if p.val = (false, vertices_645) then 1 else
  if p.val = (false, vertices_313) then 21 else
  if p.val = (false, vertices_617) then 22 else
  if p.val = (true, vertices_82) then 2 else
  if p.val = (true, vertices_146) then 3 else
  if p.val = (true, vertices_274) then 4 else
  if p.val = (true, vertices_530) then 5 else
  if p.val = (true, vertices_386) then 6 else
  if p.val = (true, vertices_770) then 7 else
  if p.val = (true, vertices_340) then 19 else
  if p.val = (true, vertices_388) then 8 else
  if p.val = (true, vertices_536) then 9 else
  if p.val = (true, vertices_112) then 10 else
  if p.val = (true, vertices_560) then 11 else
  if p.val = (true, vertices_208) then 12 else
  if p.val = (true, vertices_400) then 13 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_293), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_645), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_82), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_146), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_274), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_530), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_386), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_770), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_388), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_536), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_112), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_560), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_208), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_400), by decide +kernel⟩
  | 14 => Sum.inl 0
  | 15 => Sum.inr ⟨(false, vertices_707), by decide +kernel⟩
  | 16 => Sum.inl 1
  | 17 => Sum.inr ⟨(false, vertices_781), by decide +kernel⟩
  | 18 => Sum.inr ⟨(false, vertices_229), by decide +kernel⟩
  | 19 => Sum.inr ⟨(true, vertices_340), by decide +kernel⟩
  | 20 => Sum.inl 2
  | 21 => Sum.inr ⟨(false, vertices_313), by decide +kernel⟩
  | 22 => Sum.inr ⟨(false, vertices_617), by decide +kernel⟩
  | 23 => Sum.inl 3
  | 24 => Sum.inl 4
  | 25 => Sum.inl 5
  | 26 => Sum.inl 6
  | 27 => Sum.inl 7
  | 28 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 6 7 8 902 386 1
cert_row_2 1 1 3 5 7 340
cert_row_4 2 0 2 3 7 8 794 274 1
cert_row_4 3 0 3 4 5 8 626 82 2
cert_rows
cert_pivot_2 6 1 2 0
cert_heightProof 4
cert_coverFacet 0 902
cert_cover_5 0 0 0 1 6 7 386 902 1
cert_coverFacet 1 794
cert_cover_5 1 2 0 2 3 7 274 794 1
cert_coverFacet 2 626
cert_cover_5 2 3 0 3 4 5 82 626 2
cert_coverFacet 3 210
cert_cover_2 3 3 0 5 6 82 210 3
cert_coverFacet 4 402
cert_cover_2 4 3 0 6 7 146 402 3
cert_coverFacet 5 372
cert_cover_5 5 1 1 3 4 5 340 372 2
cert_coverFacet 6 468
cert_cover_5 6 1 1 3 5 6 340 468 3
cert_coverFacet 7 568
cert_cover_2 7 3 2 4 8 56 568 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0407

end
end BundlePart11

section BundlePart12
/- Source: ProjectionCertificates/R_m15e10q1_0408.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0408

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [659, 789, 681, 433, 865, 86, 534, 838, 714, 210, 220, 412, 364, 616, 424, 145, 273, 529, 161, 289, 545, 641, 769, 22, 70, 518, 82, 146, 530, 194, 578, 642, 156, 76, 268, 84, 276, 532, 324, 772, 104, 168, 296, 552, 200, 584, 392, 648, 208, 400, 352, 608, 416, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_659, vertices_789, vertices_681, vertices_433, vertices_865, vertices_86, vertices_534, vertices_838, vertices_714, vertices_210, vertices_220, vertices_412, vertices_364, vertices_616, vertices_424] (by decide +kernel)
  polygons := literalFinset [vertices_145, vertices_273, vertices_529, vertices_161, vertices_289, vertices_545, vertices_641, vertices_769, vertices_22, vertices_70, vertices_518, vertices_82, vertices_146, vertices_530, vertices_194, vertices_578, vertices_642, vertices_156, vertices_76, vertices_268, vertices_84, vertices_276, vertices_532, vertices_324, vertices_772, vertices_104, vertices_168, vertices_296, vertices_552, vertices_200, vertices_584, vertices_392, vertices_648, vertices_208, vertices_400, vertices_352, vertices_608, vertices_416, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_659), (false, vertices_789), (false, vertices_681), (false, vertices_433), (false, vertices_865), (true, vertices_22), (true, vertices_70), (true, vertices_518), (true, vertices_82), (true, vertices_194), (true, vertices_578), (true, vertices_156), (true, vertices_76), (true, vertices_268), (true, vertices_84), (true, vertices_324), (true, vertices_104), (true, vertices_296), (true, vertices_200), (true, vertices_584), (true, vertices_392), (true, vertices_208)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 16 18 21 23 25 27 28 29 30
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_659) then 17 else
  if p.val = (false, vertices_789) then 19 else
  if p.val = (false, vertices_681) then 22 else
  if p.val = (false, vertices_433) then 24 else
  if p.val = (false, vertices_865) then 26 else
  if p.val = (true, vertices_22) then 0 else
  if p.val = (true, vertices_70) then 1 else
  if p.val = (true, vertices_518) then 2 else
  if p.val = (true, vertices_82) then 3 else
  if p.val = (true, vertices_194) then 4 else
  if p.val = (true, vertices_578) then 5 else
  if p.val = (true, vertices_156) then 20 else
  if p.val = (true, vertices_76) then 6 else
  if p.val = (true, vertices_268) then 7 else
  if p.val = (true, vertices_84) then 8 else
  if p.val = (true, vertices_324) then 9 else
  if p.val = (true, vertices_104) then 10 else
  if p.val = (true, vertices_296) then 11 else
  if p.val = (true, vertices_200) then 12 else
  if p.val = (true, vertices_584) then 13 else
  if p.val = (true, vertices_392) then 14 else
  if p.val = (true, vertices_208) then 15 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_22), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_70), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_518), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_82), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_194), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_578), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_76), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_268), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_84), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_324), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_104), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_296), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_200), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_584), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_392), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_208), by decide +kernel⟩
  | 16 => Sum.inl 0
  | 17 => Sum.inr ⟨(false, vertices_659), by decide +kernel⟩
  | 18 => Sum.inl 1
  | 19 => Sum.inr ⟨(false, vertices_789), by decide +kernel⟩
  | 20 => Sum.inr ⟨(true, vertices_156), by decide +kernel⟩
  | 21 => Sum.inl 2
  | 22 => Sum.inr ⟨(false, vertices_681), by decide +kernel⟩
  | 23 => Sum.inl 3
  | 24 => Sum.inr ⟨(false, vertices_433), by decide +kernel⟩
  | 25 => Sum.inl 4
  | 26 => Sum.inr ⟨(false, vertices_865), by decide +kernel⟩
  | 27 => Sum.inl 5
  | 28 => Sum.inl 6
  | 29 => Sum.inl 7
  | 30 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 1 2 3 6 156
cert_row_4 1 0 2 5 6 8 714 194 1
cert_row_4 2 0 1 5 7 8 838 70 3
cert_row_4 3 1 2 4 5 7 364 76 2
cert_rows
cert_pivot_2 3 6 0 1
cert_heightProof 4
cert_coverFacet 0 86
cert_cover_2 0 1 0 3 5 22 86 3
cert_coverFacet 1 534
cert_cover_2 1 1 0 3 8 22 534 3
cert_coverFacet 2 838
cert_cover_5 2 2 0 1 5 7 70 838 3
cert_coverFacet 3 714
cert_cover_5 3 1 0 2 5 6 194 714 1
cert_coverFacet 4 210
cert_cover_2 4 3 0 5 6 82 210 3
cert_coverFacet 5 220
cert_cover_5 5 0 1 2 3 5 156 220 3
cert_coverFacet 6 412
cert_cover_5 6 0 1 2 3 7 156 412 3
cert_coverFacet 7 364
cert_cover_5 7 3 1 2 4 5 76 364 2
cert_coverFacet 8 616
cert_cover_2 8 4 2 5 8 104 616 3
cert_coverFacet 9 424
cert_cover_2 9 4 2 6 7 168 424 3
cert_coveringFacets_5
cert_coveringProof
cert_certificate 4 10
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0408

end
end BundlePart12

section BundlePart13
/- Source: ProjectionCertificates/R_m15e10q1_0409.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0409

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [339, 653, 213, 533, 569, 361, 201, 305, 566, 86, 454, 902, 810, 306, 968, 21, 133, 517, 41, 73, 137, 521, 49, 81, 273, 529, 289, 193, 321, 22, 70, 390, 518, 50, 82, 274, 290, 546, 322, 770, 84, 532, 196, 644, 296, 552, 200, 328, 648, 776, 304, 560, 448, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_339, vertices_653, vertices_213, vertices_533, vertices_569, vertices_361, vertices_201, vertices_305, vertices_566, vertices_86, vertices_454, vertices_902, vertices_810, vertices_306, vertices_968] (by decide +kernel)
  polygons := literalFinset [vertices_21, vertices_133, vertices_517, vertices_41, vertices_73, vertices_137, vertices_521, vertices_49, vertices_81, vertices_273, vertices_529, vertices_289, vertices_193, vertices_321, vertices_22, vertices_70, vertices_390, vertices_518, vertices_50, vertices_82, vertices_274, vertices_290, vertices_546, vertices_322, vertices_770, vertices_84, vertices_532, vertices_196, vertices_644, vertices_296, vertices_552, vertices_200, vertices_328, vertices_648, vertices_776, vertices_304, vertices_560, vertices_448, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_339), (false, vertices_653), (false, vertices_213), (false, vertices_533), (false, vertices_569), (false, vertices_361), (false, vertices_201), (false, vertices_305), (true, vertices_22), (true, vertices_70), (true, vertices_390), (true, vertices_518), (true, vertices_50), (true, vertices_290), (true, vertices_546), (true, vertices_770), (true, vertices_776), (true, vertices_448), (true, vertices_896)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 13 16 19 22 23 24 25 26 27
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_339) then 14 else
  if p.val = (false, vertices_653) then 17 else
  if p.val = (false, vertices_213) then 18 else
  if p.val = (false, vertices_533) then 0 else
  if p.val = (false, vertices_569) then 20 else
  if p.val = (false, vertices_361) then 21 else
  if p.val = (false, vertices_201) then 1 else
  if p.val = (false, vertices_305) then 2 else
  if p.val = (true, vertices_22) then 3 else
  if p.val = (true, vertices_70) then 4 else
  if p.val = (true, vertices_390) then 15 else
  if p.val = (true, vertices_518) then 5 else
  if p.val = (true, vertices_50) then 6 else
  if p.val = (true, vertices_290) then 7 else
  if p.val = (true, vertices_546) then 8 else
  if p.val = (true, vertices_770) then 9 else
  if p.val = (true, vertices_776) then 10 else
  if p.val = (true, vertices_448) then 11 else
  if p.val = (true, vertices_896) then 12 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_533), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_201), by decide +kernel⟩
  | 2 => Sum.inr ⟨(false, vertices_305), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_22), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_70), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_518), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_50), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_290), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_546), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_770), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_776), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_448), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_896), by decide +kernel⟩
  | 13 => Sum.inl 0
  | 14 => Sum.inr ⟨(false, vertices_339), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_390), by decide +kernel⟩
  | 16 => Sum.inl 1
  | 17 => Sum.inr ⟨(false, vertices_653), by decide +kernel⟩
  | 18 => Sum.inr ⟨(false, vertices_213), by decide +kernel⟩
  | 19 => Sum.inl 2
  | 20 => Sum.inr ⟨(false, vertices_569), by decide +kernel⟩
  | 21 => Sum.inr ⟨(false, vertices_361), by decide +kernel⟩
  | 22 => Sum.inl 3
  | 23 => Sum.inl 4
  | 24 => Sum.inl 5
  | 25 => Sum.inl 6
  | 26 => Sum.inl 7
  | 27 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 3 4 8 566 22 3
cert_row_2 1 0 1 6 7 390
cert_row_4 2 0 2 4 7 8 810 290 1
cert_row_4 3 2 5 6 7 8 968 200 3
cert_rows
cert_pivot_2 3 1 0 2
cert_heightProof 4
cert_coverFacet 0 566
cert_cover_5 0 0 0 1 3 4 22 566 3
cert_coverFacet 1 86
cert_cover_2 1 1 0 3 5 22 86 3
cert_coverFacet 2 454
cert_cover_5 2 1 0 1 5 6 70 454 3
cert_coverFacet 3 902
cert_cover_5 3 1 0 1 6 8 390 902 3
cert_coverFacet 4 810
cert_cover_5 4 2 0 2 4 7 290 810 1
cert_coverFacet 5 306
cert_cover_2 5 3 0 4 7 50 306 3
cert_coverFacet 6 968
cert_cover_5 6 3 2 5 6 7 200 968 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0409

end
end BundlePart13

section BundlePart14
/- Source: ProjectionCertificates/R_m15e10q1_0411.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0411

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [451, 677, 809, 713, 329, 433, 94, 182, 198, 794, 330, 402, 604, 820, 708, 73, 265, 521, 161, 289, 545, 193, 321, 385, 641, 22, 70, 134, 26, 74, 266, 146, 274, 194, 322, 386, 92, 52, 532, 164, 548, 196, 580, 644, 536, 328, 584, 776, 176, 304, 400, 784, 800, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_451, vertices_677, vertices_809, vertices_713, vertices_329, vertices_433, vertices_94, vertices_182, vertices_198, vertices_794, vertices_330, vertices_402, vertices_604, vertices_820, vertices_708] (by decide +kernel)
  polygons := literalFinset [vertices_73, vertices_265, vertices_521, vertices_161, vertices_289, vertices_545, vertices_193, vertices_321, vertices_385, vertices_641, vertices_22, vertices_70, vertices_134, vertices_26, vertices_74, vertices_266, vertices_146, vertices_274, vertices_194, vertices_322, vertices_386, vertices_92, vertices_52, vertices_532, vertices_164, vertices_548, vertices_196, vertices_580, vertices_644, vertices_536, vertices_328, vertices_584, vertices_776, vertices_176, vertices_304, vertices_400, vertices_784, vertices_800, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_451), (false, vertices_677), (false, vertices_809), (false, vertices_713), (false, vertices_329), (false, vertices_433), (true, vertices_22), (true, vertices_70), (true, vertices_134), (true, vertices_26), (true, vertices_74), (true, vertices_266), (true, vertices_146), (true, vertices_274), (true, vertices_92), (true, vertices_52), (true, vertices_532), (true, vertices_196), (true, vertices_580), (true, vertices_536), (true, vertices_784)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 17 20 23 25 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_451) then 16 else
  if p.val = (false, vertices_677) then 18 else
  if p.val = (false, vertices_809) then 21 else
  if p.val = (false, vertices_713) then 22 else
  if p.val = (false, vertices_329) then 0 else
  if p.val = (false, vertices_433) then 24 else
  if p.val = (true, vertices_22) then 1 else
  if p.val = (true, vertices_70) then 2 else
  if p.val = (true, vertices_134) then 3 else
  if p.val = (true, vertices_26) then 4 else
  if p.val = (true, vertices_74) then 5 else
  if p.val = (true, vertices_266) then 6 else
  if p.val = (true, vertices_146) then 7 else
  if p.val = (true, vertices_274) then 8 else
  if p.val = (true, vertices_92) then 19 else
  if p.val = (true, vertices_52) then 9 else
  if p.val = (true, vertices_532) then 10 else
  if p.val = (true, vertices_196) then 11 else
  if p.val = (true, vertices_580) then 12 else
  if p.val = (true, vertices_536) then 13 else
  if p.val = (true, vertices_784) then 14 else
  0
cert_priority
cert_nodeAtPriority_65 329 2 22 1 70 3 134 26 74 266 146 274 52 532 196 580 536 784 451 677 92 809 713 433
cert_priority_injective
cert_incidenceProof
cert_row_2 0 1 2 3 5 92
cert_row_4 1 0 1 3 4 6 182 22 3
cert_row_4 2 0 2 3 7 8 794 26 3
cert_row_4 3 1 3 4 7 8 820 52 3
cert_rows
cert_pivot_2 5 6 0 1
cert_heightProof 4
cert_coverFacet 0 94
cert_cover_5 0 0 0 1 2 3 22 94 2
cert_coverFacet 1 182
cert_cover_5 1 1 0 1 3 4 22 182 3
cert_coverFacet 2 198
cert_cover_2 2 1 0 5 6 70 198 3
cert_coverFacet 3 794
cert_cover_5 3 2 0 2 3 7 26 794 3
cert_coverFacet 4 330
cert_cover_2 4 2 0 5 7 74 330 3
cert_coverFacet 5 402
cert_cover_2 5 3 0 6 7 146 402 3
cert_coverFacet 6 604
cert_cover_5 6 0 1 2 3 8 92 604 3
cert_coverFacet 7 820
cert_cover_5 7 3 1 3 4 7 52 820 3
cert_coverFacet 8 708
cert_cover_2 8 5 1 6 8 196 708 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0411

end
end BundlePart14

section BundlePart15
/- Source: ProjectionCertificates/R_m15e10q1_0412.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0412

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [803, 205, 677, 837, 465, 417, 334, 782, 90, 538, 370, 690, 668, 216, 432, 69, 133, 517, 161, 289, 545, 193, 321, 385, 769, 270, 26, 74, 522, 50, 82, 530, 290, 546, 322, 770, 76, 140, 524, 324, 644, 772, 88, 152, 536, 200, 176, 304, 208, 336, 400, 656, 416, 672]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_803, vertices_205, vertices_677, vertices_837, vertices_465, vertices_417, vertices_334, vertices_782, vertices_90, vertices_538, vertices_370, vertices_690, vertices_668, vertices_216, vertices_432] (by decide +kernel)
  polygons := literalFinset [vertices_69, vertices_133, vertices_517, vertices_161, vertices_289, vertices_545, vertices_193, vertices_321, vertices_385, vertices_769, vertices_270, vertices_26, vertices_74, vertices_522, vertices_50, vertices_82, vertices_530, vertices_290, vertices_546, vertices_322, vertices_770, vertices_76, vertices_140, vertices_524, vertices_324, vertices_644, vertices_772, vertices_88, vertices_152, vertices_536, vertices_200, vertices_176, vertices_304, vertices_208, vertices_336, vertices_400, vertices_656, vertices_416, vertices_672] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_803), (false, vertices_205), (false, vertices_677), (false, vertices_837), (false, vertices_465), (false, vertices_417), (true, vertices_270), (true, vertices_26), (true, vertices_74), (true, vertices_522), (true, vertices_50), (true, vertices_82), (true, vertices_530), (true, vertices_322), (true, vertices_524), (true, vertices_88), (true, vertices_152), (true, vertices_536), (true, vertices_176), (true, vertices_304), (true, vertices_656)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 18 22 23 25 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_803) then 16 else
  if p.val = (false, vertices_205) then 19 else
  if p.val = (false, vertices_677) then 20 else
  if p.val = (false, vertices_837) then 21 else
  if p.val = (false, vertices_465) then 24 else
  if p.val = (false, vertices_417) then 0 else
  if p.val = (true, vertices_270) then 17 else
  if p.val = (true, vertices_26) then 1 else
  if p.val = (true, vertices_74) then 2 else
  if p.val = (true, vertices_522) then 3 else
  if p.val = (true, vertices_50) then 4 else
  if p.val = (true, vertices_82) then 5 else
  if p.val = (true, vertices_530) then 6 else
  if p.val = (true, vertices_322) then 7 else
  if p.val = (true, vertices_524) then 8 else
  if p.val = (true, vertices_88) then 9 else
  if p.val = (true, vertices_152) then 10 else
  if p.val = (true, vertices_536) then 11 else
  if p.val = (true, vertices_176) then 12 else
  if p.val = (true, vertices_304) then 13 else
  if p.val = (true, vertices_656) then 14 else
  0
cert_priority
cert_nodeAtPriority_19 0 417 1 26 74 522 50 82 530 322 524 88 152 536 176 304 656 803 270 205 677 837 465
cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 3 4 5 7 370 50 3
cert_row_2 1 0 1 2 7 270
cert_row_4 2 0 3 4 6 8 690 50 3
cert_row_4 3 1 2 3 6 8 668 140 2
cert_rows
cert_pivot_2 5 7 0 1
cert_heightProof 4
cert_coverFacet 0 334
cert_cover_5 0 1 0 1 2 5 270 334 3
cert_coverFacet 1 782
cert_cover_5 1 1 0 1 2 8 270 782 3
cert_coverFacet 2 90
cert_cover_2 2 2 0 3 5 26 90 3
cert_coverFacet 3 538
cert_cover_2 3 2 0 3 8 26 538 3
cert_coverFacet 4 370
cert_cover_5 4 0 0 3 4 5 50 370 3
cert_coverFacet 5 690
cert_cover_5 5 2 0 3 4 6 50 690 3
cert_coverFacet 6 668
cert_cover_5 6 3 1 2 3 6 140 668 2
cert_coverFacet 7 216
cert_cover_2 7 3 2 5 6 88 216 3
cert_coverFacet 8 432
cert_cover_2 8 4 3 6 7 176 432 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0412

end
end BundlePart15

section BundlePart16
/- Source: ProjectionCertificates/R_m15e10q1_0413.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0413

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [707, 61, 597, 677, 305, 337, 481, 94, 590, 282, 778, 466, 930, 812, 312, 21, 37, 517, 49, 81, 273, 161, 289, 193, 321, 577, 641, 78, 26, 266, 522, 82, 274, 194, 578, 386, 642, 770, 28, 44, 524, 84, 548, 580, 56, 280, 296, 776, 304, 336, 416, 672, 800, 448]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_707, vertices_61, vertices_597, vertices_677, vertices_305, vertices_337, vertices_481, vertices_94, vertices_590, vertices_282, vertices_778, vertices_466, vertices_930, vertices_812, vertices_312] (by decide +kernel)
  polygons := literalFinset [vertices_21, vertices_37, vertices_517, vertices_49, vertices_81, vertices_273, vertices_161, vertices_289, vertices_193, vertices_321, vertices_577, vertices_641, vertices_78, vertices_26, vertices_266, vertices_522, vertices_82, vertices_274, vertices_194, vertices_578, vertices_386, vertices_642, vertices_770, vertices_28, vertices_44, vertices_524, vertices_84, vertices_548, vertices_580, vertices_56, vertices_280, vertices_296, vertices_776, vertices_304, vertices_336, vertices_416, vertices_672, vertices_800, vertices_448] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_707), (false, vertices_61), (false, vertices_597), (false, vertices_677), (false, vertices_305), (false, vertices_337), (false, vertices_481), (true, vertices_78), (true, vertices_26), (true, vertices_266), (true, vertices_522), (true, vertices_82), (true, vertices_274), (true, vertices_386), (true, vertices_770), (true, vertices_524), (true, vertices_280), (true, vertices_296), (true, vertices_776), (true, vertices_800)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 14 17 21 22 23 25 26 27 28
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_707) then 15 else
  if p.val = (false, vertices_61) then 18 else
  if p.val = (false, vertices_597) then 19 else
  if p.val = (false, vertices_677) then 20 else
  if p.val = (false, vertices_305) then 0 else
  if p.val = (false, vertices_337) then 1 else
  if p.val = (false, vertices_481) then 24 else
  if p.val = (true, vertices_78) then 16 else
  if p.val = (true, vertices_26) then 2 else
  if p.val = (true, vertices_266) then 3 else
  if p.val = (true, vertices_522) then 4 else
  if p.val = (true, vertices_82) then 5 else
  if p.val = (true, vertices_274) then 6 else
  if p.val = (true, vertices_386) then 7 else
  if p.val = (true, vertices_770) then 8 else
  if p.val = (true, vertices_524) then 9 else
  if p.val = (true, vertices_280) then 10 else
  if p.val = (true, vertices_296) then 11 else
  if p.val = (true, vertices_776) then 12 else
  if p.val = (true, vertices_800) then 13 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_305), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_337), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_26), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_266), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_522), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_82), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_274), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_386), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_770), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_524), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_280), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_296), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_776), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_800), by decide +kernel⟩
  | 14 => Sum.inl 0
  | 15 => Sum.inr ⟨(false, vertices_707), by decide +kernel⟩
  | 16 => Sum.inr ⟨(true, vertices_78), by decide +kernel⟩
  | 17 => Sum.inl 1
  | 18 => Sum.inr ⟨(false, vertices_61), by decide +kernel⟩
  | 19 => Sum.inr ⟨(false, vertices_597), by decide +kernel⟩
  | 20 => Sum.inr ⟨(false, vertices_677), by decide +kernel⟩
  | 21 => Sum.inl 2
  | 22 => Sum.inl 3
  | 23 => Sum.inl 4
  | 24 => Sum.inr ⟨(false, vertices_481), by decide +kernel⟩
  | 25 => Sum.inl 5
  | 26 => Sum.inl 6
  | 27 => Sum.inl 7
  | 28 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 3 5 6 7 466 82 3
cert_row_2 1 0 1 2 5 78
cert_row_4 2 0 4 6 7 8 930 386 1
cert_row_4 3 1 2 4 7 8 812 44 3
cert_rows
cert_pivot_2 3 5 0 1
cert_heightProof 4
cert_coverFacet 0 94
cert_cover_5 0 1 0 1 2 3 78 94 3
cert_coverFacet 1 590
cert_cover_5 1 1 0 1 2 8 78 590 3
cert_coverFacet 2 282
cert_cover_2 2 2 0 3 7 26 282 3
cert_coverFacet 3 778
cert_cover_2 3 2 0 7 8 266 778 3
cert_coverFacet 4 466
cert_cover_5 4 0 0 3 5 6 82 466 3
cert_coverFacet 5 930
cert_cover_5 5 2 0 4 6 7 386 930 1
cert_coverFacet 6 812
cert_cover_5 6 3 1 2 4 7 44 812 3
cert_coverFacet 7 312
cert_cover_2 7 3 2 4 7 56 312 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0413

end
end BundlePart16

section BundlePart17
/- Source: ProjectionCertificates/R_m15e10q1_0414.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0414

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [403, 661, 421, 549, 793, 865, 206, 654, 346, 538, 658, 482, 620, 228, 840, 37, 133, 517, 145, 273, 529, 289, 545, 385, 769, 142, 26, 74, 522, 146, 274, 530, 194, 322, 386, 642, 76, 524, 100, 164, 548, 196, 644, 280, 536, 328, 584, 776, 656, 224, 352, 608, 416, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_403, vertices_661, vertices_421, vertices_549, vertices_793, vertices_865, vertices_206, vertices_654, vertices_346, vertices_538, vertices_658, vertices_482, vertices_620, vertices_228, vertices_840] (by decide +kernel)
  polygons := literalFinset [vertices_37, vertices_133, vertices_517, vertices_145, vertices_273, vertices_529, vertices_289, vertices_545, vertices_385, vertices_769, vertices_142, vertices_26, vertices_74, vertices_522, vertices_146, vertices_274, vertices_530, vertices_194, vertices_322, vertices_386, vertices_642, vertices_76, vertices_524, vertices_100, vertices_164, vertices_548, vertices_196, vertices_644, vertices_280, vertices_536, vertices_328, vertices_584, vertices_776, vertices_656, vertices_224, vertices_352, vertices_608, vertices_416, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_403), (false, vertices_661), (false, vertices_421), (false, vertices_549), (false, vertices_793), (false, vertices_865), (true, vertices_142), (true, vertices_26), (true, vertices_74), (true, vertices_522), (true, vertices_530), (true, vertices_194), (true, vertices_322), (true, vertices_642), (true, vertices_76), (true, vertices_524), (true, vertices_100), (true, vertices_196), (true, vertices_328), (true, vertices_584), (true, vertices_224)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 18 21 23 24 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_403) then 16 else
  if p.val = (false, vertices_661) then 19 else
  if p.val = (false, vertices_421) then 20 else
  if p.val = (false, vertices_549) then 0 else
  if p.val = (false, vertices_793) then 22 else
  if p.val = (false, vertices_865) then 25 else
  if p.val = (true, vertices_142) then 17 else
  if p.val = (true, vertices_26) then 1 else
  if p.val = (true, vertices_74) then 2 else
  if p.val = (true, vertices_522) then 3 else
  if p.val = (true, vertices_530) then 4 else
  if p.val = (true, vertices_194) then 5 else
  if p.val = (true, vertices_322) then 6 else
  if p.val = (true, vertices_642) then 7 else
  if p.val = (true, vertices_76) then 8 else
  if p.val = (true, vertices_524) then 9 else
  if p.val = (true, vertices_100) then 10 else
  if p.val = (true, vertices_196) then 11 else
  if p.val = (true, vertices_328) then 12 else
  if p.val = (true, vertices_584) then 13 else
  if p.val = (true, vertices_224) then 14 else
  0
cert_priority
cert_nodeAtPriority_34 549 26 74 522 530 194 322 642 76 524 100 196 328 584 224 403 142 661 421 793 865
cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 2 3 5 7 346 26 3
cert_row_4 1 0 4 5 6 7 482 194 1
cert_row_2 2 0 1 2 6 142
cert_row_4 3 1 2 4 5 8 620 76 2
cert_rows
cert_pivot_2 3 7 0 1
cert_heightProof 4
cert_coverFacet 0 206
cert_cover_5 0 2 0 1 2 5 142 206 3
cert_coverFacet 1 654
cert_cover_5 1 2 0 1 2 8 142 654 3
cert_coverFacet 2 346
cert_cover_5 2 0 0 2 3 5 26 346 3
cert_coverFacet 3 538
cert_cover_2 3 2 0 3 8 26 538 3
cert_coverFacet 4 658
cert_cover_2 4 3 0 6 8 146 658 3
cert_coverFacet 5 482
cert_cover_5 5 1 0 4 5 6 194 482 1
cert_coverFacet 6 620
cert_cover_5 6 3 1 2 4 5 76 620 2
cert_coverFacet 7 228
cert_cover_2 7 4 1 5 6 100 228 3
cert_coverFacet 8 840
cert_cover_2 8 5 2 7 8 328 840 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0414

end
end BundlePart17

section BundlePart18
/- Source: ProjectionCertificates/R_m15e10q1_0415.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0415

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [707, 837, 681, 177, 817, 465, 30, 590, 406, 454, 186, 650, 284, 812, 312, 49, 145, 273, 161, 545, 193, 321, 577, 641, 769, 14, 22, 70, 390, 26, 138, 522, 146, 194, 578, 642, 28, 268, 524, 276, 324, 580, 772, 56, 280, 168, 296, 552, 648, 176, 304, 400, 800, 448]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_707, vertices_837, vertices_681, vertices_177, vertices_817, vertices_465, vertices_30, vertices_590, vertices_406, vertices_454, vertices_186, vertices_650, vertices_284, vertices_812, vertices_312] (by decide +kernel)
  polygons := literalFinset [vertices_49, vertices_145, vertices_273, vertices_161, vertices_545, vertices_193, vertices_321, vertices_577, vertices_641, vertices_769, vertices_14, vertices_22, vertices_70, vertices_390, vertices_26, vertices_138, vertices_522, vertices_146, vertices_194, vertices_578, vertices_642, vertices_28, vertices_268, vertices_524, vertices_276, vertices_324, vertices_580, vertices_772, vertices_56, vertices_280, vertices_168, vertices_296, vertices_552, vertices_648, vertices_176, vertices_304, vertices_400, vertices_800, vertices_448] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_707), (false, vertices_837), (false, vertices_681), (false, vertices_177), (false, vertices_817), (false, vertices_465), (true, vertices_14), (true, vertices_22), (true, vertices_70), (true, vertices_390), (true, vertices_26), (true, vertices_138), (true, vertices_522), (true, vertices_146), (true, vertices_28), (true, vertices_268), (true, vertices_524), (true, vertices_276), (true, vertices_56), (true, vertices_280), (true, vertices_296)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 18 20 22 25 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_707) then 16 else
  if p.val = (false, vertices_837) then 19 else
  if p.val = (false, vertices_681) then 21 else
  if p.val = (false, vertices_177) then 0 else
  if p.val = (false, vertices_817) then 23 else
  if p.val = (false, vertices_465) then 24 else
  if p.val = (true, vertices_14) then 1 else
  if p.val = (true, vertices_22) then 2 else
  if p.val = (true, vertices_70) then 3 else
  if p.val = (true, vertices_390) then 17 else
  if p.val = (true, vertices_26) then 4 else
  if p.val = (true, vertices_138) then 5 else
  if p.val = (true, vertices_522) then 6 else
  if p.val = (true, vertices_146) then 7 else
  if p.val = (true, vertices_28) then 8 else
  if p.val = (true, vertices_268) then 9 else
  if p.val = (true, vertices_524) then 10 else
  if p.val = (true, vertices_276) then 11 else
  if p.val = (true, vertices_56) then 12 else
  if p.val = (true, vertices_280) then 13 else
  if p.val = (true, vertices_296) then 14 else
  0
cert_priority
cert_nodeAtPriority_40 177 14 22 70 26 138 522 146 28 268 524 276 56 280 296 707 390 837 681 817 465
cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 2 5 8 590 14 3
cert_row_4 1 0 2 3 4 6 186 26 3
cert_row_2 2 0 1 6 7 390
cert_row_4 3 1 2 4 7 8 812 268 2
cert_rows
cert_pivot_2 5 3 0 1
cert_heightProof 4
cert_coverFacet 0 30
cert_cover_2 0 1 0 2 3 14 30 3
cert_coverFacet 1 590
cert_cover_5 1 0 0 1 2 5 14 590 3
cert_coverFacet 2 406
cert_cover_5 2 2 0 1 3 6 22 406 3
cert_coverFacet 3 454
cert_cover_5 3 2 0 1 5 6 70 454 3
cert_coverFacet 4 186
cert_cover_5 4 1 0 2 3 4 26 186 3
cert_coverFacet 5 650
cert_cover_2 5 2 0 6 8 138 650 3
cert_coverFacet 6 284
cert_cover_2 6 2 1 3 7 28 284 3
cert_coverFacet 7 812
cert_cover_5 7 3 1 2 4 7 268 812 2
cert_coverFacet 8 312
cert_cover_2 8 3 2 4 7 56 312 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0415

end
end BundlePart18

section BundlePart19
/- Source: ProjectionCertificates/R_m15e10q1_0416.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0416

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [179, 565, 597, 345, 617, 425, 401, 54, 342, 678, 774, 906, 402, 844, 680, 533, 41, 73, 265, 49, 81, 145, 273, 161, 545, 577, 385, 22, 38, 262, 518, 50, 146, 274, 162, 386, 642, 770, 52, 84, 548, 324, 580, 772, 168, 552, 328, 584, 392, 648, 776, 336, 400, 672]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_179, vertices_565, vertices_597, vertices_345, vertices_617, vertices_425, vertices_401, vertices_54, vertices_342, vertices_678, vertices_774, vertices_906, vertices_402, vertices_844, vertices_680] (by decide +kernel)
  polygons := literalFinset [vertices_533, vertices_41, vertices_73, vertices_265, vertices_49, vertices_81, vertices_145, vertices_273, vertices_161, vertices_545, vertices_577, vertices_385, vertices_22, vertices_38, vertices_262, vertices_518, vertices_50, vertices_146, vertices_274, vertices_162, vertices_386, vertices_642, vertices_770, vertices_52, vertices_84, vertices_548, vertices_324, vertices_580, vertices_772, vertices_168, vertices_552, vertices_328, vertices_584, vertices_392, vertices_648, vertices_776, vertices_336, vertices_400, vertices_672] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_179), (false, vertices_565), (false, vertices_597), (false, vertices_345), (false, vertices_617), (false, vertices_425), (false, vertices_401), (true, vertices_22), (true, vertices_38), (true, vertices_262), (true, vertices_518), (true, vertices_274), (true, vertices_386), (true, vertices_642), (true, vertices_770), (true, vertices_324), (true, vertices_772), (true, vertices_648), (true, vertices_776), (true, vertices_672)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 14 16 19 23 24 25 26 27 28
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_179) then 15 else
  if p.val = (false, vertices_565) then 17 else
  if p.val = (false, vertices_597) then 18 else
  if p.val = (false, vertices_345) then 20 else
  if p.val = (false, vertices_617) then 21 else
  if p.val = (false, vertices_425) then 22 else
  if p.val = (false, vertices_401) then 0 else
  if p.val = (true, vertices_22) then 1 else
  if p.val = (true, vertices_38) then 2 else
  if p.val = (true, vertices_262) then 3 else
  if p.val = (true, vertices_518) then 4 else
  if p.val = (true, vertices_274) then 5 else
  if p.val = (true, vertices_386) then 6 else
  if p.val = (true, vertices_642) then 7 else
  if p.val = (true, vertices_770) then 8 else
  if p.val = (true, vertices_324) then 9 else
  if p.val = (true, vertices_772) then 10 else
  if p.val = (true, vertices_648) then 11 else
  if p.val = (true, vertices_776) then 12 else
  if p.val = (true, vertices_672) then 13 else
  0
cert_priority
cert_nodeAtPriority_48 0 401 2 22 1 38 262 518 274 386 642 770 324 772 648 776 672 179 565 597 345 617 425
cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 3 5 7 342 22 3
cert_row_4 1 0 1 4 6 8 678 38 3
cert_row_4 2 0 2 6 7 8 906 386 1
cert_row_4 3 1 2 5 7 8 844 324 1
cert_rows
cert_pivot_2 3 4 0 1
cert_heightProof 4
cert_coverFacet 0 54
cert_cover_2 0 1 0 3 4 22 54 3
cert_coverFacet 1 342
cert_cover_5 1 0 0 1 3 5 22 342 3
cert_coverFacet 2 678
cert_cover_5 2 1 0 1 4 6 38 678 3
cert_coverFacet 3 774
cert_cover_2 3 1 0 7 8 262 774 3
cert_coverFacet 4 906
cert_cover_5 4 2 0 2 6 7 386 906 1
cert_coverFacet 5 402
cert_cover_2 5 3 0 6 7 146 402 3
cert_coverFacet 6 844
cert_cover_5 6 3 1 2 5 7 324 844 1
cert_coverFacet 7 680
cert_cover_2 7 4 2 6 8 168 680 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0416

end
end BundlePart19

section BundlePart20
/- Source: ProjectionCertificates/R_m15e10q1_0417.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0417

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [283, 203, 611, 771, 789, 153, 721, 806, 330, 354, 668, 284, 428, 740, 488, 11, 67, 259, 515, 25, 137, 145, 273, 529, 193, 577, 769, 74, 266, 98, 290, 546, 322, 770, 28, 140, 268, 276, 532, 164, 292, 548, 644, 772, 152, 280, 424, 200, 328, 656, 224, 352, 608, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_283, vertices_203, vertices_611, vertices_771, vertices_789, vertices_153, vertices_721, vertices_806, vertices_330, vertices_354, vertices_668, vertices_284, vertices_428, vertices_740, vertices_488] (by decide +kernel)
  polygons := literalFinset [vertices_11, vertices_67, vertices_259, vertices_515, vertices_25, vertices_137, vertices_145, vertices_273, vertices_529, vertices_193, vertices_577, vertices_769, vertices_74, vertices_266, vertices_98, vertices_290, vertices_546, vertices_322, vertices_770, vertices_28, vertices_140, vertices_268, vertices_276, vertices_532, vertices_164, vertices_292, vertices_548, vertices_644, vertices_772, vertices_152, vertices_280, vertices_424, vertices_200, vertices_328, vertices_656, vertices_224, vertices_352, vertices_608, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_283), (false, vertices_203), (false, vertices_611), (false, vertices_771), (false, vertices_789), (false, vertices_153), (false, vertices_721), (true, vertices_290), (true, vertices_322), (true, vertices_28), (true, vertices_140), (true, vertices_268), (true, vertices_164), (true, vertices_292), (true, vertices_548), (true, vertices_644), (true, vertices_424), (true, vertices_328), (true, vertices_224), (true, vertices_352)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 14 18 20 22 24 25 26 27 28
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_283) then 15 else
  if p.val = (false, vertices_203) then 16 else
  if p.val = (false, vertices_611) then 17 else
  if p.val = (false, vertices_771) then 0 else
  if p.val = (false, vertices_789) then 19 else
  if p.val = (false, vertices_153) then 1 else
  if p.val = (false, vertices_721) then 23 else
  if p.val = (true, vertices_290) then 2 else
  if p.val = (true, vertices_322) then 3 else
  if p.val = (true, vertices_28) then 4 else
  if p.val = (true, vertices_140) then 5 else
  if p.val = (true, vertices_268) then 6 else
  if p.val = (true, vertices_164) then 7 else
  if p.val = (true, vertices_292) then 8 else
  if p.val = (true, vertices_548) then 9 else
  if p.val = (true, vertices_644) then 10 else
  if p.val = (true, vertices_424) then 21 else
  if p.val = (true, vertices_328) then 11 else
  if p.val = (true, vertices_224) then 12 else
  if p.val = (true, vertices_352) then 13 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_771), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_153), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_290), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_322), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_28), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_140), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_268), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_164), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_292), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_548), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_644), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_328), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_224), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_352), by decide +kernel⟩
  | 14 => Sum.inl 0
  | 15 => Sum.inr ⟨(false, vertices_283), by decide +kernel⟩
  | 16 => Sum.inr ⟨(false, vertices_203), by decide +kernel⟩
  | 17 => Sum.inr ⟨(false, vertices_611), by decide +kernel⟩
  | 18 => Sum.inl 1
  | 19 => Sum.inr ⟨(false, vertices_789), by decide +kernel⟩
  | 20 => Sum.inl 2
  | 21 => Sum.inr ⟨(true, vertices_424), by decide +kernel⟩
  | 22 => Sum.inl 3
  | 23 => Sum.inr ⟨(false, vertices_721), by decide +kernel⟩
  | 24 => Sum.inl 4
  | 25 => Sum.inl 5
  | 26 => Sum.inl 6
  | 27 => Sum.inl 7
  | 28 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 4 7 8 806 290 1
cert_row_2 1 2 4 6 7 424
cert_row_4 2 1 2 3 6 8 668 28 3
cert_row_4 3 1 4 5 6 8 740 164 2
cert_rows
cert_pivot_2 0 7 2 1
cert_heightProof 4
cert_coverFacet 0 806
cert_cover_5 0 0 0 1 4 7 290 806 1
cert_coverFacet 1 330
cert_cover_2 1 2 0 5 7 74 330 3
cert_coverFacet 2 354
cert_cover_2 2 4 0 5 7 98 354 3
cert_coverFacet 3 668
cert_cover_5 3 2 1 2 3 6 28 668 3
cert_coverFacet 4 284
cert_cover_2 4 2 1 3 7 28 284 3
cert_coverFacet 5 428
cert_cover_5 5 1 1 2 4 6 140 428 2
cert_coverFacet 6 740
cert_cover_5 6 3 1 4 5 6 164 740 2
cert_coverFacet 7 488
cert_cover_5 7 1 2 4 5 6 424 488 2
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0417

end
end BundlePart20

section BundlePart21
/- Source: ProjectionCertificates/R_m15e10q1_0418.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0418

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [803, 707, 323, 677, 457, 433, 790, 346, 602, 188, 540, 716, 308, 804, 408, 67, 259, 515, 161, 289, 545, 193, 321, 385, 641, 90, 274, 530, 322, 578, 770, 28, 140, 524, 52, 276, 532, 164, 292, 548, 644, 772, 152, 280, 536, 200, 328, 584, 392, 176, 304, 400, 800, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_803, vertices_707, vertices_323, vertices_677, vertices_457, vertices_433, vertices_790, vertices_346, vertices_602, vertices_188, vertices_540, vertices_716, vertices_308, vertices_804, vertices_408] (by decide +kernel)
  polygons := literalFinset [vertices_67, vertices_259, vertices_515, vertices_161, vertices_289, vertices_545, vertices_193, vertices_321, vertices_385, vertices_641, vertices_90, vertices_274, vertices_530, vertices_322, vertices_578, vertices_770, vertices_28, vertices_140, vertices_524, vertices_52, vertices_276, vertices_532, vertices_164, vertices_292, vertices_548, vertices_644, vertices_772, vertices_152, vertices_280, vertices_536, vertices_200, vertices_328, vertices_584, vertices_392, vertices_176, vertices_304, vertices_400, vertices_800, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_803), (false, vertices_707), (false, vertices_323), (false, vertices_677), (false, vertices_457), (false, vertices_433), (true, vertices_90), (true, vertices_274), (true, vertices_530), (true, vertices_28), (true, vertices_140), (true, vertices_524), (true, vertices_52), (true, vertices_276), (true, vertices_532), (true, vertices_292), (true, vertices_772), (true, vertices_152), (true, vertices_280), (true, vertices_536), (true, vertices_584)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 19 21 23 25 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_803) then 16 else
  if p.val = (false, vertices_707) then 17 else
  if p.val = (false, vertices_323) then 0 else
  if p.val = (false, vertices_677) then 20 else
  if p.val = (false, vertices_457) then 22 else
  if p.val = (false, vertices_433) then 24 else
  if p.val = (true, vertices_90) then 18 else
  if p.val = (true, vertices_274) then 1 else
  if p.val = (true, vertices_530) then 2 else
  if p.val = (true, vertices_28) then 3 else
  if p.val = (true, vertices_140) then 4 else
  if p.val = (true, vertices_524) then 5 else
  if p.val = (true, vertices_52) then 6 else
  if p.val = (true, vertices_276) then 7 else
  if p.val = (true, vertices_532) then 8 else
  if p.val = (true, vertices_292) then 9 else
  if p.val = (true, vertices_772) then 10 else
  if p.val = (true, vertices_152) then 11 else
  if p.val = (true, vertices_280) then 12 else
  if p.val = (true, vertices_536) then 13 else
  if p.val = (true, vertices_584) then 14 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_323), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_274), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_530), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_28), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_140), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_524), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_52), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_276), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_532), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_292), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_772), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_152), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_280), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_536), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_584), by decide +kernel⟩
  | 15 => Sum.inl 0
  | 16 => Sum.inr ⟨(false, vertices_803), by decide +kernel⟩
  | 17 => Sum.inr ⟨(false, vertices_707), by decide +kernel⟩
  | 18 => Sum.inr ⟨(true, vertices_90), by decide +kernel⟩
  | 19 => Sum.inl 1
  | 20 => Sum.inr ⟨(false, vertices_677), by decide +kernel⟩
  | 21 => Sum.inl 2
  | 22 => Sum.inr ⟨(false, vertices_457), by decide +kernel⟩
  | 23 => Sum.inl 3
  | 24 => Sum.inr ⟨(false, vertices_433), by decide +kernel⟩
  | 25 => Sum.inl 4
  | 26 => Sum.inl 5
  | 27 => Sum.inl 6
  | 28 => Sum.inl 7
  | 29 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 3 7 8 790 274 1
cert_row_2 1 0 2 3 5 90
cert_row_4 2 1 2 3 4 6 188 28 3
cert_row_4 3 1 2 5 6 8 716 140 2
cert_rows
cert_pivot_2 7 0 3 1
cert_heightProof 4
cert_coverFacet 0 790
cert_cover_5 0 0 0 1 3 7 274 790 1
cert_coverFacet 1 346
cert_cover_5 1 1 0 2 3 7 90 346 3
cert_coverFacet 2 602
cert_cover_5 2 1 0 2 3 8 90 602 3
cert_coverFacet 3 188
cert_cover_5 3 2 1 2 3 4 28 188 3
cert_coverFacet 4 540
cert_cover_2 4 2 1 3 8 28 540 3
cert_coverFacet 5 716
cert_cover_5 5 3 1 2 5 6 140 716 2
cert_coverFacet 6 308
cert_cover_2 6 3 1 4 7 52 308 3
cert_coverFacet 7 804
cert_cover_2 7 4 1 7 8 292 804 3
cert_coverFacet 8 408
cert_cover_2 8 3 2 6 7 152 408 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0418

end
end BundlePart21

section BundlePart22
/- Source: ProjectionCertificates/R_m15e10q1_0419.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0419

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [587, 563, 403, 195, 205, 397, 313, 553, 710, 658, 364, 916, 836, 616, 880, 19, 67, 131, 515, 141, 41, 73, 265, 521, 49, 273, 545, 193, 385, 146, 530, 194, 578, 642, 76, 268, 196, 324, 580, 388, 644, 772, 104, 296, 552, 584, 304, 560, 400, 656, 784, 352, 608, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_587, vertices_563, vertices_403, vertices_195, vertices_205, vertices_397, vertices_313, vertices_553, vertices_710, vertices_658, vertices_364, vertices_916, vertices_836, vertices_616, vertices_880] (by decide +kernel)
  polygons := literalFinset [vertices_19, vertices_67, vertices_131, vertices_515, vertices_141, vertices_41, vertices_73, vertices_265, vertices_521, vertices_49, vertices_273, vertices_545, vertices_193, vertices_385, vertices_146, vertices_530, vertices_194, vertices_578, vertices_642, vertices_76, vertices_268, vertices_196, vertices_324, vertices_580, vertices_388, vertices_644, vertices_772, vertices_104, vertices_296, vertices_552, vertices_584, vertices_304, vertices_560, vertices_400, vertices_656, vertices_784, vertices_352, vertices_608, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_587), (false, vertices_563), (false, vertices_403), (false, vertices_195), (false, vertices_205), (false, vertices_397), (false, vertices_313), (false, vertices_553), (true, vertices_642), (true, vertices_324), (true, vertices_580), (true, vertices_644), (true, vertices_772), (true, vertices_104), (true, vertices_656), (true, vertices_784), (true, vertices_352), (true, vertices_608), (true, vertices_832)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 13 17 20 22 23 24 25 26 27
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_587) then 14 else
  if p.val = (false, vertices_563) then 15 else
  if p.val = (false, vertices_403) then 16 else
  if p.val = (false, vertices_195) then 0 else
  if p.val = (false, vertices_205) then 18 else
  if p.val = (false, vertices_397) then 19 else
  if p.val = (false, vertices_313) then 21 else
  if p.val = (false, vertices_553) then 1 else
  if p.val = (true, vertices_642) then 2 else
  if p.val = (true, vertices_324) then 3 else
  if p.val = (true, vertices_580) then 4 else
  if p.val = (true, vertices_644) then 5 else
  if p.val = (true, vertices_772) then 6 else
  if p.val = (true, vertices_104) then 7 else
  if p.val = (true, vertices_656) then 8 else
  if p.val = (true, vertices_784) then 9 else
  if p.val = (true, vertices_352) then 10 else
  if p.val = (true, vertices_608) then 11 else
  if p.val = (true, vertices_832) then 12 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_195), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_553), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_642), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_324), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_580), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_644), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_772), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_104), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_656), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_784), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_352), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_608), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_832), by decide +kernel⟩
  | 13 => Sum.inl 0
  | 14 => Sum.inr ⟨(false, vertices_587), by decide +kernel⟩
  | 15 => Sum.inr ⟨(false, vertices_563), by decide +kernel⟩
  | 16 => Sum.inr ⟨(false, vertices_403), by decide +kernel⟩
  | 17 => Sum.inl 1
  | 18 => Sum.inr ⟨(false, vertices_205), by decide +kernel⟩
  | 19 => Sum.inr ⟨(false, vertices_397), by decide +kernel⟩
  | 20 => Sum.inl 2
  | 21 => Sum.inr ⟨(false, vertices_313), by decide +kernel⟩
  | 22 => Sum.inl 3
  | 23 => Sum.inl 4
  | 24 => Sum.inl 5
  | 25 => Sum.inl 6
  | 26 => Sum.inl 7
  | 27 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 5 6 8 710 194 1
cert_row_4 1 1 2 4 5 7 364 76 2
cert_row_4 2 1 3 6 7 8 916 388 1
cert_row_4 3 3 4 5 7 8 880 304 2
cert_rows
cert_pivot_2 0 2 1 3
cert_heightProof 4
cert_coverFacet 0 710
cert_cover_5 0 0 0 1 5 6 194 710 1
cert_coverFacet 1 658
cert_cover_2 1 3 0 6 8 146 658 3
cert_coverFacet 2 364
cert_cover_5 2 1 1 2 4 5 76 364 2
cert_coverFacet 3 916
cert_cover_5 3 2 1 3 6 7 388 916 1
cert_coverFacet 4 836
cert_cover_2 4 5 1 7 8 324 836 3
cert_coverFacet 5 616
cert_cover_2 5 4 2 5 8 104 616 3
cert_coverFacet 6 880
cert_cover_5 6 3 3 4 5 7 304 880 2
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0419

end
end BundlePart22

section BundlePart23
/- Source: ProjectionCertificates/R_m15e10q1_0420.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0420

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [283, 709, 601, 425, 649, 465, 174, 654, 614, 538, 298, 818, 484, 848, 864, 25, 137, 265, 521, 81, 273, 193, 577, 385, 641, 142, 38, 518, 26, 42, 266, 522, 274, 530, 290, 546, 100, 164, 196, 580, 644, 536, 168, 296, 648, 336, 592, 784, 352, 608, 416, 800, 448, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_283, vertices_709, vertices_601, vertices_425, vertices_649, vertices_465, vertices_174, vertices_654, vertices_614, vertices_538, vertices_298, vertices_818, vertices_484, vertices_848, vertices_864] (by decide +kernel)
  polygons := literalFinset [vertices_25, vertices_137, vertices_265, vertices_521, vertices_81, vertices_273, vertices_193, vertices_577, vertices_385, vertices_641, vertices_142, vertices_38, vertices_518, vertices_26, vertices_42, vertices_266, vertices_522, vertices_274, vertices_530, vertices_290, vertices_546, vertices_100, vertices_164, vertices_196, vertices_580, vertices_644, vertices_536, vertices_168, vertices_296, vertices_648, vertices_336, vertices_592, vertices_784, vertices_352, vertices_608, vertices_416, vertices_800, vertices_448, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_283), (false, vertices_709), (false, vertices_601), (false, vertices_425), (false, vertices_649), (false, vertices_465), (true, vertices_142), (true, vertices_38), (true, vertices_518), (true, vertices_42), (true, vertices_522), (true, vertices_530), (true, vertices_290), (true, vertices_546), (true, vertices_100), (true, vertices_164), (true, vertices_784), (true, vertices_352), (true, vertices_608), (true, vertices_800), (true, vertices_832)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 18 20 23 25 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_283) then 16 else
  if p.val = (false, vertices_709) then 19 else
  if p.val = (false, vertices_601) then 21 else
  if p.val = (false, vertices_425) then 22 else
  if p.val = (false, vertices_649) then 0 else
  if p.val = (false, vertices_465) then 24 else
  if p.val = (true, vertices_142) then 17 else
  if p.val = (true, vertices_38) then 1 else
  if p.val = (true, vertices_518) then 2 else
  if p.val = (true, vertices_42) then 3 else
  if p.val = (true, vertices_522) then 4 else
  if p.val = (true, vertices_530) then 5 else
  if p.val = (true, vertices_290) then 6 else
  if p.val = (true, vertices_546) then 7 else
  if p.val = (true, vertices_100) then 8 else
  if p.val = (true, vertices_164) then 9 else
  if p.val = (true, vertices_784) then 10 else
  if p.val = (true, vertices_352) then 11 else
  if p.val = (true, vertices_608) then 12 else
  if p.val = (true, vertices_800) then 13 else
  if p.val = (true, vertices_832) then 14 else
  0
cert_priority
cert_nodeAtPriority_31 649 38 518 42 522 530 290 546 100 164 784 352 608 800 832 283 142 709 601 425 465
cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 1 2 6 142
cert_row_4 1 0 3 4 7 8 818 274 2
cert_row_4 2 0 1 4 5 8 614 38 3
cert_row_4 3 1 4 5 6 7 484 100 3
cert_rows
cert_pivot_2 2 3 0 1
cert_heightProof 4
cert_coverFacet 0 174
cert_cover_5 0 0 0 1 2 4 142 174 3
cert_coverFacet 1 654
cert_cover_5 1 0 0 1 2 8 142 654 3
cert_coverFacet 2 614
cert_cover_5 2 2 0 1 4 5 38 614 3
cert_coverFacet 3 538
cert_cover_2 3 2 0 3 8 26 538 3
cert_coverFacet 4 298
cert_cover_2 4 2 0 4 7 42 298 3
cert_coverFacet 5 818
cert_cover_5 5 1 0 3 4 7 274 818 2
cert_coverFacet 6 484
cert_cover_5 6 3 1 4 5 6 100 484 3
cert_coverFacet 7 848
cert_cover_2 7 5 3 7 8 336 848 3
cert_coverFacet 8 864
cert_cover_2 8 5 4 7 8 352 864 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0420

end
end BundlePart23

section BundlePart24
/- Source: ProjectionCertificates/R_m15e10q1_0421.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0421

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [155, 613, 313, 553, 713, 241, 302, 558, 838, 282, 650, 402, 898, 372, 976, 25, 41, 137, 521, 49, 145, 97, 545, 193, 577, 46, 262, 518, 26, 138, 266, 522, 146, 274, 386, 642, 770, 100, 292, 548, 324, 580, 280, 296, 552, 648, 112, 304, 208, 336, 400, 704, 832, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_155, vertices_613, vertices_313, vertices_553, vertices_713, vertices_241, vertices_302, vertices_558, vertices_838, vertices_282, vertices_650, vertices_402, vertices_898, vertices_372, vertices_976] (by decide +kernel)
  polygons := literalFinset [vertices_25, vertices_41, vertices_137, vertices_521, vertices_49, vertices_145, vertices_97, vertices_545, vertices_193, vertices_577, vertices_46, vertices_262, vertices_518, vertices_26, vertices_138, vertices_266, vertices_522, vertices_146, vertices_274, vertices_386, vertices_642, vertices_770, vertices_100, vertices_292, vertices_548, vertices_324, vertices_580, vertices_280, vertices_296, vertices_552, vertices_648, vertices_112, vertices_304, vertices_208, vertices_336, vertices_400, vertices_704, vertices_832, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_155), (false, vertices_613), (false, vertices_313), (false, vertices_553), (false, vertices_713), (false, vertices_241), (true, vertices_46), (true, vertices_262), (true, vertices_518), (true, vertices_266), (true, vertices_522), (true, vertices_274), (true, vertices_386), (true, vertices_642), (true, vertices_770), (true, vertices_292), (true, vertices_324), (true, vertices_336), (true, vertices_400), (true, vertices_832), (true, vertices_896)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 18 20 23 25 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_155) then 16 else
  if p.val = (false, vertices_613) then 19 else
  if p.val = (false, vertices_313) then 21 else
  if p.val = (false, vertices_553) then 0 else
  if p.val = (false, vertices_713) then 22 else
  if p.val = (false, vertices_241) then 24 else
  if p.val = (true, vertices_46) then 17 else
  if p.val = (true, vertices_262) then 1 else
  if p.val = (true, vertices_518) then 2 else
  if p.val = (true, vertices_266) then 3 else
  if p.val = (true, vertices_522) then 4 else
  if p.val = (true, vertices_274) then 5 else
  if p.val = (true, vertices_386) then 6 else
  if p.val = (true, vertices_642) then 7 else
  if p.val = (true, vertices_770) then 8 else
  if p.val = (true, vertices_292) then 9 else
  if p.val = (true, vertices_324) then 10 else
  if p.val = (true, vertices_336) then 11 else
  if p.val = (true, vertices_400) then 12 else
  if p.val = (true, vertices_832) then 13 else
  if p.val = (true, vertices_896) then 14 else
  0
cert_priority
cert_nodeAtPriority_31 553 262 518 266 522 274 386 642 770 292 324 336 400 832 896 155 46 613 313 713 241
cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 1 2 4 46
cert_row_4 1 0 1 5 7 8 838 262 2
cert_row_4 2 1 3 4 5 7 372 100 1
cert_row_4 3 3 5 6 7 8 976 208 3
cert_rows
cert_pivot_2 2 0 1 3
cert_heightProof 4
cert_coverFacet 0 302
cert_cover_5 0 0 0 1 2 7 46 302 3
cert_coverFacet 1 558
cert_cover_5 1 0 0 1 2 8 46 558 3
cert_coverFacet 2 838
cert_cover_5 2 1 0 1 5 7 262 838 2
cert_coverFacet 3 282
cert_cover_2 3 2 0 3 7 26 282 3
cert_coverFacet 4 650
cert_cover_2 4 2 0 6 8 138 650 3
cert_coverFacet 5 402
cert_cover_2 5 3 0 6 7 146 402 3
cert_coverFacet 6 898
cert_cover_2 6 6 0 7 8 386 898 3
cert_coverFacet 7 372
cert_cover_5 7 2 1 3 4 5 100 372 1
cert_coverFacet 8 976
cert_cover_5 8 3 3 5 6 7 208 976 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0421

end
end BundlePart24

section BundlePart25
/- Source: ProjectionCertificates/R_m15e10q1_0422.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0422

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [899, 109, 557, 789, 453, 713, 342, 682, 178, 818, 210, 450, 116, 564, 248, 45, 69, 261, 517, 73, 521, 193, 385, 641, 769, 50, 82, 146, 274, 162, 546, 194, 322, 386, 642, 770, 52, 84, 276, 532, 100, 548, 324, 104, 168, 552, 200, 648, 112, 176, 560, 208, 784, 448]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_899, vertices_109, vertices_557, vertices_789, vertices_453, vertices_713, vertices_342, vertices_682, vertices_178, vertices_818, vertices_210, vertices_450, vertices_116, vertices_564, vertices_248] (by decide +kernel)
  polygons := literalFinset [vertices_45, vertices_69, vertices_261, vertices_517, vertices_73, vertices_521, vertices_193, vertices_385, vertices_641, vertices_769, vertices_50, vertices_82, vertices_146, vertices_274, vertices_162, vertices_546, vertices_194, vertices_322, vertices_386, vertices_642, vertices_770, vertices_52, vertices_84, vertices_276, vertices_532, vertices_100, vertices_548, vertices_324, vertices_104, vertices_168, vertices_552, vertices_200, vertices_648, vertices_112, vertices_176, vertices_560, vertices_208, vertices_784, vertices_448] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_899), (false, vertices_109), (false, vertices_557), (false, vertices_789), (false, vertices_453), (false, vertices_713), (true, vertices_50), (true, vertices_82), (true, vertices_146), (true, vertices_274), (true, vertices_162), (true, vertices_546), (true, vertices_194), (true, vertices_322), (true, vertices_52), (true, vertices_84), (true, vertices_168), (true, vertices_112), (true, vertices_176), (true, vertices_560), (true, vertices_208)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 21 17 24 25 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_899) then 16 else
  if p.val = (false, vertices_109) then 18 else
  if p.val = (false, vertices_557) then 19 else
  if p.val = (false, vertices_789) then 22 else
  if p.val = (false, vertices_453) then 23 else
  if p.val = (false, vertices_713) then 20 else
  if p.val = (true, vertices_50) then 0 else
  if p.val = (true, vertices_82) then 1 else
  if p.val = (true, vertices_146) then 2 else
  if p.val = (true, vertices_274) then 3 else
  if p.val = (true, vertices_162) then 4 else
  if p.val = (true, vertices_546) then 5 else
  if p.val = (true, vertices_194) then 6 else
  if p.val = (true, vertices_322) then 7 else
  if p.val = (true, vertices_52) then 8 else
  if p.val = (true, vertices_84) then 9 else
  if p.val = (true, vertices_168) then 10 else
  if p.val = (true, vertices_112) then 11 else
  if p.val = (true, vertices_176) then 12 else
  if p.val = (true, vertices_560) then 13 else
  if p.val = (true, vertices_208) then 14 else
  0
cert_priority
cert_nodeAtPriority_36 0 50 2 82 1 146 274 162 546 194 322 52 84 168 112 176 560 208 899 109 557 713 789 453
cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 3 5 7 342 82 1
cert_row_4 1 0 3 4 7 8 818 50 3
cert_row_4 2 0 2 4 6 8 682 162 1
cert_row_4 3 2 3 4 5 6 248 104 1
cert_rows
cert_pivot_2 1 7 0 2
cert_heightProof 4
cert_coverFacet 0 342
cert_cover_5 0 0 0 1 3 5 82 342 1
cert_coverFacet 1 682
cert_cover_5 1 2 0 2 4 6 162 682 1
cert_coverFacet 2 178
cert_cover_2 2 3 0 4 6 50 178 3
cert_coverFacet 3 818
cert_cover_5 3 1 0 3 4 7 50 818 3
cert_coverFacet 4 210
cert_cover_2 4 3 0 5 6 82 210 3
cert_coverFacet 5 450
cert_cover_2 5 5 0 6 7 194 450 3
cert_coverFacet 6 116
cert_cover_2 6 3 1 4 5 52 116 3
cert_coverFacet 7 564
cert_cover_2 7 3 1 4 8 52 564 3
cert_coverFacet 8 248
cert_cover_5 8 3 2 3 4 5 104 248 1
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0422

end
end BundlePart25

section BundlePart26
/- Source: ProjectionCertificates/R_m15e10q1_0423.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0423

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [803, 205, 597, 677, 425, 585, 777, 566, 602, 282, 778, 306, 372, 484, 472, 69, 133, 517, 73, 137, 265, 521, 161, 289, 545, 577, 769, 26, 266, 522, 50, 274, 530, 290, 546, 770, 52, 84, 532, 356, 164, 548, 196, 88, 280, 200, 584, 392, 776, 304, 336, 592, 416, 448]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_803, vertices_205, vertices_597, vertices_677, vertices_425, vertices_585, vertices_777, vertices_566, vertices_602, vertices_282, vertices_778, vertices_306, vertices_372, vertices_484, vertices_472] (by decide +kernel)
  polygons := literalFinset [vertices_69, vertices_133, vertices_517, vertices_73, vertices_137, vertices_265, vertices_521, vertices_161, vertices_289, vertices_545, vertices_577, vertices_769, vertices_26, vertices_266, vertices_522, vertices_50, vertices_274, vertices_530, vertices_290, vertices_546, vertices_770, vertices_52, vertices_84, vertices_532, vertices_356, vertices_164, vertices_548, vertices_196, vertices_88, vertices_280, vertices_200, vertices_584, vertices_392, vertices_776, vertices_304, vertices_336, vertices_592, vertices_416, vertices_448] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_803), (false, vertices_205), (false, vertices_597), (false, vertices_677), (false, vertices_425), (false, vertices_585), (false, vertices_777), (true, vertices_26), (true, vertices_266), (true, vertices_522), (true, vertices_50), (true, vertices_274), (true, vertices_530), (true, vertices_52), (true, vertices_356), (true, vertices_88), (true, vertices_280), (true, vertices_304), (true, vertices_336), (true, vertices_448)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 14 19 16 23 24 25 26 27 28
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_803) then 15 else
  if p.val = (false, vertices_205) then 17 else
  if p.val = (false, vertices_597) then 20 else
  if p.val = (false, vertices_677) then 21 else
  if p.val = (false, vertices_425) then 18 else
  if p.val = (false, vertices_585) then 0 else
  if p.val = (false, vertices_777) then 1 else
  if p.val = (true, vertices_26) then 2 else
  if p.val = (true, vertices_266) then 3 else
  if p.val = (true, vertices_522) then 4 else
  if p.val = (true, vertices_50) then 5 else
  if p.val = (true, vertices_274) then 6 else
  if p.val = (true, vertices_530) then 7 else
  if p.val = (true, vertices_52) then 8 else
  if p.val = (true, vertices_356) then 22 else
  if p.val = (true, vertices_88) then 9 else
  if p.val = (true, vertices_280) then 10 else
  if p.val = (true, vertices_304) then 11 else
  if p.val = (true, vertices_336) then 12 else
  if p.val = (true, vertices_448) then 13 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_585), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_777), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_26), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_266), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_522), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_50), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_274), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_530), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_52), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_88), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_280), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_304), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_336), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_448), by decide +kernel⟩
  | 14 => Sum.inl 0
  | 15 => Sum.inr ⟨(false, vertices_803), by decide +kernel⟩
  | 16 => Sum.inl 2
  | 17 => Sum.inr ⟨(false, vertices_205), by decide +kernel⟩
  | 18 => Sum.inr ⟨(false, vertices_425), by decide +kernel⟩
  | 19 => Sum.inl 1
  | 20 => Sum.inr ⟨(false, vertices_597), by decide +kernel⟩
  | 21 => Sum.inr ⟨(false, vertices_677), by decide +kernel⟩
  | 22 => Sum.inr ⟨(true, vertices_356), by decide +kernel⟩
  | 23 => Sum.inl 3
  | 24 => Sum.inl 4
  | 25 => Sum.inl 5
  | 26 => Sum.inl 6
  | 27 => Sum.inl 7
  | 28 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 2 3 5 6 7 472 88 3
cert_row_2 1 1 4 5 7 356
cert_row_4 2 0 1 3 4 8 566 50 1
cert_row_4 3 0 2 3 5 8 602 26 3
cert_rows
cert_pivot_2 6 7 1 0
cert_heightProof 4
cert_coverFacet 0 566
cert_cover_5 0 2 0 1 3 4 50 566 1
cert_coverFacet 1 602
cert_cover_5 1 3 0 2 3 5 26 602 3
cert_coverFacet 2 282
cert_cover_2 2 2 0 3 7 26 282 3
cert_coverFacet 3 778
cert_cover_2 3 2 0 7 8 266 778 3
cert_coverFacet 4 306
cert_cover_2 4 3 0 4 7 50 306 3
cert_coverFacet 5 372
cert_cover_5 5 1 1 3 4 5 52 372 3
cert_coverFacet 6 484
cert_cover_5 6 1 1 4 5 6 356 484 3
cert_coverFacet 7 472
cert_cover_5 7 0 2 3 5 6 88 472 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0423

end
end BundlePart26

section BundlePart27
/- Source: ProjectionCertificates/R_m15e10q1_0424.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0424

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [55, 157, 397, 805, 689, 961, 30, 526, 550, 90, 618, 242, 844, 472, 736, 141, 21, 37, 261, 49, 145, 545, 385, 641, 769, 14, 22, 38, 518, 26, 74, 522, 50, 82, 98, 546, 28, 268, 524, 548, 772, 88, 152, 328, 584, 392, 176, 208, 224, 608, 672, 448, 704, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_55, vertices_157, vertices_397, vertices_805, vertices_689, vertices_961, vertices_30, vertices_526, vertices_550, vertices_90, vertices_618, vertices_242, vertices_844, vertices_472, vertices_736] (by decide +kernel)
  polygons := literalFinset [vertices_141, vertices_21, vertices_37, vertices_261, vertices_49, vertices_145, vertices_545, vertices_385, vertices_641, vertices_769, vertices_14, vertices_22, vertices_38, vertices_518, vertices_26, vertices_74, vertices_522, vertices_50, vertices_82, vertices_98, vertices_546, vertices_28, vertices_268, vertices_524, vertices_548, vertices_772, vertices_88, vertices_152, vertices_328, vertices_584, vertices_392, vertices_176, vertices_208, vertices_224, vertices_608, vertices_672, vertices_448, vertices_704, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_55), (false, vertices_157), (false, vertices_397), (false, vertices_805), (false, vertices_689), (false, vertices_961), (true, vertices_14), (true, vertices_518), (true, vertices_26), (true, vertices_74), (true, vertices_522), (true, vertices_82), (true, vertices_98), (true, vertices_546), (true, vertices_524), (true, vertices_88), (true, vertices_328), (true, vertices_584), (true, vertices_208), (true, vertices_224), (true, vertices_608)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 17 21 22 24 25 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_55) then 16 else
  if p.val = (false, vertices_157) then 18 else
  if p.val = (false, vertices_397) then 19 else
  if p.val = (false, vertices_805) then 20 else
  if p.val = (false, vertices_689) then 23 else
  if p.val = (false, vertices_961) then 26 else
  if p.val = (true, vertices_14) then 0 else
  if p.val = (true, vertices_518) then 1 else
  if p.val = (true, vertices_26) then 2 else
  if p.val = (true, vertices_74) then 3 else
  if p.val = (true, vertices_522) then 4 else
  if p.val = (true, vertices_82) then 5 else
  if p.val = (true, vertices_98) then 6 else
  if p.val = (true, vertices_546) then 7 else
  if p.val = (true, vertices_524) then 8 else
  if p.val = (true, vertices_88) then 9 else
  if p.val = (true, vertices_328) then 10 else
  if p.val = (true, vertices_584) then 11 else
  if p.val = (true, vertices_208) then 12 else
  if p.val = (true, vertices_224) then 13 else
  if p.val = (true, vertices_608) then 14 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_14), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_518), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_26), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_74), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_522), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_82), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_98), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_546), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_524), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_88), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_328), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_584), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_208), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_224), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_608), by decide +kernel⟩
  | 15 => Sum.inl 0
  | 16 => Sum.inr ⟨(false, vertices_55), by decide +kernel⟩
  | 17 => Sum.inl 1
  | 18 => Sum.inr ⟨(false, vertices_157), by decide +kernel⟩
  | 19 => Sum.inr ⟨(false, vertices_397), by decide +kernel⟩
  | 20 => Sum.inr ⟨(false, vertices_805), by decide +kernel⟩
  | 21 => Sum.inl 2
  | 22 => Sum.inl 3
  | 23 => Sum.inr ⟨(false, vertices_689), by decide +kernel⟩
  | 24 => Sum.inl 4
  | 25 => Sum.inl 5
  | 26 => Sum.inr ⟨(false, vertices_961), by decide +kernel⟩
  | 27 => Sum.inl 6
  | 28 => Sum.inl 7
  | 29 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 1 2 5 7 8 844 268 2
cert_row_4 1 0 2 4 5 8 618 74 2
cert_row_4 2 0 3 4 5 6 242 50 3
cert_row_4 3 2 3 5 6 7 472 88 3
cert_rows
cert_pivot_2 1 8 0 2
cert_heightProof 4
cert_coverFacet 0 30
cert_cover_2 0 1 0 2 3 14 30 3
cert_coverFacet 1 526
cert_cover_2 1 1 0 2 8 14 526 3
cert_coverFacet 2 550
cert_cover_2 2 1 0 4 8 38 550 3
cert_coverFacet 3 90
cert_cover_2 3 2 0 3 5 26 90 3
cert_coverFacet 4 618
cert_cover_5 4 1 0 2 4 5 74 618 2
cert_coverFacet 5 242
cert_cover_5 5 2 0 3 4 5 50 242 3
cert_coverFacet 6 844
cert_cover_5 6 0 1 2 5 7 268 844 2
cert_coverFacet 7 472
cert_cover_5 7 3 2 3 5 6 88 472 3
cert_coverFacet 8 736
cert_cover_2 8 5 4 6 8 224 736 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0424

end
end BundlePart27

section BundlePart28
/- Source: ProjectionCertificates/R_m15e10q1_0425.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0425

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [103, 179, 403, 835, 53, 597, 793, 906, 738, 60, 540, 236, 588, 440, 712, 147, 35, 67, 259, 21, 37, 69, 49, 273, 529, 577, 769, 98, 162, 578, 386, 642, 770, 28, 44, 76, 524, 52, 532, 100, 580, 56, 280, 536, 168, 200, 584, 392, 648, 776, 176, 400, 224, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_103, vertices_179, vertices_403, vertices_835, vertices_53, vertices_597, vertices_793, vertices_906, vertices_738, vertices_60, vertices_540, vertices_236, vertices_588, vertices_440, vertices_712] (by decide +kernel)
  polygons := literalFinset [vertices_147, vertices_35, vertices_67, vertices_259, vertices_21, vertices_37, vertices_69, vertices_49, vertices_273, vertices_529, vertices_577, vertices_769, vertices_98, vertices_162, vertices_578, vertices_386, vertices_642, vertices_770, vertices_28, vertices_44, vertices_76, vertices_524, vertices_52, vertices_532, vertices_100, vertices_580, vertices_56, vertices_280, vertices_536, vertices_168, vertices_200, vertices_584, vertices_392, vertices_648, vertices_776, vertices_176, vertices_400, vertices_224, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_103), (false, vertices_179), (false, vertices_403), (false, vertices_835), (false, vertices_53), (false, vertices_597), (false, vertices_793), (true, vertices_642), (true, vertices_28), (true, vertices_44), (true, vertices_76), (true, vertices_524), (true, vertices_56), (true, vertices_168), (true, vertices_200), (true, vertices_584), (true, vertices_392), (true, vertices_648), (true, vertices_224), (true, vertices_704)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 17 14 21 23 24 25 26 27 28
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_103) then 15 else
  if p.val = (false, vertices_179) then 18 else
  if p.val = (false, vertices_403) then 19 else
  if p.val = (false, vertices_835) then 20 else
  if p.val = (false, vertices_53) then 0 else
  if p.val = (false, vertices_597) then 16 else
  if p.val = (false, vertices_793) then 22 else
  if p.val = (true, vertices_642) then 1 else
  if p.val = (true, vertices_28) then 2 else
  if p.val = (true, vertices_44) then 3 else
  if p.val = (true, vertices_76) then 4 else
  if p.val = (true, vertices_524) then 5 else
  if p.val = (true, vertices_56) then 6 else
  if p.val = (true, vertices_168) then 7 else
  if p.val = (true, vertices_200) then 8 else
  if p.val = (true, vertices_584) then 9 else
  if p.val = (true, vertices_392) then 10 else
  if p.val = (true, vertices_648) then 11 else
  if p.val = (true, vertices_224) then 12 else
  if p.val = (true, vertices_704) then 13 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_53), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_642), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_28), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_44), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_76), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_524), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_56), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_168), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_200), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_584), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_392), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_648), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_224), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_704), by decide +kernel⟩
  | 14 => Sum.inl 1
  | 15 => Sum.inr ⟨(false, vertices_103), by decide +kernel⟩
  | 16 => Sum.inr ⟨(false, vertices_597), by decide +kernel⟩
  | 17 => Sum.inl 0
  | 18 => Sum.inr ⟨(false, vertices_179), by decide +kernel⟩
  | 19 => Sum.inr ⟨(false, vertices_403), by decide +kernel⟩
  | 20 => Sum.inr ⟨(false, vertices_835), by decide +kernel⟩
  | 21 => Sum.inl 2
  | 22 => Sum.inr ⟨(false, vertices_793), by decide +kernel⟩
  | 23 => Sum.inl 3
  | 24 => Sum.inl 4
  | 25 => Sum.inl 5
  | 26 => Sum.inl 6
  | 27 => Sum.inl 7
  | 28 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 1 2 4 5 6 236 44 3
cert_row_4 1 0 4 5 6 8 738 98 3
cert_row_4 2 0 2 6 7 8 906 386 1
cert_row_4 3 2 3 4 6 7 440 56 3
cert_rows
cert_pivot_2 1 5 0 2
cert_heightProof 4
cert_coverFacet 0 906
cert_cover_5 0 2 0 2 6 7 386 906 1
cert_coverFacet 1 738
cert_cover_5 1 1 0 4 5 6 98 738 3
cert_coverFacet 2 60
cert_cover_2 2 2 1 3 4 28 60 3
cert_coverFacet 3 540
cert_cover_2 3 2 1 3 8 28 540 3
cert_coverFacet 4 236
cert_cover_5 4 0 1 2 4 5 44 236 3
cert_coverFacet 5 588
cert_cover_2 5 2 1 5 8 76 588 3
cert_coverFacet 6 440
cert_cover_5 6 3 2 3 4 6 56 440 3
cert_coverFacet 7 712
cert_cover_2 7 5 2 6 8 200 712 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0425

end
end BundlePart28

section BundlePart29
/- Source: ProjectionCertificates/R_m15e10q1_0426.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0426

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [527, 333, 661, 453, 601, 241, 270, 774, 618, 298, 818, 436, 788, 488, 624, 13, 325, 133, 517, 73, 521, 81, 145, 529, 193, 14, 262, 518, 42, 266, 522, 290, 546, 770, 268, 148, 276, 532, 388, 772, 104, 296, 328, 584, 112, 176, 304, 560, 592, 784, 224, 608, 416, 448]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_527, vertices_333, vertices_661, vertices_453, vertices_601, vertices_241, vertices_270, vertices_774, vertices_618, vertices_298, vertices_818, vertices_436, vertices_788, vertices_488, vertices_624] (by decide +kernel)
  polygons := literalFinset [vertices_13, vertices_325, vertices_133, vertices_517, vertices_73, vertices_521, vertices_81, vertices_145, vertices_529, vertices_193, vertices_14, vertices_262, vertices_518, vertices_42, vertices_266, vertices_522, vertices_290, vertices_546, vertices_770, vertices_268, vertices_148, vertices_276, vertices_532, vertices_388, vertices_772, vertices_104, vertices_296, vertices_328, vertices_584, vertices_112, vertices_176, vertices_304, vertices_560, vertices_592, vertices_784, vertices_224, vertices_608, vertices_416, vertices_448] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_527), (false, vertices_333), (false, vertices_661), (false, vertices_453), (false, vertices_601), (false, vertices_241), (true, vertices_262), (true, vertices_42), (true, vertices_266), (true, vertices_290), (true, vertices_546), (true, vertices_770), (true, vertices_276), (true, vertices_772), (true, vertices_104), (true, vertices_296), (true, vertices_304), (true, vertices_560), (true, vertices_784), (true, vertices_608), (true, vertices_416)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 17 21 23 25 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_527) then 16 else
  if p.val = (false, vertices_333) then 18 else
  if p.val = (false, vertices_661) then 19 else
  if p.val = (false, vertices_453) then 20 else
  if p.val = (false, vertices_601) then 22 else
  if p.val = (false, vertices_241) then 24 else
  if p.val = (true, vertices_262) then 0 else
  if p.val = (true, vertices_42) then 1 else
  if p.val = (true, vertices_266) then 2 else
  if p.val = (true, vertices_290) then 3 else
  if p.val = (true, vertices_546) then 4 else
  if p.val = (true, vertices_770) then 5 else
  if p.val = (true, vertices_276) then 6 else
  if p.val = (true, vertices_772) then 7 else
  if p.val = (true, vertices_104) then 8 else
  if p.val = (true, vertices_296) then 9 else
  if p.val = (true, vertices_304) then 10 else
  if p.val = (true, vertices_560) then 11 else
  if p.val = (true, vertices_784) then 12 else
  if p.val = (true, vertices_608) then 13 else
  if p.val = (true, vertices_416) then 14 else
  0
cert_priority
cert_nodeAtPriority_68 0 262 1 42 266 290 546 770 276 772 104 296 304 560 784 608 416 527 333 661 453 601 241
cert_priority_injective
cert_incidenceProof
cert_row_4 0 1 3 4 6 7 436 148 2
cert_row_4 1 0 3 4 7 8 818 290 1
cert_row_4 2 0 2 4 5 8 618 42 3
cert_row_4 3 2 4 5 6 7 488 104 3
cert_rows
cert_pivot_2 1 3 0 2
cert_heightProof 4
cert_coverFacet 0 270
cert_cover_2 0 1 0 2 7 14 270 3
cert_coverFacet 1 774
cert_cover_2 1 1 0 7 8 262 774 3
cert_coverFacet 2 618
cert_cover_5 2 2 0 2 4 5 42 618 3
cert_coverFacet 3 298
cert_cover_2 3 2 0 4 7 42 298 3
cert_coverFacet 4 818
cert_cover_5 4 1 0 3 4 7 290 818 1
cert_coverFacet 5 436
cert_cover_5 5 0 1 3 4 6 148 436 2
cert_coverFacet 6 788
cert_cover_2 6 3 1 7 8 276 788 3
cert_coverFacet 7 488
cert_cover_5 7 3 2 4 5 6 104 488 3
cert_coverFacet 8 624
cert_cover_2 8 4 3 5 8 112 624 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0426

end
end BundlePart29

-- Public target certificates; internal witness data stays private.
namespace Nonrational.TerminalVerification
open Papers.RationalityTen.ChirotopeDensity.FiniteProjection
open Nonrational.TerminalData
set_option maxRecDepth 100000
set_option maxHeartbeats 0

public theorem projection_3003 : Certifies 3003 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0395.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3004 : Certifies 3004 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0396.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3005 : Certifies 3005 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0397.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3006 : Certifies 3006 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0398.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3007 : Certifies 3007 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0399.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3008 : Certifies 3008 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0401.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3009 : Certifies 3009 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0402.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3010 : Certifies 3010 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0403.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3011 : Certifies 3011 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0404.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3012 : Certifies 3012 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0405.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3013 : Certifies 3013 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0406.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3014 : Certifies 3014 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0407.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3015 : Certifies 3015 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0408.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3016 : Certifies 3016 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0409.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3017 : Certifies 3017 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0411.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3018 : Certifies 3018 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0412.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3019 : Certifies 3019 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0413.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3020 : Certifies 3020 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0414.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3021 : Certifies 3021 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0415.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3022 : Certifies 3022 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0416.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3023 : Certifies 3023 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0417.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3024 : Certifies 3024 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0418.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3025 : Certifies 3025 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0419.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3026 : Certifies 3026 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0420.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3027 : Certifies 3027 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0421.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3028 : Certifies 3028 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0422.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3029 : Certifies 3029 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0423.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3030 : Certifies 3030 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0424.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3031 : Certifies 3031 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0425.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3032 : Certifies 3032 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0426.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem certified_B099 (j : Fin 30) :
    Certifies (3003 + j.val) := by
  fin_cases j
  · exact projection_3003
  · exact projection_3004
  · exact projection_3005
  · exact projection_3006
  · exact projection_3007
  · exact projection_3008
  · exact projection_3009
  · exact projection_3010
  · exact projection_3011
  · exact projection_3012
  · exact projection_3013
  · exact projection_3014
  · exact projection_3015
  · exact projection_3016
  · exact projection_3017
  · exact projection_3018
  · exact projection_3019
  · exact projection_3020
  · exact projection_3021
  · exact projection_3022
  · exact projection_3023
  · exact projection_3024
  · exact projection_3025
  · exact projection_3026
  · exact projection_3027
  · exact projection_3028
  · exact projection_3029
  · exact projection_3030
  · exact projection_3031
  · exact projection_3032

end Nonrational.TerminalVerification
-- Explicit facial frame witnesses, with lexical vector tracking.
