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
/- Source: ProjectionCertificates/R_m14e10q1_0355.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0355

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [835, 117, 805, 325, 569, 721, 454, 666, 810, 394, 706, 316, 412, 212, 37, 69, 261, 49, 81, 529, 545, 321, 577, 769, 138, 266, 522, 194, 322, 578, 386, 642, 770, 284, 52, 84, 148, 292, 196, 324, 388, 56, 152, 536, 296, 552, 392, 208, 656, 800, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_835, vertices_117, vertices_805, vertices_325, vertices_569, vertices_721, vertices_454, vertices_666, vertices_810, vertices_394, vertices_706, vertices_316, vertices_412, vertices_212] (by decide +kernel)
  polygons := literalFinset [vertices_37, vertices_69, vertices_261, vertices_49, vertices_81, vertices_529, vertices_545, vertices_321, vertices_577, vertices_769, vertices_138, vertices_266, vertices_522, vertices_194, vertices_322, vertices_578, vertices_386, vertices_642, vertices_770, vertices_284, vertices_52, vertices_84, vertices_148, vertices_292, vertices_196, vertices_324, vertices_388, vertices_56, vertices_152, vertices_536, vertices_296, vertices_552, vertices_392, vertices_208, vertices_656, vertices_800, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_835), (false, vertices_117), (false, vertices_805), (false, vertices_325), (false, vertices_569), (false, vertices_721), (true, vertices_138), (true, vertices_266), (true, vertices_522), (true, vertices_194), (true, vertices_386), (true, vertices_642), (true, vertices_284), (true, vertices_148), (true, vertices_196), (true, vertices_388), (true, vertices_152), (true, vertices_296), (true, vertices_392)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 13 15 19 21 23 24 25 26 27
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_835) then 14 else
  if p.val = (false, vertices_117) then 16 else
  if p.val = (false, vertices_805) then 17 else
  if p.val = (false, vertices_325) then 0 else
  if p.val = (false, vertices_569) then 20 else
  if p.val = (false, vertices_721) then 22 else
  if p.val = (true, vertices_138) then 1 else
  if p.val = (true, vertices_266) then 2 else
  if p.val = (true, vertices_522) then 3 else
  if p.val = (true, vertices_194) then 4 else
  if p.val = (true, vertices_386) then 5 else
  if p.val = (true, vertices_642) then 6 else
  if p.val = (true, vertices_284) then 18 else
  if p.val = (true, vertices_148) then 7 else
  if p.val = (true, vertices_196) then 8 else
  if p.val = (true, vertices_388) then 9 else
  if p.val = (true, vertices_152) then 10 else
  if p.val = (true, vertices_296) then 11 else
  if p.val = (true, vertices_392) then 12 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_325), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_138), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_266), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_522), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_194), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_386), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_642), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_148), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_196), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_388), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_152), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_296), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_392), by decide +kernel⟩
  | 13 => Sum.inl 0
  | 14 => Sum.inr ⟨(false, vertices_835), by decide +kernel⟩
  | 15 => Sum.inl 1
  | 16 => Sum.inr ⟨(false, vertices_117), by decide +kernel⟩
  | 17 => Sum.inr ⟨(false, vertices_805), by decide +kernel⟩
  | 18 => Sum.inr ⟨(true, vertices_284), by decide +kernel⟩
  | 19 => Sum.inl 2
  | 20 => Sum.inr ⟨(false, vertices_569), by decide +kernel⟩
  | 21 => Sum.inl 3
  | 22 => Sum.inr ⟨(false, vertices_721), by decide +kernel⟩
  | 23 => Sum.inl 4
  | 24 => Sum.inl 5
  | 25 => Sum.inl 6
  | 26 => Sum.inl 7
  | 27 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 5 6 7 454 194 1
cert_row_2 1 1 2 3 7 284
cert_row_4 2 0 2 3 6 8 666 138 2
cert_row_4 3 0 2 4 7 8 810 266 2
cert_rows
cert_pivot_2 5 1 3 0
cert_heightProof 4
cert_coverFacet 0 454
cert_cover_5 0 0 0 1 5 6 194 454 1
cert_coverFacet 1 666
cert_cover_5 1 2 0 2 3 6 138 666 2
cert_coverFacet 2 810
cert_cover_5 2 3 0 2 4 7 266 810 2
cert_coverFacet 3 394
cert_cover_2 3 2 0 6 7 138 394 3
cert_coverFacet 4 706
cert_cover_2 4 5 0 6 8 194 706 3
cert_coverFacet 5 316
cert_cover_5 5 1 1 2 3 4 284 316 3
cert_coverFacet 6 412
cert_cover_5 6 1 1 2 3 6 284 412 3
cert_coverFacet 7 212
cert_cover_2 7 3 1 5 6 84 212 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0355

end
end BundlePart0

section BundlePart1
/- Source: ProjectionCertificates/R_m14e10q1_0370.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0370

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [899, 93, 213, 793, 713, 433, 230, 618, 818, 418, 706, 572, 108, 180, 85, 25, 73, 521, 145, 273, 193, 385, 641, 769, 98, 162, 290, 546, 194, 578, 386, 642, 770, 28, 44, 76, 52, 148, 100, 164, 196, 536, 104, 552, 584, 176, 304, 560, 784, 416, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_899, vertices_93, vertices_213, vertices_793, vertices_713, vertices_433, vertices_230, vertices_618, vertices_818, vertices_418, vertices_706, vertices_572, vertices_108, vertices_180] (by decide +kernel)
  polygons := literalFinset [vertices_85, vertices_25, vertices_73, vertices_521, vertices_145, vertices_273, vertices_193, vertices_385, vertices_641, vertices_769, vertices_98, vertices_162, vertices_290, vertices_546, vertices_194, vertices_578, vertices_386, vertices_642, vertices_770, vertices_28, vertices_44, vertices_76, vertices_52, vertices_148, vertices_100, vertices_164, vertices_196, vertices_536, vertices_104, vertices_552, vertices_584, vertices_176, vertices_304, vertices_560, vertices_784, vertices_416, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_899), (false, vertices_93), (false, vertices_213), (false, vertices_793), (false, vertices_713), (false, vertices_433), (true, vertices_98), (true, vertices_162), (true, vertices_290), (true, vertices_546), (true, vertices_194), (true, vertices_578), (true, vertices_44), (true, vertices_52), (true, vertices_100), (true, vertices_164), (true, vertices_104), (true, vertices_552), (true, vertices_560)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 13 15 18 21 23 24 25 26 27
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_899) then 14 else
  if p.val = (false, vertices_93) then 16 else
  if p.val = (false, vertices_213) then 17 else
  if p.val = (false, vertices_793) then 19 else
  if p.val = (false, vertices_713) then 20 else
  if p.val = (false, vertices_433) then 22 else
  if p.val = (true, vertices_98) then 0 else
  if p.val = (true, vertices_162) then 1 else
  if p.val = (true, vertices_290) then 2 else
  if p.val = (true, vertices_546) then 3 else
  if p.val = (true, vertices_194) then 4 else
  if p.val = (true, vertices_578) then 5 else
  if p.val = (true, vertices_44) then 6 else
  if p.val = (true, vertices_52) then 7 else
  if p.val = (true, vertices_100) then 8 else
  if p.val = (true, vertices_164) then 9 else
  if p.val = (true, vertices_104) then 10 else
  if p.val = (true, vertices_552) then 11 else
  if p.val = (true, vertices_560) then 12 else
  0
cert_priority
cert_nodeAtPriority_12 98 1 162 2 290 546 194 578 44 52 100 164 104 552 560 899 93 213 793 713 433
cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 4 5 6 230 98 1
cert_row_4 1 0 2 4 5 8 618 98 1
cert_row_4 2 0 3 4 7 8 818 290 1
cert_row_4 3 1 2 3 4 8 572 28 3
cert_rows
cert_pivot_2 6 5 0 1
cert_heightProof 4
cert_coverFacet 0 230
cert_cover_5 0 0 0 1 4 5 98 230 1
cert_coverFacet 1 618
cert_cover_5 1 1 0 2 4 5 98 618 1
cert_coverFacet 2 818
cert_cover_5 2 2 0 3 4 7 290 818 1
cert_coverFacet 3 418
cert_cover_2 3 4 0 6 7 162 418 3
cert_coverFacet 4 706
cert_cover_2 4 5 0 6 8 194 706 3
cert_coverFacet 5 572
cert_cover_5 5 3 1 2 3 4 28 572 3
cert_coverFacet 6 108
cert_cover_2 6 2 1 4 5 44 108 3
cert_coverFacet 7 180
cert_cover_2 7 3 1 4 6 52 180 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0370

end
end BundlePart1

section BundlePart2
/- Source: ProjectionCertificates/R_m14e10q1_0382.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0382

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [835, 157, 653, 341, 613, 793, 678, 906, 242, 610, 450, 116, 180, 472, 141, 21, 69, 517, 25, 521, 273, 321, 577, 769, 98, 162, 546, 194, 322, 578, 386, 642, 770, 52, 84, 148, 100, 164, 548, 644, 152, 280, 392, 648, 776, 112, 176, 208, 336, 608, 448]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_835, vertices_157, vertices_653, vertices_341, vertices_613, vertices_793, vertices_678, vertices_906, vertices_242, vertices_610, vertices_450, vertices_116, vertices_180, vertices_472] (by decide +kernel)
  polygons := literalFinset [vertices_141, vertices_21, vertices_69, vertices_517, vertices_25, vertices_521, vertices_273, vertices_321, vertices_577, vertices_769, vertices_98, vertices_162, vertices_546, vertices_194, vertices_322, vertices_578, vertices_386, vertices_642, vertices_770, vertices_52, vertices_84, vertices_148, vertices_100, vertices_164, vertices_548, vertices_644, vertices_152, vertices_280, vertices_392, vertices_648, vertices_776, vertices_112, vertices_176, vertices_208, vertices_336, vertices_608, vertices_448] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_835), (false, vertices_157), (false, vertices_653), (false, vertices_341), (false, vertices_613), (false, vertices_793), (true, vertices_98), (true, vertices_162), (true, vertices_546), (true, vertices_194), (true, vertices_386), (true, vertices_642), (true, vertices_52), (true, vertices_164), (true, vertices_392), (true, vertices_112), (true, vertices_176), (true, vertices_208), (true, vertices_448)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 13 19 15 22 23 24 25 26 27
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_835) then 14 else
  if p.val = (false, vertices_157) then 16 else
  if p.val = (false, vertices_653) then 17 else
  if p.val = (false, vertices_341) then 20 else
  if p.val = (false, vertices_613) then 21 else
  if p.val = (false, vertices_793) then 18 else
  if p.val = (true, vertices_98) then 0 else
  if p.val = (true, vertices_162) then 1 else
  if p.val = (true, vertices_546) then 2 else
  if p.val = (true, vertices_194) then 3 else
  if p.val = (true, vertices_386) then 4 else
  if p.val = (true, vertices_642) then 5 else
  if p.val = (true, vertices_52) then 6 else
  if p.val = (true, vertices_164) then 7 else
  if p.val = (true, vertices_392) then 8 else
  if p.val = (true, vertices_112) then 9 else
  if p.val = (true, vertices_176) then 10 else
  if p.val = (true, vertices_208) then 11 else
  if p.val = (true, vertices_448) then 12 else
  0
cert_priority
cert_nodeAtPriority 0 98 2 162 1 546 194 386 642 52 164 392 112 176 208 448 835 157 653 793 341 613
cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 4 6 8 678 162 1
cert_row_4 1 0 2 6 7 8 906 386 1
cert_row_4 2 0 3 4 5 6 242 98 1
cert_row_4 3 2 3 5 6 7 472 152 2
cert_rows
cert_pivot_2 1 8 0 2
cert_heightProof 4
cert_coverFacet 0 678
cert_cover_5 0 0 0 1 4 6 162 678 1
cert_coverFacet 1 906
cert_cover_5 1 1 0 2 6 7 386 906 1
cert_coverFacet 2 242
cert_cover_5 2 2 0 3 4 5 98 242 1
cert_coverFacet 3 610
cert_cover_2 3 4 0 5 8 98 610 3
cert_coverFacet 4 450
cert_cover_2 4 5 0 6 7 194 450 3
cert_coverFacet 5 116
cert_cover_2 5 3 1 4 5 52 116 3
cert_coverFacet 6 180
cert_cover_2 6 3 1 4 6 52 180 3
cert_coverFacet 7 472
cert_cover_5 7 3 2 3 5 6 152 472 2
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0382

end
end BundlePart2

section BundlePart3
/- Source: ProjectionCertificates/R_m14e10q1_0389.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0389

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [355, 653, 789, 421, 233, 841, 662, 618, 682, 178, 306, 850, 404, 432, 133, 261, 517, 73, 137, 521, 97, 161, 289, 321, 769, 554, 50, 146, 274, 530, 98, 162, 290, 322, 578, 642, 148, 276, 532, 388, 644, 104, 168, 584, 648, 176, 304, 400, 784, 416, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_355, vertices_653, vertices_789, vertices_421, vertices_233, vertices_841, vertices_662, vertices_618, vertices_682, vertices_178, vertices_306, vertices_850, vertices_404, vertices_432] (by decide +kernel)
  polygons := literalFinset [vertices_133, vertices_261, vertices_517, vertices_73, vertices_137, vertices_521, vertices_97, vertices_161, vertices_289, vertices_321, vertices_769, vertices_554, vertices_50, vertices_146, vertices_274, vertices_530, vertices_98, vertices_162, vertices_290, vertices_322, vertices_578, vertices_642, vertices_148, vertices_276, vertices_532, vertices_388, vertices_644, vertices_104, vertices_168, vertices_584, vertices_648, vertices_176, vertices_304, vertices_400, vertices_784, vertices_416, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_355), (false, vertices_653), (false, vertices_789), (false, vertices_421), (false, vertices_233), (false, vertices_841), (true, vertices_554), (true, vertices_50), (true, vertices_146), (true, vertices_274), (true, vertices_530), (true, vertices_162), (true, vertices_578), (true, vertices_642), (true, vertices_148), (true, vertices_176), (true, vertices_304), (true, vertices_400)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 11 14 18 21 22 23 24 25 26
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_355) then 12 else
  if p.val = (false, vertices_653) then 15 else
  if p.val = (false, vertices_789) then 16 else
  if p.val = (false, vertices_421) then 17 else
  if p.val = (false, vertices_233) then 19 else
  if p.val = (false, vertices_841) then 20 else
  if p.val = (true, vertices_554) then 13 else
  if p.val = (true, vertices_50) then 0 else
  if p.val = (true, vertices_146) then 1 else
  if p.val = (true, vertices_274) then 2 else
  if p.val = (true, vertices_530) then 3 else
  if p.val = (true, vertices_162) then 4 else
  if p.val = (true, vertices_578) then 5 else
  if p.val = (true, vertices_642) then 6 else
  if p.val = (true, vertices_148) then 7 else
  if p.val = (true, vertices_176) then 8 else
  if p.val = (true, vertices_304) then 9 else
  if p.val = (true, vertices_400) then 10 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_50), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_146), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_274), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_530), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_162), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_578), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_642), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_148), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_176), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_304), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_400), by decide +kernel⟩
  | 11 => Sum.inl 0
  | 12 => Sum.inr ⟨(false, vertices_355), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_554), by decide +kernel⟩
  | 14 => Sum.inl 1
  | 15 => Sum.inr ⟨(false, vertices_653), by decide +kernel⟩
  | 16 => Sum.inr ⟨(false, vertices_789), by decide +kernel⟩
  | 17 => Sum.inr ⟨(false, vertices_421), by decide +kernel⟩
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
cert_row_2 0 0 2 4 8 554
cert_row_4 1 0 1 3 6 8 662 146 1
cert_row_4 2 0 3 5 7 8 850 274 2
cert_rows_3
cert_pivot_3 1 2 0
cert_heightProof 3
cert_coverFacet 0 662
cert_cover_5 0 1 0 1 3 6 146 662 1
cert_coverFacet 1 618
cert_cover_5 1 0 0 2 4 5 554 618 3
cert_coverFacet 2 682
cert_cover_5 2 0 0 2 4 6 554 682 3
cert_coverFacet 3 178
cert_cover_2 3 3 0 4 6 50 178 3
cert_coverFacet 4 306
cert_cover_2 4 3 0 4 7 50 306 3
cert_coverFacet 5 850
cert_cover_5 5 2 0 3 5 7 274 850 2
cert_coverFacet 6 404
cert_cover_2 6 3 1 6 7 148 404 3
cert_coverFacet 7 432
cert_cover_2 7 4 3 6 7 176 432 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 3 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0389

end
end BundlePart3

section BundlePart4
/- Source: ProjectionCertificates/R_m14e10q1_0390.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0390

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [659, 275, 451, 709, 313, 601, 329, 806, 902, 570, 306, 620, 484, 360, 19, 131, 259, 25, 73, 265, 273, 529, 193, 321, 577, 641, 774, 50, 274, 530, 290, 546, 386, 642, 100, 292, 548, 196, 580, 388, 644, 56, 536, 104, 296, 552, 328, 584, 304, 352, 448]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_659, vertices_275, vertices_451, vertices_709, vertices_313, vertices_601, vertices_329, vertices_806, vertices_902, vertices_570, vertices_306, vertices_620, vertices_484, vertices_360] (by decide +kernel)
  polygons := literalFinset [vertices_19, vertices_131, vertices_259, vertices_25, vertices_73, vertices_265, vertices_273, vertices_529, vertices_193, vertices_321, vertices_577, vertices_641, vertices_774, vertices_50, vertices_274, vertices_530, vertices_290, vertices_546, vertices_386, vertices_642, vertices_100, vertices_292, vertices_548, vertices_196, vertices_580, vertices_388, vertices_644, vertices_56, vertices_536, vertices_104, vertices_296, vertices_552, vertices_328, vertices_584, vertices_304, vertices_352, vertices_448] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_659), (false, vertices_275), (false, vertices_451), (false, vertices_709), (false, vertices_313), (false, vertices_601), (false, vertices_329), (true, vertices_774), (true, vertices_50), (true, vertices_290), (true, vertices_546), (true, vertices_100), (true, vertices_292), (true, vertices_548), (true, vertices_388), (true, vertices_104), (true, vertices_552), (true, vertices_352)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 12 16 18 21 22 23 24 25 26
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_659) then 13 else
  if p.val = (false, vertices_275) then 0 else
  if p.val = (false, vertices_451) then 14 else
  if p.val = (false, vertices_709) then 17 else
  if p.val = (false, vertices_313) then 19 else
  if p.val = (false, vertices_601) then 20 else
  if p.val = (false, vertices_329) then 1 else
  if p.val = (true, vertices_774) then 15 else
  if p.val = (true, vertices_50) then 2 else
  if p.val = (true, vertices_290) then 3 else
  if p.val = (true, vertices_546) then 4 else
  if p.val = (true, vertices_100) then 5 else
  if p.val = (true, vertices_292) then 6 else
  if p.val = (true, vertices_548) then 7 else
  if p.val = (true, vertices_388) then 8 else
  if p.val = (true, vertices_104) then 9 else
  if p.val = (true, vertices_552) then 10 else
  if p.val = (true, vertices_352) then 11 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_275), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_329), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_50), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_290), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_546), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_100), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_292), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_548), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_388), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_104), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_552), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_352), by decide +kernel⟩
  | 12 => Sum.inl 0
  | 13 => Sum.inr ⟨(false, vertices_659), by decide +kernel⟩
  | 14 => Sum.inr ⟨(false, vertices_451), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_774), by decide +kernel⟩
  | 16 => Sum.inl 1
  | 17 => Sum.inr ⟨(false, vertices_709), by decide +kernel⟩
  | 18 => Sum.inl 2
  | 19 => Sum.inr ⟨(false, vertices_313), by decide +kernel⟩
  | 20 => Sum.inr ⟨(false, vertices_601), by decide +kernel⟩
  | 21 => Sum.inl 3
  | 22 => Sum.inl 4
  | 23 => Sum.inl 5
  | 24 => Sum.inl 6
  | 25 => Sum.inl 7
  | 26 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 2 3 4 8 570 50 1
cert_row_2 1 0 1 7 8 774
cert_row_4 2 1 2 4 5 8 620 100 1
cert_row_4 3 1 4 5 6 7 484 100 3
cert_rows
cert_pivot_2 3 0 2 1
cert_heightProof 4
cert_coverFacet 0 806
cert_cover_5 0 1 0 1 4 7 774 806 2
cert_coverFacet 1 902
cert_cover_5 1 1 0 1 6 7 774 902 2
cert_coverFacet 2 570
cert_cover_5 2 0 0 2 3 4 50 570 1
cert_coverFacet 3 306
cert_cover_2 3 3 0 4 7 50 306 3
cert_coverFacet 4 620
cert_cover_5 4 2 1 2 4 5 100 620 1
cert_coverFacet 5 484
cert_cover_5 5 3 1 4 5 6 100 484 3
cert_coverFacet 6 360
cert_cover_2 6 4 2 5 7 104 360 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0390

end
end BundlePart4

section BundlePart5
/- Source: ProjectionCertificates/R_m14e10q1_0391.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0391

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [651, 403, 835, 597, 661, 369, 810, 394, 684, 244, 868, 184, 312, 408, 131, 259, 515, 533, 81, 145, 273, 321, 577, 641, 138, 266, 522, 386, 770, 84, 148, 100, 164, 548, 580, 644, 56, 152, 280, 168, 296, 552, 392, 648, 112, 176, 304, 400, 352, 800, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_651, vertices_403, vertices_835, vertices_597, vertices_661, vertices_369, vertices_810, vertices_394, vertices_684, vertices_244, vertices_868, vertices_184, vertices_312, vertices_408] (by decide +kernel)
  polygons := literalFinset [vertices_131, vertices_259, vertices_515, vertices_533, vertices_81, vertices_145, vertices_273, vertices_321, vertices_577, vertices_641, vertices_138, vertices_266, vertices_522, vertices_386, vertices_770, vertices_84, vertices_148, vertices_100, vertices_164, vertices_548, vertices_580, vertices_644, vertices_56, vertices_152, vertices_280, vertices_168, vertices_296, vertices_552, vertices_392, vertices_648, vertices_112, vertices_176, vertices_304, vertices_400, vertices_352, vertices_800, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_651), (false, vertices_403), (false, vertices_835), (false, vertices_597), (false, vertices_661), (false, vertices_369), (true, vertices_266), (true, vertices_100), (true, vertices_164), (true, vertices_548), (true, vertices_56), (true, vertices_152), (true, vertices_280), (true, vertices_168), (true, vertices_296), (true, vertices_552), (true, vertices_392), (true, vertices_176), (true, vertices_800)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 13 17 20 21 23 24 25 26 27
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_651) then 14 else
  if p.val = (false, vertices_403) then 15 else
  if p.val = (false, vertices_835) then 16 else
  if p.val = (false, vertices_597) then 18 else
  if p.val = (false, vertices_661) then 19 else
  if p.val = (false, vertices_369) then 22 else
  if p.val = (true, vertices_266) then 0 else
  if p.val = (true, vertices_100) then 1 else
  if p.val = (true, vertices_164) then 2 else
  if p.val = (true, vertices_548) then 3 else
  if p.val = (true, vertices_56) then 4 else
  if p.val = (true, vertices_152) then 5 else
  if p.val = (true, vertices_280) then 6 else
  if p.val = (true, vertices_168) then 7 else
  if p.val = (true, vertices_296) then 8 else
  if p.val = (true, vertices_552) then 9 else
  if p.val = (true, vertices_392) then 10 else
  if p.val = (true, vertices_176) then 11 else
  if p.val = (true, vertices_800) then 12 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_266), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_100), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_164), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_548), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_56), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_152), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_280), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_168), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_296), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_552), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_392), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_176), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_800), by decide +kernel⟩
  | 13 => Sum.inl 0
  | 14 => Sum.inr ⟨(false, vertices_651), by decide +kernel⟩
  | 15 => Sum.inr ⟨(false, vertices_403), by decide +kernel⟩
  | 16 => Sum.inr ⟨(false, vertices_835), by decide +kernel⟩
  | 17 => Sum.inl 1
  | 18 => Sum.inr ⟨(false, vertices_597), by decide +kernel⟩
  | 19 => Sum.inr ⟨(false, vertices_661), by decide +kernel⟩
  | 20 => Sum.inl 2
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
cert_coverFacet 5 184
cert_cover_2 5 3 2 4 6 56 184 3
cert_coverFacet 6 312
cert_cover_2 6 3 2 4 7 56 312 3
cert_coverFacet 7 408
cert_cover_2 7 3 2 6 7 152 408 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0391

end
end BundlePart5

section BundlePart6
/- Source: ProjectionCertificates/R_m14e10q1_0393.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0393

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [899, 109, 205, 661, 805, 425, 214, 458, 818, 338, 658, 116, 564, 376, 77, 37, 133, 517, 41, 137, 289, 385, 641, 769, 82, 146, 274, 530, 194, 322, 386, 642, 770, 52, 84, 148, 532, 100, 548, 196, 104, 296, 200, 328, 392, 112, 304, 560, 336, 656, 800]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_899, vertices_109, vertices_205, vertices_661, vertices_805, vertices_425, vertices_214, vertices_458, vertices_818, vertices_338, vertices_658, vertices_116, vertices_564, vertices_376] (by decide +kernel)
  polygons := literalFinset [vertices_77, vertices_37, vertices_133, vertices_517, vertices_41, vertices_137, vertices_289, vertices_385, vertices_641, vertices_769, vertices_82, vertices_146, vertices_274, vertices_530, vertices_194, vertices_322, vertices_386, vertices_642, vertices_770, vertices_52, vertices_84, vertices_148, vertices_532, vertices_100, vertices_548, vertices_196, vertices_104, vertices_296, vertices_200, vertices_328, vertices_392, vertices_112, vertices_304, vertices_560, vertices_336, vertices_656, vertices_800] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_899), (false, vertices_109), (false, vertices_205), (false, vertices_661), (false, vertices_805), (false, vertices_425), (true, vertices_82), (true, vertices_146), (true, vertices_274), (true, vertices_530), (true, vertices_194), (true, vertices_322), (true, vertices_52), (true, vertices_84), (true, vertices_328), (true, vertices_112), (true, vertices_304), (true, vertices_560), (true, vertices_336)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 13 19 15 22 23 24 25 26 27
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_899) then 14 else
  if p.val = (false, vertices_109) then 16 else
  if p.val = (false, vertices_205) then 17 else
  if p.val = (false, vertices_661) then 20 else
  if p.val = (false, vertices_805) then 21 else
  if p.val = (false, vertices_425) then 18 else
  if p.val = (true, vertices_82) then 0 else
  if p.val = (true, vertices_146) then 1 else
  if p.val = (true, vertices_274) then 2 else
  if p.val = (true, vertices_530) then 3 else
  if p.val = (true, vertices_194) then 4 else
  if p.val = (true, vertices_322) then 5 else
  if p.val = (true, vertices_52) then 6 else
  if p.val = (true, vertices_84) then 7 else
  if p.val = (true, vertices_328) then 8 else
  if p.val = (true, vertices_112) then 9 else
  if p.val = (true, vertices_304) then 10 else
  if p.val = (true, vertices_560) then 11 else
  if p.val = (true, vertices_336) then 12 else
  0
cert_priority
cert_nodeAtPriority 0 82 2 146 1 274 530 194 322 52 84 328 112 304 560 336 899 109 205 425 661 805
cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 3 5 6 214 82 1
cert_row_4 1 0 2 5 6 7 458 194 1
cert_row_4 2 0 3 4 7 8 818 274 2
cert_row_4 3 2 3 4 5 7 376 104 1
cert_rows
cert_pivot_2 1 6 0 2
cert_heightProof 4
cert_coverFacet 0 214
cert_cover_5 0 0 0 1 3 5 82 214 1
cert_coverFacet 1 458
cert_cover_5 1 1 0 2 5 6 194 458 1
cert_coverFacet 2 818
cert_cover_5 2 2 0 3 4 7 274 818 2
cert_coverFacet 3 338
cert_cover_2 3 3 0 5 7 82 338 3
cert_coverFacet 4 658
cert_cover_2 4 3 0 6 8 146 658 3
cert_coverFacet 5 116
cert_cover_2 5 3 1 4 5 52 116 3
cert_coverFacet 6 564
cert_cover_2 6 3 1 4 8 52 564 3
cert_coverFacet 7 376
cert_cover_5 7 3 2 3 4 5 104 376 1
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0393

end
end BundlePart6

section BundlePart7
/- Source: ProjectionCertificates/R_m14e10q1_0399.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0399

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [899, 53, 789, 421, 681, 625, 206, 454, 618, 650, 850, 124, 172, 340, 21, 37, 261, 49, 529, 161, 545, 385, 641, 769, 198, 74, 138, 522, 322, 578, 386, 642, 770, 44, 76, 140, 52, 84, 276, 164, 324, 388, 104, 168, 552, 648, 112, 336, 592, 784, 608]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_899, vertices_53, vertices_789, vertices_421, vertices_681, vertices_625, vertices_206, vertices_454, vertices_618, vertices_650, vertices_850, vertices_124, vertices_172, vertices_340] (by decide +kernel)
  polygons := literalFinset [vertices_21, vertices_37, vertices_261, vertices_49, vertices_529, vertices_161, vertices_545, vertices_385, vertices_641, vertices_769, vertices_198, vertices_74, vertices_138, vertices_522, vertices_322, vertices_578, vertices_386, vertices_642, vertices_770, vertices_44, vertices_76, vertices_140, vertices_52, vertices_84, vertices_276, vertices_164, vertices_324, vertices_388, vertices_104, vertices_168, vertices_552, vertices_648, vertices_112, vertices_336, vertices_592, vertices_784, vertices_608] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_899), (false, vertices_53), (false, vertices_789), (false, vertices_421), (false, vertices_681), (false, vertices_625), (true, vertices_198), (true, vertices_74), (true, vertices_138), (true, vertices_522), (true, vertices_322), (true, vertices_578), (true, vertices_44), (true, vertices_76), (true, vertices_140), (true, vertices_84), (true, vertices_324), (true, vertices_104), (true, vertices_336)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 13 16 19 21 23 24 25 26 27
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_899) then 14 else
  if p.val = (false, vertices_53) then 0 else
  if p.val = (false, vertices_789) then 17 else
  if p.val = (false, vertices_421) then 18 else
  if p.val = (false, vertices_681) then 20 else
  if p.val = (false, vertices_625) then 22 else
  if p.val = (true, vertices_198) then 15 else
  if p.val = (true, vertices_74) then 1 else
  if p.val = (true, vertices_138) then 2 else
  if p.val = (true, vertices_522) then 3 else
  if p.val = (true, vertices_322) then 4 else
  if p.val = (true, vertices_578) then 5 else
  if p.val = (true, vertices_44) then 6 else
  if p.val = (true, vertices_76) then 7 else
  if p.val = (true, vertices_140) then 8 else
  if p.val = (true, vertices_84) then 9 else
  if p.val = (true, vertices_324) then 10 else
  if p.val = (true, vertices_104) then 11 else
  if p.val = (true, vertices_336) then 12 else
  0
cert_priority
cert_nodeAtPriority_17 53 74 138 522 322 578 44 76 140 84 324 104 336 899 198 789 421 681 625
cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 1 5 6 198
cert_row_4 1 0 3 5 7 8 850 322 1
cert_row_4 2 0 2 4 5 8 618 74 2
cert_row_4 3 1 2 3 4 5 124 44 2
cert_rows
cert_pivot_2 6 7 0 1
cert_heightProof 4
cert_coverFacet 0 206
cert_cover_5 0 0 0 1 2 5 198 206 2
cert_coverFacet 1 454
cert_cover_5 1 0 0 1 5 7 198 454 3
cert_coverFacet 2 618
cert_cover_5 2 2 0 2 4 5 74 618 2
cert_coverFacet 3 650
cert_cover_2 3 2 0 6 8 138 650 3
cert_coverFacet 4 850
cert_cover_5 4 1 0 3 5 7 322 850 1
cert_coverFacet 5 124
cert_cover_5 5 3 1 2 3 4 44 124 2
cert_coverFacet 6 172
cert_cover_2 6 2 1 4 6 44 172 3
cert_coverFacet 7 340
cert_cover_2 7 3 1 5 7 84 340 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0399

end
end BundlePart7

section BundlePart8
/- Source: ProjectionCertificates/R_m14e10q1_0400.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0400

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [391, 781, 181, 533, 57, 601, 425, 214, 598, 774, 842, 482, 376, 240, 21, 133, 261, 517, 25, 41, 265, 521, 49, 529, 161, 385, 86, 134, 262, 518, 194, 322, 578, 386, 770, 148, 532, 772, 56, 88, 296, 328, 584, 776, 112, 176, 208, 592, 224, 352, 416]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_391, vertices_781, vertices_181, vertices_533, vertices_57, vertices_601, vertices_425, vertices_214, vertices_598, vertices_774, vertices_842, vertices_482, vertices_376, vertices_240] (by decide +kernel)
  polygons := literalFinset [vertices_21, vertices_133, vertices_261, vertices_517, vertices_25, vertices_41, vertices_265, vertices_521, vertices_49, vertices_529, vertices_161, vertices_385, vertices_86, vertices_134, vertices_262, vertices_518, vertices_194, vertices_322, vertices_578, vertices_386, vertices_770, vertices_148, vertices_532, vertices_772, vertices_56, vertices_88, vertices_296, vertices_328, vertices_584, vertices_776, vertices_112, vertices_176, vertices_208, vertices_592, vertices_224, vertices_352, vertices_416] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_391), (false, vertices_781), (false, vertices_181), (false, vertices_533), (false, vertices_57), (false, vertices_601), (false, vertices_425), (true, vertices_86), (true, vertices_518), (true, vertices_194), (true, vertices_322), (true, vertices_578), (true, vertices_770), (true, vertices_328), (true, vertices_112), (true, vertices_208), (true, vertices_224), (true, vertices_352)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 12 15 18 21 22 23 24 25 26
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_391) then 13 else
  if p.val = (false, vertices_781) then 16 else
  if p.val = (false, vertices_181) then 17 else
  if p.val = (false, vertices_533) then 0 else
  if p.val = (false, vertices_57) then 1 else
  if p.val = (false, vertices_601) then 19 else
  if p.val = (false, vertices_425) then 20 else
  if p.val = (true, vertices_86) then 14 else
  if p.val = (true, vertices_518) then 2 else
  if p.val = (true, vertices_194) then 3 else
  if p.val = (true, vertices_322) then 4 else
  if p.val = (true, vertices_578) then 5 else
  if p.val = (true, vertices_770) then 6 else
  if p.val = (true, vertices_328) then 7 else
  if p.val = (true, vertices_112) then 8 else
  if p.val = (true, vertices_208) then 9 else
  if p.val = (true, vertices_224) then 10 else
  if p.val = (true, vertices_352) then 11 else
  0
cert_priority
cert_nodeAtPriority_10 0 533 1 57 518 194 322 578 770 328 112 208 224 352 391 86 781 181 601 425
cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 1 3 5 86
cert_row_4 1 0 2 5 7 8 842 322 1
cert_row_4 2 0 4 5 6 7 482 194 1
cert_row_4 3 2 3 4 5 7 376 56 3
cert_rows
cert_pivot_2 1 8 0 2
cert_heightProof 4
cert_coverFacet 0 214
cert_cover_5 0 0 0 1 3 6 86 214 3
cert_coverFacet 1 598
cert_cover_5 1 0 0 1 3 8 86 598 3
cert_coverFacet 2 774
cert_cover_2 2 1 0 7 8 262 774 3
cert_coverFacet 3 842
cert_cover_5 3 1 0 2 5 7 322 842 1
cert_coverFacet 4 482
cert_cover_5 4 2 0 4 5 6 194 482 1
cert_coverFacet 5 376
cert_cover_5 5 3 2 3 4 5 56 376 3
cert_coverFacet 6 240
cert_cover_2 6 4 3 5 6 112 240 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0400

end
end BundlePart8

section BundlePart9
/- Source: ProjectionCertificates/R_m14e10q1_0406.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0406

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [143, 263, 659, 803, 45, 357, 681, 406, 850, 108, 716, 468, 872, 720, 7, 131, 259, 515, 13, 37, 261, 41, 137, 289, 545, 641, 134, 262, 146, 274, 530, 770, 44, 76, 140, 404, 100, 196, 324, 104, 552, 584, 648, 208, 336, 592, 656, 352, 800, 704, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_143, vertices_263, vertices_659, vertices_803, vertices_45, vertices_357, vertices_681, vertices_406, vertices_850, vertices_108, vertices_716, vertices_468, vertices_872, vertices_720] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_131, vertices_259, vertices_515, vertices_13, vertices_37, vertices_261, vertices_41, vertices_137, vertices_289, vertices_545, vertices_641, vertices_134, vertices_262, vertices_146, vertices_274, vertices_530, vertices_770, vertices_44, vertices_76, vertices_140, vertices_404, vertices_100, vertices_196, vertices_324, vertices_104, vertices_552, vertices_584, vertices_648, vertices_208, vertices_336, vertices_592, vertices_656, vertices_352, vertices_800, vertices_704, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_143), (false, vertices_263), (false, vertices_659), (false, vertices_803), (false, vertices_45), (false, vertices_357), (false, vertices_681), (true, vertices_274), (true, vertices_76), (true, vertices_404), (true, vertices_196), (true, vertices_104), (true, vertices_584), (true, vertices_208), (true, vertices_336), (true, vertices_592), (true, vertices_704), (true, vertices_832)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 12 16 19 21 22 23 24 25 26
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_143) then 13 else
  if p.val = (false, vertices_263) then 0 else
  if p.val = (false, vertices_659) then 14 else
  if p.val = (false, vertices_803) then 15 else
  if p.val = (false, vertices_45) then 1 else
  if p.val = (false, vertices_357) then 17 else
  if p.val = (false, vertices_681) then 20 else
  if p.val = (true, vertices_274) then 2 else
  if p.val = (true, vertices_76) then 3 else
  if p.val = (true, vertices_404) then 18 else
  if p.val = (true, vertices_196) then 4 else
  if p.val = (true, vertices_104) then 5 else
  if p.val = (true, vertices_584) then 6 else
  if p.val = (true, vertices_208) then 7 else
  if p.val = (true, vertices_336) then 8 else
  if p.val = (true, vertices_592) then 9 else
  if p.val = (true, vertices_704) then 10 else
  if p.val = (true, vertices_832) then 11 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_263), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_45), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_274), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_76), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_196), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_104), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_584), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_208), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_336), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_592), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_704), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_832), by decide +kernel⟩
  | 12 => Sum.inl 0
  | 13 => Sum.inr ⟨(false, vertices_143), by decide +kernel⟩
  | 14 => Sum.inr ⟨(false, vertices_659), by decide +kernel⟩
  | 15 => Sum.inr ⟨(false, vertices_803), by decide +kernel⟩
  | 16 => Sum.inl 1
  | 17 => Sum.inr ⟨(false, vertices_357), by decide +kernel⟩
  | 18 => Sum.inr ⟨(true, vertices_404), by decide +kernel⟩
  | 19 => Sum.inl 2
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
cert_row_4 0 0 3 5 7 8 850 274 2
cert_row_2 1 1 3 6 7 404
cert_row_4 2 1 2 5 6 8 716 76 3
cert_row_4 3 2 4 5 7 8 872 104 3
cert_rows
cert_pivot_2 0 3 1 2
cert_heightProof 4
cert_coverFacet 0 406
cert_cover_5 0 1 0 1 3 6 134 406 2
cert_coverFacet 1 850
cert_cover_5 1 0 0 3 5 7 274 850 2
cert_coverFacet 2 108
cert_cover_2 2 2 1 4 5 44 108 3
cert_coverFacet 3 716
cert_cover_5 3 2 1 2 5 6 76 716 3
cert_coverFacet 4 468
cert_cover_5 4 1 1 3 5 6 404 468 2
cert_coverFacet 5 872
cert_cover_5 5 3 2 4 5 7 104 872 3
cert_coverFacet 6 720
cert_cover_2 6 5 3 6 8 208 720 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0406

end
end BundlePart9

section BundlePart10
/- Source: ProjectionCertificates/R_m14e10q1_0407.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0407

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [59, 203, 307, 835, 709, 681, 801, 454, 154, 402, 668, 852, 404, 824, 11, 51, 67, 259, 41, 137, 289, 545, 193, 577, 641, 769, 26, 138, 146, 274, 194, 322, 386, 148, 276, 532, 196, 324, 580, 388, 644, 56, 152, 536, 552, 648, 304, 400, 784, 800, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_59, vertices_203, vertices_307, vertices_835, vertices_709, vertices_681, vertices_801, vertices_454, vertices_154, vertices_402, vertices_668, vertices_852, vertices_404, vertices_824] (by decide +kernel)
  polygons := literalFinset [vertices_11, vertices_51, vertices_67, vertices_259, vertices_41, vertices_137, vertices_289, vertices_545, vertices_193, vertices_577, vertices_641, vertices_769, vertices_26, vertices_138, vertices_146, vertices_274, vertices_194, vertices_322, vertices_386, vertices_148, vertices_276, vertices_532, vertices_196, vertices_324, vertices_580, vertices_388, vertices_644, vertices_56, vertices_152, vertices_536, vertices_552, vertices_648, vertices_304, vertices_400, vertices_784, vertices_800, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_59), (false, vertices_203), (false, vertices_307), (false, vertices_835), (false, vertices_709), (false, vertices_681), (false, vertices_801), (true, vertices_146), (true, vertices_386), (true, vertices_148), (true, vertices_276), (true, vertices_532), (true, vertices_324), (true, vertices_388), (true, vertices_152), (true, vertices_536), (true, vertices_400), (true, vertices_784)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 17 12 14 21 22 23 24 25 26
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_59) then 18 else
  if p.val = (false, vertices_203) then 15 else
  if p.val = (false, vertices_307) then 19 else
  if p.val = (false, vertices_835) then 20 else
  if p.val = (false, vertices_709) then 13 else
  if p.val = (false, vertices_681) then 16 else
  if p.val = (false, vertices_801) then 0 else
  if p.val = (true, vertices_146) then 1 else
  if p.val = (true, vertices_386) then 2 else
  if p.val = (true, vertices_148) then 3 else
  if p.val = (true, vertices_276) then 4 else
  if p.val = (true, vertices_532) then 5 else
  if p.val = (true, vertices_324) then 6 else
  if p.val = (true, vertices_388) then 7 else
  if p.val = (true, vertices_152) then 8 else
  if p.val = (true, vertices_536) then 9 else
  if p.val = (true, vertices_400) then 10 else
  if p.val = (true, vertices_784) then 11 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_801), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_146), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_386), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_148), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_276), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_532), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_324), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_388), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_152), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_536), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_400), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_784), by decide +kernel⟩
  | 12 => Sum.inl 1
  | 13 => Sum.inr ⟨(false, vertices_709), by decide +kernel⟩
  | 14 => Sum.inl 2
  | 15 => Sum.inr ⟨(false, vertices_203), by decide +kernel⟩
  | 16 => Sum.inr ⟨(false, vertices_681), by decide +kernel⟩
  | 17 => Sum.inl 0
  | 18 => Sum.inr ⟨(false, vertices_59), by decide +kernel⟩
  | 19 => Sum.inr ⟨(false, vertices_307), by decide +kernel⟩
  | 20 => Sum.inr ⟨(false, vertices_835), by decide +kernel⟩
  | 21 => Sum.inl 3
  | 22 => Sum.inl 4
  | 23 => Sum.inl 5
  | 24 => Sum.inl 6
  | 25 => Sum.inl 7
  | 26 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 5 6 7 454 194 1
cert_row_4 1 1 2 3 6 8 668 148 1
cert_row_4 2 1 3 5 7 8 852 276 2
cert_row_4 3 2 3 4 7 8 824 56 3
cert_rows
cert_pivot_2 0 6 1 2
cert_heightProof 4
cert_coverFacet 0 454
cert_cover_5 0 0 0 1 5 6 194 454 1
cert_coverFacet 1 154
cert_cover_2 1 2 0 3 6 26 154 3
cert_coverFacet 2 402
cert_cover_2 2 3 0 6 7 146 402 3
cert_coverFacet 3 668
cert_cover_5 3 1 1 2 3 6 148 668 1
cert_coverFacet 4 852
cert_cover_5 4 2 1 3 5 7 276 852 2
cert_coverFacet 5 404
cert_cover_2 5 3 1 6 7 148 404 3
cert_coverFacet 6 824
cert_cover_5 6 3 2 3 4 7 56 824 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0407

end
end BundlePart10

section BundlePart11
/- Source: ProjectionCertificates/R_m14e10q1_0444.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0444

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [651, 301, 397, 181, 569, 721, 454, 810, 394, 850, 706, 820, 212, 340, 269, 37, 133, 41, 137, 521, 49, 145, 529, 641, 138, 266, 522, 194, 322, 578, 386, 642, 770, 52, 84, 148, 276, 292, 196, 324, 388, 296, 552, 392, 560, 208, 336, 592, 784, 800, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_651, vertices_301, vertices_397, vertices_181, vertices_569, vertices_721, vertices_454, vertices_810, vertices_394, vertices_850, vertices_706, vertices_820, vertices_212, vertices_340] (by decide +kernel)
  polygons := literalFinset [vertices_269, vertices_37, vertices_133, vertices_41, vertices_137, vertices_521, vertices_49, vertices_145, vertices_529, vertices_641, vertices_138, vertices_266, vertices_522, vertices_194, vertices_322, vertices_578, vertices_386, vertices_642, vertices_770, vertices_52, vertices_84, vertices_148, vertices_276, vertices_292, vertices_196, vertices_324, vertices_388, vertices_296, vertices_552, vertices_392, vertices_560, vertices_208, vertices_336, vertices_592, vertices_784, vertices_800, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_651), (false, vertices_301), (false, vertices_397), (false, vertices_181), (false, vertices_569), (false, vertices_721), (true, vertices_266), (true, vertices_194), (true, vertices_322), (true, vertices_578), (true, vertices_386), (true, vertices_770), (true, vertices_84), (true, vertices_276), (true, vertices_196), (true, vertices_324), (true, vertices_336), (true, vertices_784), (true, vertices_800)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 13 15 19 21 23 24 25 26 27
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_651) then 14 else
  if p.val = (false, vertices_301) then 16 else
  if p.val = (false, vertices_397) then 17 else
  if p.val = (false, vertices_181) then 18 else
  if p.val = (false, vertices_569) then 20 else
  if p.val = (false, vertices_721) then 22 else
  if p.val = (true, vertices_266) then 0 else
  if p.val = (true, vertices_194) then 1 else
  if p.val = (true, vertices_322) then 2 else
  if p.val = (true, vertices_578) then 3 else
  if p.val = (true, vertices_386) then 4 else
  if p.val = (true, vertices_770) then 5 else
  if p.val = (true, vertices_84) then 6 else
  if p.val = (true, vertices_276) then 7 else
  if p.val = (true, vertices_196) then 8 else
  if p.val = (true, vertices_324) then 9 else
  if p.val = (true, vertices_336) then 10 else
  if p.val = (true, vertices_784) then 11 else
  if p.val = (true, vertices_800) then 12 else
  0
cert_priority
cert_nodeAtPriority_11 266 194 322 578 386 770 84 276 196 324 336 784 800 651 301 397 181 569 721
cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 5 6 7 454 194 1
cert_row_4 1 0 2 4 7 8 810 266 2
cert_row_4 2 0 3 5 7 8 850 322 1
cert_row_4 3 1 3 4 7 8 820 52 3
cert_rows
cert_pivot_2 6 2 0 1
cert_heightProof 4
cert_coverFacet 0 454
cert_cover_5 0 0 0 1 5 6 194 454 1
cert_coverFacet 1 810
cert_cover_5 1 1 0 2 4 7 266 810 2
cert_coverFacet 2 394
cert_cover_2 2 2 0 6 7 138 394 3
cert_coverFacet 3 850
cert_cover_5 3 2 0 3 5 7 322 850 1
cert_coverFacet 4 706
cert_cover_2 4 5 0 6 8 194 706 3
cert_coverFacet 5 820
cert_cover_5 5 3 1 3 4 7 52 820 3
cert_coverFacet 6 212
cert_cover_2 6 3 1 5 6 84 212 3
cert_coverFacet 7 340
cert_cover_2 7 3 1 5 7 84 340 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0444

end
end BundlePart11

section BundlePart12
/- Source: ProjectionCertificates/R_m14e10q1_0465.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0465

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [803, 677, 665, 425, 841, 118, 566, 602, 482, 834, 220, 660, 228, 456, 137, 265, 521, 161, 289, 545, 641, 769, 54, 82, 530, 98, 290, 546, 322, 578, 770, 84, 148, 532, 100, 164, 548, 196, 644, 88, 152, 536, 200, 328, 584, 392, 656, 224, 416, 448, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_803, vertices_677, vertices_665, vertices_425, vertices_841, vertices_118, vertices_566, vertices_602, vertices_482, vertices_834, vertices_220, vertices_660, vertices_228, vertices_456] (by decide +kernel)
  polygons := literalFinset [vertices_137, vertices_265, vertices_521, vertices_161, vertices_289, vertices_545, vertices_641, vertices_769, vertices_54, vertices_82, vertices_530, vertices_98, vertices_290, vertices_546, vertices_322, vertices_578, vertices_770, vertices_84, vertices_148, vertices_532, vertices_100, vertices_164, vertices_548, vertices_196, vertices_644, vertices_88, vertices_152, vertices_536, vertices_200, vertices_328, vertices_584, vertices_392, vertices_656, vertices_224, vertices_416, vertices_448, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_803), (false, vertices_677), (false, vertices_665), (false, vertices_425), (false, vertices_841), (true, vertices_54), (true, vertices_82), (true, vertices_530), (true, vertices_98), (true, vertices_322), (true, vertices_578), (true, vertices_84), (true, vertices_148), (true, vertices_532), (true, vertices_100), (true, vertices_196), (true, vertices_88), (true, vertices_200), (true, vertices_224), (true, vertices_448)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 14 17 19 23 24 25 26 27 28
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_803) then 15 else
  if p.val = (false, vertices_677) then 18 else
  if p.val = (false, vertices_665) then 20 else
  if p.val = (false, vertices_425) then 21 else
  if p.val = (false, vertices_841) then 22 else
  if p.val = (true, vertices_54) then 16 else
  if p.val = (true, vertices_82) then 0 else
  if p.val = (true, vertices_530) then 1 else
  if p.val = (true, vertices_98) then 2 else
  if p.val = (true, vertices_322) then 3 else
  if p.val = (true, vertices_578) then 4 else
  if p.val = (true, vertices_84) then 5 else
  if p.val = (true, vertices_148) then 6 else
  if p.val = (true, vertices_532) then 7 else
  if p.val = (true, vertices_100) then 8 else
  if p.val = (true, vertices_196) then 9 else
  if p.val = (true, vertices_88) then 10 else
  if p.val = (true, vertices_200) then 11 else
  if p.val = (true, vertices_224) then 12 else
  if p.val = (true, vertices_448) then 13 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_82), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_530), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_98), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_322), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_578), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_84), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_148), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_532), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_100), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_196), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_88), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_200), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_224), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_448), by decide +kernel⟩
  | 14 => Sum.inl 0
  | 15 => Sum.inr ⟨(false, vertices_803), by decide +kernel⟩
  | 16 => Sum.inr ⟨(true, vertices_54), by decide +kernel⟩
  | 17 => Sum.inl 1
  | 18 => Sum.inr ⟨(false, vertices_677), by decide +kernel⟩
  | 19 => Sum.inl 2
  | 20 => Sum.inr ⟨(false, vertices_665), by decide +kernel⟩
  | 21 => Sum.inr ⟨(false, vertices_425), by decide +kernel⟩
  | 22 => Sum.inr ⟨(false, vertices_841), by decide +kernel⟩
  | 23 => Sum.inl 3
  | 24 => Sum.inl 4
  | 25 => Sum.inl 5
  | 26 => Sum.inl 6
  | 27 => Sum.inl 7
  | 28 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 2 3 5 8 602 82 1
cert_row_4 1 0 4 5 6 7 482 98 3
cert_row_2 2 0 1 3 4 54
cert_row_4 3 1 2 3 5 6 220 84 1
cert_rows
cert_pivot_2 8 7 0 1
cert_heightProof 4
cert_coverFacet 0 118
cert_cover_5 0 2 0 1 3 5 54 118 3
cert_coverFacet 1 566
cert_cover_5 1 2 0 1 3 8 54 566 3
cert_coverFacet 2 602
cert_cover_5 2 0 0 2 3 5 82 602 1
cert_coverFacet 3 482
cert_cover_5 3 1 0 4 5 6 98 482 3
cert_coverFacet 4 834
cert_cover_2 4 5 0 7 8 322 834 3
cert_coverFacet 5 220
cert_cover_5 5 3 1 2 3 5 84 220 1
cert_coverFacet 6 660
cert_cover_2 6 3 1 6 8 148 660 3
cert_coverFacet 7 228
cert_cover_2 7 4 1 5 6 100 228 3
cert_coverFacet 8 456
cert_cover_2 8 5 2 6 7 200 456 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0465

end
end BundlePart12

section BundlePart13
/- Source: ProjectionCertificates/R_m14e10q1_0495.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0495

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [327, 285, 141, 709, 905, 865, 214, 278, 314, 242, 354, 188, 744, 808, 13, 69, 133, 261, 137, 265, 321, 577, 641, 769, 22, 70, 262, 50, 210, 274, 98, 290, 322, 28, 140, 148, 276, 196, 56, 280, 168, 296, 552, 648, 776, 176, 224, 352, 608, 800, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_327, vertices_285, vertices_141, vertices_709, vertices_905, vertices_865, vertices_214, vertices_278, vertices_314, vertices_242, vertices_354, vertices_188, vertices_744, vertices_808] (by decide +kernel)
  polygons := literalFinset [vertices_13, vertices_69, vertices_133, vertices_261, vertices_137, vertices_265, vertices_321, vertices_577, vertices_641, vertices_769, vertices_22, vertices_70, vertices_262, vertices_50, vertices_210, vertices_274, vertices_98, vertices_290, vertices_322, vertices_28, vertices_140, vertices_148, vertices_276, vertices_196, vertices_56, vertices_280, vertices_168, vertices_296, vertices_552, vertices_648, vertices_776, vertices_176, vertices_224, vertices_352, vertices_608, vertices_800, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_327), (false, vertices_285), (false, vertices_141), (false, vertices_709), (false, vertices_905), (false, vertices_865), (true, vertices_22), (true, vertices_50), (true, vertices_210), (true, vertices_274), (true, vertices_98), (true, vertices_290), (true, vertices_148), (true, vertices_56), (true, vertices_168), (true, vertices_296), (true, vertices_552), (true, vertices_176), (true, vertices_224)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 13 16 19 21 22 24 25 26 27
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_327) then 14 else
  if p.val = (false, vertices_285) then 17 else
  if p.val = (false, vertices_141) then 0 else
  if p.val = (false, vertices_709) then 18 else
  if p.val = (false, vertices_905) then 20 else
  if p.val = (false, vertices_865) then 23 else
  if p.val = (true, vertices_22) then 1 else
  if p.val = (true, vertices_50) then 2 else
  if p.val = (true, vertices_210) then 15 else
  if p.val = (true, vertices_274) then 3 else
  if p.val = (true, vertices_98) then 4 else
  if p.val = (true, vertices_290) then 5 else
  if p.val = (true, vertices_148) then 6 else
  if p.val = (true, vertices_56) then 7 else
  if p.val = (true, vertices_168) then 8 else
  if p.val = (true, vertices_296) then 9 else
  if p.val = (true, vertices_552) then 10 else
  if p.val = (true, vertices_176) then 11 else
  if p.val = (true, vertices_224) then 12 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_141), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_22), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_50), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_274), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_98), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_290), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_148), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_56), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_168), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_296), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_552), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_176), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_224), by decide +kernel⟩
  | 13 => Sum.inl 0
  | 14 => Sum.inr ⟨(false, vertices_327), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_210), by decide +kernel⟩
  | 16 => Sum.inl 1
  | 17 => Sum.inr ⟨(false, vertices_285), by decide +kernel⟩
  | 18 => Sum.inr ⟨(false, vertices_709), by decide +kernel⟩
  | 19 => Sum.inl 2
  | 20 => Sum.inr ⟨(false, vertices_905), by decide +kernel⟩
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
cert_row_4 0 0 2 3 4 7 314 50 1
cert_row_2 1 0 3 5 6 210
cert_row_4 2 1 2 3 4 6 188 28 3
cert_row_4 3 2 4 5 6 8 744 168 2
cert_rows
cert_pivot_2 7 0 1 2
cert_heightProof 4
cert_coverFacet 0 214
cert_cover_5 0 1 0 1 3 5 22 214 3
cert_coverFacet 1 278
cert_cover_2 1 1 0 3 7 22 278 3
cert_coverFacet 2 314
cert_cover_5 2 0 0 2 3 4 50 314 1
cert_coverFacet 3 242
cert_cover_5 3 1 0 3 4 5 50 242 3
cert_coverFacet 4 354
cert_cover_2 4 4 0 5 7 98 354 3
cert_coverFacet 5 188
cert_cover_5 5 2 1 2 3 4 28 188 3
cert_coverFacet 6 744
cert_cover_5 6 3 2 4 5 6 168 744 2
cert_coverFacet 7 808
cert_cover_2 7 4 2 7 8 296 808 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0495

end
end BundlePart13

section BundlePart14
/- Source: ProjectionCertificates/R_m14e10q1_0505.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0505

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [327, 285, 141, 709, 681, 841, 214, 278, 314, 242, 354, 188, 808, 992, 13, 69, 133, 261, 137, 265, 521, 321, 577, 641, 22, 70, 262, 50, 210, 274, 98, 290, 322, 28, 140, 148, 276, 196, 56, 280, 168, 296, 552, 776, 176, 224, 352, 672, 800, 704, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_327, vertices_285, vertices_141, vertices_709, vertices_681, vertices_841, vertices_214, vertices_278, vertices_314, vertices_242, vertices_354, vertices_188, vertices_808, vertices_992] (by decide +kernel)
  polygons := literalFinset [vertices_13, vertices_69, vertices_133, vertices_261, vertices_137, vertices_265, vertices_521, vertices_321, vertices_577, vertices_641, vertices_22, vertices_70, vertices_262, vertices_50, vertices_210, vertices_274, vertices_98, vertices_290, vertices_322, vertices_28, vertices_140, vertices_148, vertices_276, vertices_196, vertices_56, vertices_280, vertices_168, vertices_296, vertices_552, vertices_776, vertices_176, vertices_224, vertices_352, vertices_672, vertices_800, vertices_704, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_327), (false, vertices_285), (false, vertices_141), (false, vertices_709), (false, vertices_681), (false, vertices_841), (true, vertices_22), (true, vertices_50), (true, vertices_210), (true, vertices_274), (true, vertices_98), (true, vertices_290), (true, vertices_148), (true, vertices_56), (true, vertices_296), (true, vertices_176), (true, vertices_224), (true, vertices_352), (true, vertices_800)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 13 16 19 22 23 24 25 26 27
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_327) then 14 else
  if p.val = (false, vertices_285) then 17 else
  if p.val = (false, vertices_141) then 0 else
  if p.val = (false, vertices_709) then 18 else
  if p.val = (false, vertices_681) then 20 else
  if p.val = (false, vertices_841) then 21 else
  if p.val = (true, vertices_22) then 1 else
  if p.val = (true, vertices_50) then 2 else
  if p.val = (true, vertices_210) then 15 else
  if p.val = (true, vertices_274) then 3 else
  if p.val = (true, vertices_98) then 4 else
  if p.val = (true, vertices_290) then 5 else
  if p.val = (true, vertices_148) then 6 else
  if p.val = (true, vertices_56) then 7 else
  if p.val = (true, vertices_296) then 8 else
  if p.val = (true, vertices_176) then 9 else
  if p.val = (true, vertices_224) then 10 else
  if p.val = (true, vertices_352) then 11 else
  if p.val = (true, vertices_800) then 12 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_141), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_22), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_50), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_274), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_98), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_290), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_148), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_56), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_296), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_176), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_224), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_352), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_800), by decide +kernel⟩
  | 13 => Sum.inl 0
  | 14 => Sum.inr ⟨(false, vertices_327), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_210), by decide +kernel⟩
  | 16 => Sum.inl 1
  | 17 => Sum.inr ⟨(false, vertices_285), by decide +kernel⟩
  | 18 => Sum.inr ⟨(false, vertices_709), by decide +kernel⟩
  | 19 => Sum.inl 2
  | 20 => Sum.inr ⟨(false, vertices_681), by decide +kernel⟩
  | 21 => Sum.inr ⟨(false, vertices_841), by decide +kernel⟩
  | 22 => Sum.inl 3
  | 23 => Sum.inl 4
  | 24 => Sum.inl 5
  | 25 => Sum.inl 6
  | 26 => Sum.inl 7
  | 27 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 1 2 3 4 6 188 28 3
cert_row_4 1 0 2 3 4 7 314 50 1
cert_row_2 2 0 3 5 6 210
cert_row_4 3 4 5 6 7 8 992 224 3
cert_rows
cert_pivot_2 1 2 0 4
cert_heightProof 4
cert_coverFacet 0 214
cert_cover_5 0 2 0 1 3 5 22 214 3
cert_coverFacet 1 278
cert_cover_2 1 1 0 3 7 22 278 3
cert_coverFacet 2 314
cert_cover_5 2 1 0 2 3 4 50 314 1
cert_coverFacet 3 242
cert_cover_5 3 2 0 3 4 5 50 242 3
cert_coverFacet 4 354
cert_cover_2 4 4 0 5 7 98 354 3
cert_coverFacet 5 188
cert_cover_5 5 0 1 2 3 4 28 188 3
cert_coverFacet 6 808
cert_cover_2 6 4 2 7 8 296 808 3
cert_coverFacet 7 992
cert_cover_5 7 3 4 5 6 7 224 992 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0505

end
end BundlePart14

section BundlePart15
/- Source: ProjectionCertificates/R_m14e10q1_0508.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0508

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [299, 709, 617, 777, 913, 481, 558, 118, 662, 778, 370, 786, 468, 612, 41, 265, 521, 97, 289, 193, 577, 385, 641, 769, 22, 38, 518, 42, 266, 522, 114, 274, 530, 290, 770, 84, 148, 100, 548, 196, 580, 644, 552, 776, 336, 400, 656, 784, 352, 608, 448]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_299, vertices_709, vertices_617, vertices_777, vertices_913, vertices_481, vertices_558, vertices_118, vertices_662, vertices_778, vertices_370, vertices_786, vertices_468, vertices_612] (by decide +kernel)
  polygons := literalFinset [vertices_41, vertices_265, vertices_521, vertices_97, vertices_289, vertices_193, vertices_577, vertices_385, vertices_641, vertices_769, vertices_22, vertices_38, vertices_518, vertices_42, vertices_266, vertices_522, vertices_114, vertices_274, vertices_530, vertices_290, vertices_770, vertices_84, vertices_148, vertices_100, vertices_548, vertices_196, vertices_580, vertices_644, vertices_552, vertices_776, vertices_336, vertices_400, vertices_656, vertices_784, vertices_352, vertices_608, vertices_448] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_299), (false, vertices_709), (false, vertices_617), (false, vertices_777), (false, vertices_913), (false, vertices_481), (true, vertices_22), (true, vertices_38), (true, vertices_518), (true, vertices_522), (true, vertices_114), (true, vertices_274), (true, vertices_530), (true, vertices_770), (true, vertices_84), (true, vertices_148), (true, vertices_100), (true, vertices_548), (true, vertices_336)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 13 16 18 20 22 24 25 26 27
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_299) then 14 else
  if p.val = (false, vertices_709) then 17 else
  if p.val = (false, vertices_617) then 19 else
  if p.val = (false, vertices_777) then 0 else
  if p.val = (false, vertices_913) then 21 else
  if p.val = (false, vertices_481) then 23 else
  if p.val = (true, vertices_22) then 1 else
  if p.val = (true, vertices_38) then 2 else
  if p.val = (true, vertices_518) then 3 else
  if p.val = (true, vertices_522) then 4 else
  if p.val = (true, vertices_114) then 15 else
  if p.val = (true, vertices_274) then 5 else
  if p.val = (true, vertices_530) then 6 else
  if p.val = (true, vertices_770) then 7 else
  if p.val = (true, vertices_84) then 8 else
  if p.val = (true, vertices_148) then 9 else
  if p.val = (true, vertices_100) then 10 else
  if p.val = (true, vertices_548) then 11 else
  if p.val = (true, vertices_336) then 12 else
  0
cert_priority
cert_nodeAtPriority_49 777 22 38 518 522 274 530 770 84 148 100 548 336 299 114 709 617 913 481
cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 2 4 8 558 38 2
cert_row_2 1 0 3 4 5 114
cert_row_4 2 0 1 3 6 8 662 22 3
cert_row_4 3 1 3 5 6 7 468 84 3
cert_rows
cert_pivot_2 2 4 0 1
cert_heightProof 4
cert_coverFacet 0 558
cert_cover_5 0 0 0 1 2 4 38 558 2
cert_coverFacet 1 118
cert_cover_5 1 1 0 1 3 4 22 118 3
cert_coverFacet 2 662
cert_cover_5 2 2 0 1 3 6 22 662 3
cert_coverFacet 3 778
cert_cover_2 3 2 0 7 8 266 778 3
cert_coverFacet 4 370
cert_cover_5 4 1 0 3 4 7 114 370 3
cert_coverFacet 5 786
cert_cover_2 5 3 0 7 8 274 786 3
cert_coverFacet 6 468
cert_cover_5 6 3 1 3 5 6 84 468 3
cert_coverFacet 7 612
cert_cover_2 7 4 1 5 8 100 612 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0508

end
end BundlePart15

section BundlePart16
/- Source: ProjectionCertificates/R_m14e10q1_0510.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0510

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [659, 357, 681, 433, 849, 609, 302, 654, 342, 598, 394, 402, 620, 424, 145, 273, 529, 97, 161, 289, 545, 321, 577, 641, 14, 86, 262, 518, 138, 266, 146, 274, 530, 386, 642, 44, 524, 100, 292, 324, 580, 168, 296, 552, 392, 648, 336, 592, 400, 608, 416]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_659, vertices_357, vertices_681, vertices_433, vertices_849, vertices_609, vertices_302, vertices_654, vertices_342, vertices_598, vertices_394, vertices_402, vertices_620, vertices_424] (by decide +kernel)
  polygons := literalFinset [vertices_145, vertices_273, vertices_529, vertices_97, vertices_161, vertices_289, vertices_545, vertices_321, vertices_577, vertices_641, vertices_14, vertices_86, vertices_262, vertices_518, vertices_138, vertices_266, vertices_146, vertices_274, vertices_530, vertices_386, vertices_642, vertices_44, vertices_524, vertices_100, vertices_292, vertices_324, vertices_580, vertices_168, vertices_296, vertices_552, vertices_392, vertices_648, vertices_336, vertices_592, vertices_400, vertices_608, vertices_416] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_659), (false, vertices_357), (false, vertices_681), (false, vertices_433), (false, vertices_849), (false, vertices_609), (true, vertices_14), (true, vertices_86), (true, vertices_262), (true, vertices_518), (true, vertices_138), (true, vertices_266), (true, vertices_274), (true, vertices_386), (true, vertices_44), (true, vertices_524), (true, vertices_580), (true, vertices_296), (true, vertices_392)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 13 16 18 20 23 24 25 26 27
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_659) then 14 else
  if p.val = (false, vertices_357) then 17 else
  if p.val = (false, vertices_681) then 19 else
  if p.val = (false, vertices_433) then 21 else
  if p.val = (false, vertices_849) then 22 else
  if p.val = (false, vertices_609) then 0 else
  if p.val = (true, vertices_14) then 1 else
  if p.val = (true, vertices_86) then 15 else
  if p.val = (true, vertices_262) then 2 else
  if p.val = (true, vertices_518) then 3 else
  if p.val = (true, vertices_138) then 4 else
  if p.val = (true, vertices_266) then 5 else
  if p.val = (true, vertices_274) then 6 else
  if p.val = (true, vertices_386) then 7 else
  if p.val = (true, vertices_44) then 8 else
  if p.val = (true, vertices_524) then 9 else
  if p.val = (true, vertices_580) then 10 else
  if p.val = (true, vertices_296) then 11 else
  if p.val = (true, vertices_392) then 12 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_609), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_14), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_262), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_518), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_138), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_266), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_274), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_386), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_44), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_524), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_580), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_296), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_392), by decide +kernel⟩
  | 13 => Sum.inl 0
  | 14 => Sum.inr ⟨(false, vertices_659), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_86), by decide +kernel⟩
  | 16 => Sum.inl 1
  | 17 => Sum.inr ⟨(false, vertices_357), by decide +kernel⟩
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
cert_row_2 0 0 1 3 5 86
cert_row_4 1 0 1 2 4 7 302 14 3
cert_row_4 2 0 1 2 6 8 654 14 3
cert_row_4 3 1 2 4 5 8 620 44 3
cert_rows
cert_pivot_2 3 7 0 1
cert_heightProof 4
cert_coverFacet 0 302
cert_cover_5 0 1 0 1 2 4 14 302 3
cert_coverFacet 1 654
cert_cover_5 1 2 0 1 2 6 14 654 3
cert_coverFacet 2 342
cert_cover_5 2 0 0 1 3 7 86 342 3
cert_coverFacet 3 598
cert_cover_5 3 0 0 1 3 8 86 598 3
cert_coverFacet 4 394
cert_cover_2 4 2 0 6 7 138 394 3
cert_coverFacet 5 402
cert_cover_2 5 3 0 6 7 146 402 3
cert_coverFacet 6 620
cert_cover_5 6 3 1 2 4 5 44 620 3
cert_coverFacet 7 424
cert_cover_2 7 4 2 6 7 168 424 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0510

end
end BundlePart16

section BundlePart17
/- Source: ProjectionCertificates/R_m14e10q1_0513.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0513

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [787, 357, 677, 773, 665, 433, 838, 218, 538, 618, 466, 612, 488, 680, 37, 261, 517, 145, 273, 529, 161, 289, 641, 769, 26, 74, 522, 210, 274, 530, 322, 578, 770, 100, 548, 324, 580, 772, 152, 536, 104, 168, 552, 200, 648, 400, 352, 608, 416, 672, 448]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_787, vertices_357, vertices_677, vertices_773, vertices_665, vertices_433, vertices_838, vertices_218, vertices_538, vertices_618, vertices_466, vertices_612, vertices_488, vertices_680] (by decide +kernel)
  polygons := literalFinset [vertices_37, vertices_261, vertices_517, vertices_145, vertices_273, vertices_529, vertices_161, vertices_289, vertices_641, vertices_769, vertices_26, vertices_74, vertices_522, vertices_210, vertices_274, vertices_530, vertices_322, vertices_578, vertices_770, vertices_100, vertices_548, vertices_324, vertices_580, vertices_772, vertices_152, vertices_536, vertices_104, vertices_168, vertices_552, vertices_200, vertices_648, vertices_400, vertices_352, vertices_608, vertices_416, vertices_672, vertices_448] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_787), (false, vertices_357), (false, vertices_677), (false, vertices_773), (false, vertices_665), (false, vertices_433), (true, vertices_26), (true, vertices_74), (true, vertices_522), (true, vertices_210), (true, vertices_322), (true, vertices_578), (true, vertices_580), (true, vertices_104), (true, vertices_168), (true, vertices_552), (true, vertices_200), (true, vertices_608), (true, vertices_448)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 13 16 19 21 23 24 25 26 27
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_787) then 14 else
  if p.val = (false, vertices_357) then 17 else
  if p.val = (false, vertices_677) then 18 else
  if p.val = (false, vertices_773) then 0 else
  if p.val = (false, vertices_665) then 20 else
  if p.val = (false, vertices_433) then 22 else
  if p.val = (true, vertices_26) then 1 else
  if p.val = (true, vertices_74) then 2 else
  if p.val = (true, vertices_522) then 3 else
  if p.val = (true, vertices_210) then 15 else
  if p.val = (true, vertices_322) then 4 else
  if p.val = (true, vertices_578) then 5 else
  if p.val = (true, vertices_580) then 6 else
  if p.val = (true, vertices_104) then 7 else
  if p.val = (true, vertices_168) then 8 else
  if p.val = (true, vertices_552) then 9 else
  if p.val = (true, vertices_200) then 10 else
  if p.val = (true, vertices_608) then 11 else
  if p.val = (true, vertices_448) then 12 else
  0
cert_priority
cert_nodeAtPriority_17 773 26 74 522 322 578 580 104 168 552 200 608 448 787 210 357 677 665 433
cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 3 5 6 210
cert_row_4 1 0 1 5 7 8 838 322 1
cert_row_4 2 0 2 4 5 8 618 74 2
cert_row_4 3 2 4 5 6 7 488 104 3
cert_rows
cert_pivot_2 3 1 0 2
cert_heightProof 4
cert_coverFacet 0 838
cert_cover_5 0 1 0 1 5 7 322 838 1
cert_coverFacet 1 218
cert_cover_5 1 0 0 2 3 5 26 218 3
cert_coverFacet 2 538
cert_cover_2 2 2 0 3 8 26 538 3
cert_coverFacet 3 618
cert_cover_5 3 2 0 2 4 5 74 618 2
cert_coverFacet 4 466
cert_cover_5 4 0 0 3 5 7 210 466 3
cert_coverFacet 5 612
cert_cover_2 5 4 1 5 8 100 612 3
cert_coverFacet 6 488
cert_cover_5 6 3 2 4 5 6 104 488 3
cert_coverFacet 7 680
cert_cover_2 7 4 2 6 8 168 680 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0513

end
end BundlePart17

section BundlePart18
/- Source: ProjectionCertificates/R_m14e10q1_0522.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0522

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [563, 453, 425, 553, 713, 369, 593, 118, 534, 358, 774, 810, 908, 724, 41, 137, 521, 49, 81, 529, 289, 545, 193, 321, 577, 385, 22, 102, 262, 518, 50, 530, 290, 546, 770, 84, 532, 196, 324, 388, 644, 772, 296, 552, 392, 648, 776, 112, 592, 352, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_563, vertices_453, vertices_425, vertices_553, vertices_713, vertices_369, vertices_593, vertices_118, vertices_534, vertices_358, vertices_774, vertices_810, vertices_908, vertices_724] (by decide +kernel)
  polygons := literalFinset [vertices_41, vertices_137, vertices_521, vertices_49, vertices_81, vertices_529, vertices_289, vertices_545, vertices_193, vertices_321, vertices_577, vertices_385, vertices_22, vertices_102, vertices_262, vertices_518, vertices_50, vertices_530, vertices_290, vertices_546, vertices_770, vertices_84, vertices_532, vertices_196, vertices_324, vertices_388, vertices_644, vertices_772, vertices_296, vertices_552, vertices_392, vertices_648, vertices_776, vertices_112, vertices_592, vertices_352, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_563), (false, vertices_453), (false, vertices_425), (false, vertices_553), (false, vertices_713), (false, vertices_369), (false, vertices_593), (true, vertices_22), (true, vertices_102), (true, vertices_262), (true, vertices_518), (true, vertices_290), (true, vertices_770), (true, vertices_84), (true, vertices_532), (true, vertices_644), (true, vertices_772), (true, vertices_776)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 12 15 17 20 22 23 24 25 26
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_563) then 13 else
  if p.val = (false, vertices_453) then 16 else
  if p.val = (false, vertices_425) then 18 else
  if p.val = (false, vertices_553) then 0 else
  if p.val = (false, vertices_713) then 19 else
  if p.val = (false, vertices_369) then 21 else
  if p.val = (false, vertices_593) then 1 else
  if p.val = (true, vertices_22) then 2 else
  if p.val = (true, vertices_102) then 14 else
  if p.val = (true, vertices_262) then 3 else
  if p.val = (true, vertices_518) then 4 else
  if p.val = (true, vertices_290) then 5 else
  if p.val = (true, vertices_770) then 6 else
  if p.val = (true, vertices_84) then 7 else
  if p.val = (true, vertices_532) then 8 else
  if p.val = (true, vertices_644) then 9 else
  if p.val = (true, vertices_772) then 10 else
  if p.val = (true, vertices_776) then 11 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_553), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_593), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_22), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_262), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_518), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_290), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_770), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_84), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_532), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_644), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_772), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_776), by decide +kernel⟩
  | 12 => Sum.inl 0
  | 13 => Sum.inr ⟨(false, vertices_563), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_102), by decide +kernel⟩
  | 15 => Sum.inl 1
  | 16 => Sum.inr ⟨(false, vertices_453), by decide +kernel⟩
  | 17 => Sum.inl 2
  | 18 => Sum.inr ⟨(false, vertices_425), by decide +kernel⟩
  | 19 => Sum.inr ⟨(false, vertices_713), by decide +kernel⟩
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
cert_row_4 0 1 3 5 6 8 724 84 3
cert_row_2 1 0 1 4 5 102
cert_row_4 2 0 2 4 7 8 810 290 1
cert_row_4 3 1 2 6 7 8 908 388 1
cert_rows
cert_pivot_2 3 5 0 1
cert_heightProof 4
cert_coverFacet 0 118
cert_cover_5 0 1 0 1 3 4 22 118 3
cert_coverFacet 1 534
cert_cover_2 1 1 0 3 8 22 534 3
cert_coverFacet 2 358
cert_cover_5 2 1 0 1 4 7 102 358 3
cert_coverFacet 3 774
cert_cover_2 3 1 0 7 8 262 774 3
cert_coverFacet 4 810
cert_cover_5 4 2 0 2 4 7 290 810 1
cert_coverFacet 5 908
cert_cover_5 5 3 1 2 6 7 388 908 1
cert_coverFacet 6 724
cert_cover_5 6 0 1 3 5 6 84 724 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0522

end
end BundlePart18

section BundlePart19
/- Source: ProjectionCertificates/R_m14e10q1_0534.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0534

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [595, 173, 397, 565, 837, 361, 113, 902, 458, 690, 210, 834, 676, 248, 141, 37, 261, 517, 41, 265, 49, 81, 529, 97, 321, 577, 82, 146, 530, 194, 322, 578, 386, 642, 770, 164, 548, 388, 644, 772, 104, 168, 200, 328, 392, 112, 176, 560, 208, 672, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_595, vertices_173, vertices_397, vertices_565, vertices_837, vertices_361, vertices_113, vertices_902, vertices_458, vertices_690, vertices_210, vertices_834, vertices_676, vertices_248] (by decide +kernel)
  polygons := literalFinset [vertices_141, vertices_37, vertices_261, vertices_517, vertices_41, vertices_265, vertices_49, vertices_81, vertices_529, vertices_97, vertices_321, vertices_577, vertices_82, vertices_146, vertices_530, vertices_194, vertices_322, vertices_578, vertices_386, vertices_642, vertices_770, vertices_164, vertices_548, vertices_388, vertices_644, vertices_772, vertices_104, vertices_168, vertices_200, vertices_328, vertices_392, vertices_112, vertices_176, vertices_560, vertices_208, vertices_672, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_595), (false, vertices_173), (false, vertices_397), (false, vertices_565), (false, vertices_837), (false, vertices_361), (false, vertices_113), (true, vertices_146), (true, vertices_194), (true, vertices_322), (true, vertices_386), (true, vertices_642), (true, vertices_770), (true, vertices_644), (true, vertices_200), (true, vertices_176), (true, vertices_208), (true, vertices_672)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 12 18 14 21 22 23 24 25 26
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_595) then 13 else
  if p.val = (false, vertices_173) then 15 else
  if p.val = (false, vertices_397) then 16 else
  if p.val = (false, vertices_565) then 19 else
  if p.val = (false, vertices_837) then 20 else
  if p.val = (false, vertices_361) then 17 else
  if p.val = (false, vertices_113) then 0 else
  if p.val = (true, vertices_146) then 1 else
  if p.val = (true, vertices_194) then 2 else
  if p.val = (true, vertices_322) then 3 else
  if p.val = (true, vertices_386) then 4 else
  if p.val = (true, vertices_642) then 5 else
  if p.val = (true, vertices_770) then 6 else
  if p.val = (true, vertices_644) then 7 else
  if p.val = (true, vertices_200) then 8 else
  if p.val = (true, vertices_176) then 9 else
  if p.val = (true, vertices_208) then 10 else
  if p.val = (true, vertices_672) then 11 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_113), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_146), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_194), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_322), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_386), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_642), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_770), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_644), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_200), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_176), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_208), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_672), by decide +kernel⟩
  | 12 => Sum.inl 0
  | 13 => Sum.inr ⟨(false, vertices_595), by decide +kernel⟩
  | 14 => Sum.inl 2
  | 15 => Sum.inr ⟨(false, vertices_173), by decide +kernel⟩
  | 16 => Sum.inr ⟨(false, vertices_397), by decide +kernel⟩
  | 17 => Sum.inr ⟨(false, vertices_361), by decide +kernel⟩
  | 18 => Sum.inl 1
  | 19 => Sum.inr ⟨(false, vertices_565), by decide +kernel⟩
  | 20 => Sum.inr ⟨(false, vertices_837), by decide +kernel⟩
  | 21 => Sum.inl 3
  | 22 => Sum.inl 4
  | 23 => Sum.inl 5
  | 24 => Sum.inl 6
  | 25 => Sum.inl 7
  | 26 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 6 7 8 902 386 1
cert_row_4 1 0 2 5 6 7 458 194 1
cert_row_4 2 0 3 4 6 8 690 146 2
cert_row_4 3 2 3 4 5 6 248 104 1
cert_rows
cert_pivot_2 1 7 0 2
cert_heightProof 4
cert_coverFacet 0 902
cert_cover_5 0 0 0 1 6 7 386 902 1
cert_coverFacet 1 458
cert_cover_5 1 1 0 2 5 6 194 458 1
cert_coverFacet 2 690
cert_cover_5 2 2 0 3 4 6 146 690 2
cert_coverFacet 3 210
cert_cover_2 3 3 0 5 6 82 210 3
cert_coverFacet 4 834
cert_cover_2 4 5 0 7 8 322 834 3
cert_coverFacet 5 676
cert_cover_2 5 4 1 6 8 164 676 3
cert_coverFacet 6 248
cert_cover_5 6 3 2 3 4 5 104 248 1
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0534

end
end BundlePart19

section BundlePart20
/- Source: ProjectionCertificates/R_m14e10q1_0538.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0538

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [527, 279, 403, 675, 61, 553, 241, 902, 284, 844, 120, 344, 744, 976, 7, 275, 131, 515, 13, 21, 41, 521, 49, 145, 161, 545, 262, 518, 386, 642, 28, 268, 524, 276, 772, 56, 88, 280, 104, 552, 328, 584, 112, 208, 336, 400, 224, 672, 704, 832, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_527, vertices_279, vertices_403, vertices_675, vertices_61, vertices_553, vertices_241, vertices_902, vertices_284, vertices_844, vertices_120, vertices_344, vertices_744, vertices_976] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_275, vertices_131, vertices_515, vertices_13, vertices_21, vertices_41, vertices_521, vertices_49, vertices_145, vertices_161, vertices_545, vertices_262, vertices_518, vertices_386, vertices_642, vertices_28, vertices_268, vertices_524, vertices_276, vertices_772, vertices_56, vertices_88, vertices_280, vertices_104, vertices_552, vertices_328, vertices_584, vertices_112, vertices_208, vertices_336, vertices_400, vertices_224, vertices_672, vertices_704, vertices_832, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_527), (false, vertices_279), (false, vertices_403), (false, vertices_675), (false, vertices_61), (false, vertices_553), (false, vertices_241), (true, vertices_268), (true, vertices_772), (true, vertices_88), (true, vertices_280), (true, vertices_104), (true, vertices_328), (true, vertices_584), (true, vertices_336), (true, vertices_704), (true, vertices_832), (true, vertices_896)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 12 19 20 22 23 24 25 26
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_527) then 13 else
  if p.val = (false, vertices_279) then 16 else
  if p.val = (false, vertices_403) then 17 else
  if p.val = (false, vertices_675) then 18 else
  if p.val = (false, vertices_61) then 14 else
  if p.val = (false, vertices_553) then 0 else
  if p.val = (false, vertices_241) then 21 else
  if p.val = (true, vertices_268) then 1 else
  if p.val = (true, vertices_772) then 2 else
  if p.val = (true, vertices_88) then 3 else
  if p.val = (true, vertices_280) then 4 else
  if p.val = (true, vertices_104) then 5 else
  if p.val = (true, vertices_328) then 6 else
  if p.val = (true, vertices_584) then 7 else
  if p.val = (true, vertices_336) then 8 else
  if p.val = (true, vertices_704) then 9 else
  if p.val = (true, vertices_832) then 10 else
  if p.val = (true, vertices_896) then 11 else
  0
cert_priority
cert_nodeAtPriority_8 0 553 1 268 772 88 280 104 328 584 336 704 832 896 527 61 279 403 675 241
cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 6 7 8 902 262 2
cert_row_4 1 1 2 5 7 8 844 268 2
cert_row_4 2 2 4 5 6 8 744 104 3
cert_row_4 3 3 5 6 7 8 976 208 3
cert_rows
cert_pivot_2 0 1 2 3
cert_heightProof 4
cert_coverFacet 0 902
cert_cover_5 0 0 0 1 6 7 262 902 2
cert_coverFacet 1 284
cert_cover_2 1 2 1 3 7 28 284 3
cert_coverFacet 2 844
cert_cover_5 2 1 1 2 5 7 268 844 2
cert_coverFacet 3 120
cert_cover_2 3 3 2 4 5 56 120 3
cert_coverFacet 4 344
cert_cover_2 4 3 2 5 7 88 344 3
cert_coverFacet 5 744
cert_cover_5 5 2 2 4 5 6 104 744 3
cert_coverFacet 6 976
cert_cover_5 6 3 3 5 6 7 208 976 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0538

end
end BundlePart20

section BundlePart21
/- Source: ProjectionCertificates/R_m14e10q1_0541.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0541

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [59, 283, 803, 53, 213, 677, 913, 558, 842, 60, 92, 588, 964, 472, 27, 35, 259, 21, 37, 133, 49, 145, 273, 545, 641, 769, 42, 266, 522, 546, 770, 28, 44, 76, 524, 52, 84, 548, 196, 580, 644, 56, 88, 280, 328, 584, 208, 400, 448, 832, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_59, vertices_283, vertices_803, vertices_53, vertices_213, vertices_677, vertices_913, vertices_558, vertices_842, vertices_60, vertices_92, vertices_588, vertices_964, vertices_472] (by decide +kernel)
  polygons := literalFinset [vertices_27, vertices_35, vertices_259, vertices_21, vertices_37, vertices_133, vertices_49, vertices_145, vertices_273, vertices_545, vertices_641, vertices_769, vertices_42, vertices_266, vertices_522, vertices_546, vertices_770, vertices_28, vertices_44, vertices_76, vertices_524, vertices_52, vertices_84, vertices_548, vertices_196, vertices_580, vertices_644, vertices_56, vertices_88, vertices_280, vertices_328, vertices_584, vertices_208, vertices_400, vertices_448, vertices_832, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_59), (false, vertices_283), (false, vertices_803), (false, vertices_53), (false, vertices_213), (false, vertices_677), (false, vertices_913), (true, vertices_522), (true, vertices_28), (true, vertices_44), (true, vertices_76), (true, vertices_524), (true, vertices_580), (true, vertices_88), (true, vertices_328), (true, vertices_584), (true, vertices_448), (true, vertices_832)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 12 16 19 20 22 23 24 25 26
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_59) then 13 else
  if p.val = (false, vertices_283) then 14 else
  if p.val = (false, vertices_803) then 15 else
  if p.val = (false, vertices_53) then 0 else
  if p.val = (false, vertices_213) then 17 else
  if p.val = (false, vertices_677) then 18 else
  if p.val = (false, vertices_913) then 21 else
  if p.val = (true, vertices_522) then 1 else
  if p.val = (true, vertices_28) then 2 else
  if p.val = (true, vertices_44) then 3 else
  if p.val = (true, vertices_76) then 4 else
  if p.val = (true, vertices_524) then 5 else
  if p.val = (true, vertices_580) then 6 else
  if p.val = (true, vertices_88) then 7 else
  if p.val = (true, vertices_328) then 8 else
  if p.val = (true, vertices_584) then 9 else
  if p.val = (true, vertices_448) then 10 else
  if p.val = (true, vertices_832) then 11 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_53), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_522), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_28), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_44), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_76), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_524), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_580), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_88), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_328), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_584), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_448), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_832), by decide +kernel⟩
  | 12 => Sum.inl 0
  | 13 => Sum.inr ⟨(false, vertices_59), by decide +kernel⟩
  | 14 => Sum.inr ⟨(false, vertices_283), by decide +kernel⟩
  | 15 => Sum.inr ⟨(false, vertices_803), by decide +kernel⟩
  | 16 => Sum.inl 1
  | 17 => Sum.inr ⟨(false, vertices_213), by decide +kernel⟩
  | 18 => Sum.inr ⟨(false, vertices_677), by decide +kernel⟩
  | 19 => Sum.inl 2
  | 20 => Sum.inl 3
  | 21 => Sum.inr ⟨(false, vertices_913), by decide +kernel⟩
  | 22 => Sum.inl 4
  | 23 => Sum.inl 5
  | 24 => Sum.inl 6
  | 25 => Sum.inl 7
  | 26 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 2 4 8 558 42 1
cert_row_4 1 0 2 5 7 8 842 266 2
cert_row_4 2 1 5 6 7 8 964 196 3
cert_row_4 3 2 3 5 6 7 472 88 3
cert_rows
cert_pivot_2 4 0 1 2
cert_heightProof 4
cert_coverFacet 0 558
cert_cover_5 0 0 0 1 2 4 42 558 1
cert_coverFacet 1 842
cert_cover_5 1 1 0 2 5 7 266 842 2
cert_coverFacet 2 60
cert_cover_2 2 2 1 3 4 28 60 3
cert_coverFacet 3 92
cert_cover_2 3 2 1 3 5 28 92 3
cert_coverFacet 4 588
cert_cover_2 4 2 1 5 8 76 588 3
cert_coverFacet 5 964
cert_cover_5 5 2 1 5 6 7 196 964 3
cert_coverFacet 6 472
cert_cover_5 6 3 2 3 5 6 88 472 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0541

end
end BundlePart21

section BundlePart22
/- Source: ProjectionCertificates/R_m14e10q1_0543.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0543

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [299, 117, 309, 409, 233, 721, 806, 554, 714, 394, 898, 620, 852, 912, 53, 41, 137, 265, 81, 145, 273, 97, 289, 193, 42, 138, 266, 522, 290, 546, 386, 642, 770, 84, 276, 100, 292, 548, 580, 772, 104, 552, 200, 584, 392, 592, 400, 656, 784, 704, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_299, vertices_117, vertices_309, vertices_409, vertices_233, vertices_721, vertices_806, vertices_554, vertices_714, vertices_394, vertices_898, vertices_620, vertices_852, vertices_912] (by decide +kernel)
  polygons := literalFinset [vertices_53, vertices_41, vertices_137, vertices_265, vertices_81, vertices_145, vertices_273, vertices_97, vertices_289, vertices_193, vertices_42, vertices_138, vertices_266, vertices_522, vertices_290, vertices_546, vertices_386, vertices_642, vertices_770, vertices_84, vertices_276, vertices_100, vertices_292, vertices_548, vertices_580, vertices_772, vertices_104, vertices_552, vertices_200, vertices_584, vertices_392, vertices_592, vertices_400, vertices_656, vertices_784, vertices_704, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_299), (false, vertices_117), (false, vertices_309), (false, vertices_409), (false, vertices_233), (false, vertices_721), (true, vertices_138), (true, vertices_522), (true, vertices_546), (true, vertices_386), (true, vertices_642), (true, vertices_770), (true, vertices_548), (true, vertices_580), (true, vertices_772), (true, vertices_552), (true, vertices_584), (true, vertices_784), (true, vertices_896)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 13 15 18 21 23 24 25 26 27
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_299) then 14 else
  if p.val = (false, vertices_117) then 16 else
  if p.val = (false, vertices_309) then 17 else
  if p.val = (false, vertices_409) then 19 else
  if p.val = (false, vertices_233) then 20 else
  if p.val = (false, vertices_721) then 22 else
  if p.val = (true, vertices_138) then 0 else
  if p.val = (true, vertices_522) then 1 else
  if p.val = (true, vertices_546) then 2 else
  if p.val = (true, vertices_386) then 3 else
  if p.val = (true, vertices_642) then 4 else
  if p.val = (true, vertices_770) then 5 else
  if p.val = (true, vertices_548) then 6 else
  if p.val = (true, vertices_580) then 7 else
  if p.val = (true, vertices_772) then 8 else
  if p.val = (true, vertices_552) then 9 else
  if p.val = (true, vertices_584) then 10 else
  if p.val = (true, vertices_784) then 11 else
  if p.val = (true, vertices_896) then 12 else
  0
cert_priority
cert_nodeAtPriority_12 138 1 522 2 546 386 642 770 548 580 772 552 584 784 896 299 117 309 409 233 721
cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 2 5 6 8 714 138 2
cert_row_4 1 0 1 4 7 8 806 290 1
cert_row_4 2 1 2 4 5 8 620 100 1
cert_row_4 3 1 3 5 7 8 852 84 3
cert_rows
cert_pivot_2 6 0 2 1
cert_heightProof 4
cert_coverFacet 0 806
cert_cover_5 0 1 0 1 4 7 290 806 1
cert_coverFacet 1 554
cert_cover_2 1 2 0 4 8 42 554 3
cert_coverFacet 2 714
cert_cover_5 2 0 0 2 5 6 138 714 2
cert_coverFacet 3 394
cert_cover_2 3 2 0 6 7 138 394 3
cert_coverFacet 4 898
cert_cover_2 4 6 0 7 8 386 898 3
cert_coverFacet 5 620
cert_cover_5 5 2 1 2 4 5 100 620 1
cert_coverFacet 6 852
cert_cover_5 6 3 1 3 5 7 84 852 3
cert_coverFacet 7 912
cert_cover_2 7 6 3 7 8 400 912 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0543

end
end BundlePart22

section BundlePart23
/- Source: ProjectionCertificates/R_m14e10q1_0544.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0544

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [647, 557, 293, 453, 233, 649, 369, 310, 566, 390, 850, 898, 632, 968, 37, 133, 261, 517, 41, 137, 521, 97, 289, 193, 321, 641, 54, 134, 262, 518, 274, 530, 386, 642, 770, 292, 548, 388, 104, 552, 200, 584, 648, 112, 304, 560, 336, 592, 448, 832, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_647, vertices_557, vertices_293, vertices_453, vertices_233, vertices_649, vertices_369, vertices_310, vertices_566, vertices_390, vertices_850, vertices_898, vertices_632, vertices_968] (by decide +kernel)
  polygons := literalFinset [vertices_37, vertices_133, vertices_261, vertices_517, vertices_41, vertices_137, vertices_521, vertices_97, vertices_289, vertices_193, vertices_321, vertices_641, vertices_54, vertices_134, vertices_262, vertices_518, vertices_274, vertices_530, vertices_386, vertices_642, vertices_770, vertices_292, vertices_548, vertices_388, vertices_104, vertices_552, vertices_200, vertices_584, vertices_648, vertices_112, vertices_304, vertices_560, vertices_336, vertices_592, vertices_448, vertices_832, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_647), (false, vertices_557), (false, vertices_293), (false, vertices_453), (false, vertices_233), (false, vertices_649), (false, vertices_369), (true, vertices_54), (true, vertices_262), (true, vertices_274), (true, vertices_530), (true, vertices_386), (true, vertices_770), (true, vertices_584), (true, vertices_560), (true, vertices_592), (true, vertices_832), (true, vertices_896)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 12 15 18 20 22 23 24 25 26
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_647) then 13 else
  if p.val = (false, vertices_557) then 16 else
  if p.val = (false, vertices_293) then 0 else
  if p.val = (false, vertices_453) then 17 else
  if p.val = (false, vertices_233) then 19 else
  if p.val = (false, vertices_649) then 1 else
  if p.val = (false, vertices_369) then 21 else
  if p.val = (true, vertices_54) then 14 else
  if p.val = (true, vertices_262) then 2 else
  if p.val = (true, vertices_274) then 3 else
  if p.val = (true, vertices_530) then 4 else
  if p.val = (true, vertices_386) then 5 else
  if p.val = (true, vertices_770) then 6 else
  if p.val = (true, vertices_584) then 7 else
  if p.val = (true, vertices_560) then 8 else
  if p.val = (true, vertices_592) then 9 else
  if p.val = (true, vertices_832) then 10 else
  if p.val = (true, vertices_896) then 11 else
  0
cert_priority
cert_nodeAtPriority_67 0 293 1 649 262 274 530 386 770 584 560 592 832 896 647 54 557 453 233 369
cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 1 3 4 54
cert_row_4 1 0 3 5 7 8 850 274 2
cert_row_4 2 2 3 4 5 8 632 104 1
cert_row_4 3 2 5 6 7 8 968 200 3
cert_rows
cert_pivot_2 1 0 3 2
cert_heightProof 4
cert_coverFacet 0 310
cert_cover_5 0 0 0 1 3 7 54 310 3
cert_coverFacet 1 566
cert_cover_5 1 0 0 1 3 8 54 566 3
cert_coverFacet 2 390
cert_cover_2 2 1 0 6 7 134 390 3
cert_coverFacet 3 850
cert_cover_5 3 1 0 3 5 7 274 850 2
cert_coverFacet 4 898
cert_cover_2 4 6 0 7 8 386 898 3
cert_coverFacet 5 632
cert_cover_5 5 2 2 3 4 5 104 632 1
cert_coverFacet 6 968
cert_cover_5 6 3 2 5 6 7 200 968 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0544

end
end BundlePart23

section BundlePart24
/- Source: ProjectionCertificates/R_m14e10q1_0546.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0546

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [79, 535, 451, 643, 525, 361, 905, 214, 690, 108, 812, 244, 564, 992, 7, 67, 131, 515, 13, 517, 73, 265, 521, 321, 385, 641, 22, 70, 146, 530, 194, 642, 44, 76, 524, 52, 212, 532, 100, 548, 104, 296, 776, 176, 560, 224, 352, 672, 800, 448, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_79, vertices_535, vertices_451, vertices_643, vertices_525, vertices_361, vertices_905, vertices_214, vertices_690, vertices_108, vertices_812, vertices_244, vertices_564, vertices_992] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_67, vertices_131, vertices_515, vertices_13, vertices_517, vertices_73, vertices_265, vertices_521, vertices_321, vertices_385, vertices_641, vertices_22, vertices_70, vertices_146, vertices_530, vertices_194, vertices_642, vertices_44, vertices_76, vertices_524, vertices_52, vertices_212, vertices_532, vertices_100, vertices_548, vertices_104, vertices_296, vertices_776, vertices_176, vertices_560, vertices_224, vertices_352, vertices_672, vertices_800, vertices_448, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_79), (false, vertices_535), (false, vertices_451), (false, vertices_643), (false, vertices_525), (false, vertices_361), (false, vertices_905), (true, vertices_146), (true, vertices_44), (true, vertices_52), (true, vertices_212), (true, vertices_100), (true, vertices_548), (true, vertices_176), (true, vertices_560), (true, vertices_224), (true, vertices_672), (true, vertices_800)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 12 16 18 21 22 23 24 25 26
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_79) then 13 else
  if p.val = (false, vertices_535) then 14 else
  if p.val = (false, vertices_451) then 15 else
  if p.val = (false, vertices_643) then 0 else
  if p.val = (false, vertices_525) then 1 else
  if p.val = (false, vertices_361) then 19 else
  if p.val = (false, vertices_905) then 20 else
  if p.val = (true, vertices_146) then 2 else
  if p.val = (true, vertices_44) then 3 else
  if p.val = (true, vertices_52) then 4 else
  if p.val = (true, vertices_212) then 17 else
  if p.val = (true, vertices_100) then 5 else
  if p.val = (true, vertices_548) then 6 else
  if p.val = (true, vertices_176) then 7 else
  if p.val = (true, vertices_560) then 8 else
  if p.val = (true, vertices_224) then 9 else
  if p.val = (true, vertices_672) then 10 else
  if p.val = (true, vertices_800) then 11 else
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
  | 7 => Sum.inr ⟨(true, vertices_176), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_560), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_224), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_672), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_800), by decide +kernel⟩
  | 12 => Sum.inl 0
  | 13 => Sum.inr ⟨(false, vertices_79), by decide +kernel⟩
  | 14 => Sum.inr ⟨(false, vertices_535), by decide +kernel⟩
  | 15 => Sum.inr ⟨(false, vertices_451), by decide +kernel⟩
  | 16 => Sum.inl 1
  | 17 => Sum.inr ⟨(true, vertices_212), by decide +kernel⟩
  | 18 => Sum.inl 2
  | 19 => Sum.inr ⟨(false, vertices_361), by decide +kernel⟩
  | 20 => Sum.inr ⟨(false, vertices_905), by decide +kernel⟩
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
cert_row_2 1 1 3 5 6 212
cert_row_4 2 1 2 4 7 8 812 44 3
cert_row_4 3 4 5 6 7 8 992 224 3
cert_rows
cert_pivot_2 0 3 1 4
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
cert_coverFacet 6 992
cert_cover_5 6 3 4 5 6 7 224 992 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0546

end
end BundlePart24

section BundlePart25
/- Source: ProjectionCertificates/R_m14e10q1_0547.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0547

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [595, 147, 419, 771, 181, 841, 369, 662, 898, 572, 364, 908, 420, 632, 19, 131, 259, 515, 49, 81, 145, 161, 289, 321, 577, 769, 146, 530, 386, 642, 770, 44, 268, 524, 52, 148, 532, 164, 292, 388, 644, 568, 104, 328, 584, 776, 112, 592, 352, 416, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_595, vertices_147, vertices_419, vertices_771, vertices_181, vertices_841, vertices_369, vertices_662, vertices_898, vertices_572, vertices_364, vertices_908, vertices_420, vertices_632] (by decide +kernel)
  polygons := literalFinset [vertices_19, vertices_131, vertices_259, vertices_515, vertices_49, vertices_81, vertices_145, vertices_161, vertices_289, vertices_321, vertices_577, vertices_769, vertices_146, vertices_530, vertices_386, vertices_642, vertices_770, vertices_44, vertices_268, vertices_524, vertices_52, vertices_148, vertices_532, vertices_164, vertices_292, vertices_388, vertices_644, vertices_568, vertices_104, vertices_328, vertices_584, vertices_776, vertices_112, vertices_592, vertices_352, vertices_416, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_595), (false, vertices_147), (false, vertices_419), (false, vertices_771), (false, vertices_181), (false, vertices_841), (false, vertices_369), (true, vertices_642), (true, vertices_44), (true, vertices_268), (true, vertices_524), (true, vertices_532), (true, vertices_292), (true, vertices_388), (true, vertices_644), (true, vertices_568), (true, vertices_104), (true, vertices_896)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 12 15 17 20 22 23 24 25 26
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_595) then 13 else
  if p.val = (false, vertices_147) then 0 else
  if p.val = (false, vertices_419) then 14 else
  if p.val = (false, vertices_771) then 1 else
  if p.val = (false, vertices_181) then 16 else
  if p.val = (false, vertices_841) then 18 else
  if p.val = (false, vertices_369) then 21 else
  if p.val = (true, vertices_642) then 2 else
  if p.val = (true, vertices_44) then 3 else
  if p.val = (true, vertices_268) then 4 else
  if p.val = (true, vertices_524) then 5 else
  if p.val = (true, vertices_532) then 6 else
  if p.val = (true, vertices_292) then 7 else
  if p.val = (true, vertices_388) then 8 else
  if p.val = (true, vertices_644) then 9 else
  if p.val = (true, vertices_568) then 19 else
  if p.val = (true, vertices_104) then 10 else
  if p.val = (true, vertices_896) then 11 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_147), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_771), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_642), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_44), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_268), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_524), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_532), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_292), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_388), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_644), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_104), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_896), by decide +kernel⟩
  | 12 => Sum.inl 0
  | 13 => Sum.inr ⟨(false, vertices_595), by decide +kernel⟩
  | 14 => Sum.inr ⟨(false, vertices_419), by decide +kernel⟩
  | 15 => Sum.inl 1
  | 16 => Sum.inr ⟨(false, vertices_181), by decide +kernel⟩
  | 17 => Sum.inl 2
  | 18 => Sum.inr ⟨(false, vertices_841), by decide +kernel⟩
  | 19 => Sum.inr ⟨(true, vertices_568), by decide +kernel⟩
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
cert_row_4 0 0 1 3 6 8 662 146 1
cert_row_2 1 2 3 4 8 568
cert_row_4 2 1 2 4 5 7 364 44 3
cert_row_4 3 1 2 6 7 8 908 268 2
cert_rows
cert_pivot_2 0 3 4 1
cert_heightProof 4
cert_coverFacet 0 662
cert_cover_5 0 0 0 1 3 6 146 662 1
cert_coverFacet 1 898
cert_cover_2 1 6 0 7 8 386 898 3
cert_coverFacet 2 572
cert_cover_5 2 1 1 2 3 4 44 572 2
cert_coverFacet 3 364
cert_cover_5 3 2 1 2 4 5 44 364 3
cert_coverFacet 4 908
cert_cover_5 4 3 1 2 6 7 268 908 2
cert_coverFacet 5 420
cert_cover_2 5 4 1 6 7 164 420 3
cert_coverFacet 6 632
cert_cover_5 6 1 2 3 4 5 568 632 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0547

end
end BundlePart25

section BundlePart26
/- Source: ProjectionCertificates/R_m14e10q1_0548.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0548

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [167, 779, 563, 387, 109, 397, 617, 178, 466, 786, 844, 244, 452, 880, 35, 131, 259, 515, 13, 37, 133, 105, 265, 521, 545, 385, 50, 146, 274, 530, 162, 386, 770, 76, 268, 100, 164, 196, 324, 388, 584, 776, 112, 176, 560, 208, 336, 784, 608, 448, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_167, vertices_779, vertices_563, vertices_387, vertices_109, vertices_397, vertices_617, vertices_178, vertices_466, vertices_786, vertices_844, vertices_244, vertices_452, vertices_880] (by decide +kernel)
  polygons := literalFinset [vertices_35, vertices_131, vertices_259, vertices_515, vertices_13, vertices_37, vertices_133, vertices_105, vertices_265, vertices_521, vertices_545, vertices_385, vertices_50, vertices_146, vertices_274, vertices_530, vertices_162, vertices_386, vertices_770, vertices_76, vertices_268, vertices_100, vertices_164, vertices_196, vertices_324, vertices_388, vertices_584, vertices_776, vertices_112, vertices_176, vertices_560, vertices_208, vertices_336, vertices_784, vertices_608, vertices_448, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_167), (false, vertices_779), (false, vertices_563), (false, vertices_387), (false, vertices_109), (false, vertices_397), (false, vertices_617), (true, vertices_146), (true, vertices_274), (true, vertices_196), (true, vertices_324), (true, vertices_112), (true, vertices_176), (true, vertices_208), (true, vertices_336), (true, vertices_784), (true, vertices_448), (true, vertices_832)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 12 16 18 21 22 23 24 25 26
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_167) then 13 else
  if p.val = (false, vertices_779) then 14 else
  if p.val = (false, vertices_563) then 15 else
  if p.val = (false, vertices_387) then 0 else
  if p.val = (false, vertices_109) then 19 else
  if p.val = (false, vertices_397) then 17 else
  if p.val = (false, vertices_617) then 20 else
  if p.val = (true, vertices_146) then 1 else
  if p.val = (true, vertices_274) then 2 else
  if p.val = (true, vertices_196) then 3 else
  if p.val = (true, vertices_324) then 4 else
  if p.val = (true, vertices_112) then 5 else
  if p.val = (true, vertices_176) then 6 else
  if p.val = (true, vertices_208) then 7 else
  if p.val = (true, vertices_336) then 8 else
  if p.val = (true, vertices_784) then 9 else
  if p.val = (true, vertices_448) then 10 else
  if p.val = (true, vertices_832) then 11 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_387), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_146), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_274), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_196), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_324), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_112), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_176), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_208), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_336), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_784), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_448), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_832), by decide +kernel⟩
  | 12 => Sum.inl 0
  | 13 => Sum.inr ⟨(false, vertices_167), by decide +kernel⟩
  | 14 => Sum.inr ⟨(false, vertices_779), by decide +kernel⟩
  | 15 => Sum.inr ⟨(false, vertices_563), by decide +kernel⟩
  | 16 => Sum.inl 1
  | 17 => Sum.inr ⟨(false, vertices_397), by decide +kernel⟩
  | 18 => Sum.inl 2
  | 19 => Sum.inr ⟨(false, vertices_109), by decide +kernel⟩
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
cert_row_4 0 0 3 5 6 7 466 146 2
cert_row_4 1 1 2 5 7 8 844 76 3
cert_row_4 2 1 3 4 5 6 244 100 1
cert_row_4 3 3 4 5 7 8 880 112 3
cert_rows
cert_pivot_2 0 2 1 3
cert_heightProof 4
cert_coverFacet 0 178
cert_cover_2 0 3 0 4 6 50 178 3
cert_coverFacet 1 466
cert_cover_5 1 0 0 3 5 6 146 466 2
cert_coverFacet 2 786
cert_cover_2 2 3 0 7 8 274 786 3
cert_coverFacet 3 844
cert_cover_5 3 1 1 2 5 7 76 844 3
cert_coverFacet 4 244
cert_cover_5 4 2 1 3 4 5 100 244 1
cert_coverFacet 5 452
cert_cover_2 5 5 1 6 7 196 452 3
cert_coverFacet 6 880
cert_cover_5 6 3 3 4 5 7 112 880 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0548

end
end BundlePart26

section BundlePart27
/- Source: ProjectionCertificates/R_m14e10q1_0549.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0549

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [167, 563, 835, 387, 397, 613, 325, 410, 178, 786, 348, 236, 248, 880, 35, 131, 259, 515, 37, 69, 133, 261, 545, 321, 577, 385, 50, 146, 274, 530, 162, 386, 770, 76, 140, 268, 100, 164, 324, 88, 152, 280, 232, 392, 112, 176, 560, 336, 784, 608, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_167, vertices_563, vertices_835, vertices_387, vertices_397, vertices_613, vertices_325, vertices_410, vertices_178, vertices_786, vertices_348, vertices_236, vertices_248, vertices_880] (by decide +kernel)
  polygons := literalFinset [vertices_35, vertices_131, vertices_259, vertices_515, vertices_37, vertices_69, vertices_133, vertices_261, vertices_545, vertices_321, vertices_577, vertices_385, vertices_50, vertices_146, vertices_274, vertices_530, vertices_162, vertices_386, vertices_770, vertices_76, vertices_140, vertices_268, vertices_100, vertices_164, vertices_324, vertices_88, vertices_152, vertices_280, vertices_232, vertices_392, vertices_112, vertices_176, vertices_560, vertices_336, vertices_784, vertices_608, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_167), (false, vertices_563), (false, vertices_835), (false, vertices_387), (false, vertices_397), (false, vertices_613), (false, vertices_325), (true, vertices_146), (true, vertices_274), (true, vertices_76), (true, vertices_88), (true, vertices_152), (true, vertices_280), (true, vertices_232), (true, vertices_112), (true, vertices_176), (true, vertices_336), (true, vertices_784)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 12 16 19 21 22 23 24 25 26
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_167) then 13 else
  if p.val = (false, vertices_563) then 14 else
  if p.val = (false, vertices_835) then 15 else
  if p.val = (false, vertices_387) then 0 else
  if p.val = (false, vertices_397) then 17 else
  if p.val = (false, vertices_613) then 18 else
  if p.val = (false, vertices_325) then 1 else
  if p.val = (true, vertices_146) then 2 else
  if p.val = (true, vertices_274) then 3 else
  if p.val = (true, vertices_76) then 4 else
  if p.val = (true, vertices_88) then 5 else
  if p.val = (true, vertices_152) then 6 else
  if p.val = (true, vertices_280) then 7 else
  if p.val = (true, vertices_232) then 20 else
  if p.val = (true, vertices_112) then 8 else
  if p.val = (true, vertices_176) then 9 else
  if p.val = (true, vertices_336) then 10 else
  if p.val = (true, vertices_784) then 11 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_387), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_325), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_146), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_274), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_76), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_88), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_152), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_280), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_112), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_176), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_336), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_784), by decide +kernel⟩
  | 12 => Sum.inl 0
  | 13 => Sum.inr ⟨(false, vertices_167), by decide +kernel⟩
  | 14 => Sum.inr ⟨(false, vertices_563), by decide +kernel⟩
  | 15 => Sum.inr ⟨(false, vertices_835), by decide +kernel⟩
  | 16 => Sum.inl 1
  | 17 => Sum.inr ⟨(false, vertices_397), by decide +kernel⟩
  | 18 => Sum.inr ⟨(false, vertices_613), by decide +kernel⟩
  | 19 => Sum.inl 2
  | 20 => Sum.inr ⟨(true, vertices_232), by decide +kernel⟩
  | 21 => Sum.inl 3
  | 22 => Sum.inl 4
  | 23 => Sum.inl 5
  | 24 => Sum.inl 6
  | 25 => Sum.inl 7
  | 26 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 2 3 6 7 410 146 1
cert_row_2 1 2 4 5 6 232
cert_row_4 2 1 2 3 5 7 348 76 2
cert_row_4 3 3 4 5 7 8 880 112 3
cert_rows
cert_pivot_2 0 6 1 3
cert_heightProof 4
cert_coverFacet 0 410
cert_cover_5 0 0 0 2 3 6 146 410 1
cert_coverFacet 1 178
cert_cover_2 1 3 0 4 6 50 178 3
cert_coverFacet 2 786
cert_cover_2 2 3 0 7 8 274 786 3
cert_coverFacet 3 348
cert_cover_5 3 2 1 2 3 5 76 348 2
cert_coverFacet 4 236
cert_cover_5 4 1 1 2 4 5 76 236 2
cert_coverFacet 5 248
cert_cover_5 5 1 2 3 4 5 88 248 2
cert_coverFacet 6 880
cert_cover_5 6 3 3 4 5 7 112 880 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0549

end
end BundlePart27

section BundlePart28
/- Source: ProjectionCertificates/R_m14e10q1_0559.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0559

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [59, 275, 419, 901, 793, 553, 737, 342, 602, 618, 354, 724, 788, 484, 19, 35, 259, 25, 41, 521, 273, 161, 545, 385, 641, 769, 26, 42, 586, 82, 274, 98, 290, 322, 84, 276, 532, 196, 324, 388, 644, 772, 536, 552, 592, 784, 224, 352, 608, 416, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_59, vertices_275, vertices_419, vertices_901, vertices_793, vertices_553, vertices_737, vertices_342, vertices_602, vertices_618, vertices_354, vertices_724, vertices_788, vertices_484] (by decide +kernel)
  polygons := literalFinset [vertices_19, vertices_35, vertices_259, vertices_25, vertices_41, vertices_521, vertices_273, vertices_161, vertices_545, vertices_385, vertices_641, vertices_769, vertices_26, vertices_42, vertices_586, vertices_82, vertices_274, vertices_98, vertices_290, vertices_322, vertices_84, vertices_276, vertices_532, vertices_196, vertices_324, vertices_388, vertices_644, vertices_772, vertices_536, vertices_552, vertices_592, vertices_784, vertices_224, vertices_352, vertices_608, vertices_416, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_59), (false, vertices_275), (false, vertices_419), (false, vertices_901), (false, vertices_793), (false, vertices_553), (false, vertices_737), (true, vertices_586), (true, vertices_82), (true, vertices_98), (true, vertices_322), (true, vertices_84), (true, vertices_276), (true, vertices_532), (true, vertices_196), (true, vertices_324), (true, vertices_592), (true, vertices_352)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 12 16 18 20 21 23 24 25 26
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_59) then 13 else
  if p.val = (false, vertices_275) then 0 else
  if p.val = (false, vertices_419) then 14 else
  if p.val = (false, vertices_901) then 17 else
  if p.val = (false, vertices_793) then 19 else
  if p.val = (false, vertices_553) then 1 else
  if p.val = (false, vertices_737) then 22 else
  if p.val = (true, vertices_586) then 15 else
  if p.val = (true, vertices_82) then 2 else
  if p.val = (true, vertices_98) then 3 else
  if p.val = (true, vertices_322) then 4 else
  if p.val = (true, vertices_84) then 5 else
  if p.val = (true, vertices_276) then 6 else
  if p.val = (true, vertices_532) then 7 else
  if p.val = (true, vertices_196) then 8 else
  if p.val = (true, vertices_324) then 9 else
  if p.val = (true, vertices_592) then 10 else
  if p.val = (true, vertices_352) then 11 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_275), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_553), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_82), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_98), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_322), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_84), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_276), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_532), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_196), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_324), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_592), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_352), by decide +kernel⟩
  | 12 => Sum.inl 0
  | 13 => Sum.inr ⟨(false, vertices_59), by decide +kernel⟩
  | 14 => Sum.inr ⟨(false, vertices_419), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_586), by decide +kernel⟩
  | 16 => Sum.inl 1
  | 17 => Sum.inr ⟨(false, vertices_901), by decide +kernel⟩
  | 18 => Sum.inl 2
  | 19 => Sum.inr ⟨(false, vertices_793), by decide +kernel⟩
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
cert_row_2 0 0 2 5 8 586
cert_row_4 1 0 1 3 5 7 342 82 1
cert_row_4 2 1 3 5 6 8 724 84 3
cert_row_4 3 1 4 5 6 7 484 196 1
cert_rows
cert_pivot_2 2 0 3 1
cert_heightProof 4
cert_coverFacet 0 342
cert_cover_5 0 1 0 1 3 5 82 342 1
cert_coverFacet 1 602
cert_cover_5 1 0 0 2 3 5 26 602 3
cert_coverFacet 2 618
cert_cover_5 2 0 0 2 4 5 42 618 3
cert_coverFacet 3 354
cert_cover_2 3 4 0 5 7 98 354 3
cert_coverFacet 4 724
cert_cover_5 4 2 1 3 5 6 84 724 3
cert_coverFacet 5 788
cert_cover_2 5 3 1 7 8 276 788 3
cert_coverFacet 6 484
cert_cover_5 6 3 1 4 5 6 196 484 1
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0559

end
end BundlePart28

section BundlePart29
/- Source: ProjectionCertificates/R_m14e10q1_0560.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0560

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [675, 341, 229, 901, 809, 353, 214, 570, 346, 362, 658, 226, 404, 920, 69, 133, 261, 97, 161, 289, 545, 321, 641, 769, 26, 42, 330, 82, 146, 530, 98, 162, 546, 194, 642, 84, 148, 276, 196, 388, 280, 536, 296, 552, 776, 336, 400, 656, 224, 352, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_675, vertices_341, vertices_229, vertices_901, vertices_809, vertices_353, vertices_214, vertices_570, vertices_346, vertices_362, vertices_658, vertices_226, vertices_404, vertices_920] (by decide +kernel)
  polygons := literalFinset [vertices_69, vertices_133, vertices_261, vertices_97, vertices_161, vertices_289, vertices_545, vertices_321, vertices_641, vertices_769, vertices_26, vertices_42, vertices_330, vertices_82, vertices_146, vertices_530, vertices_98, vertices_162, vertices_546, vertices_194, vertices_642, vertices_84, vertices_148, vertices_276, vertices_196, vertices_388, vertices_280, vertices_536, vertices_296, vertices_552, vertices_776, vertices_336, vertices_400, vertices_656, vertices_224, vertices_352, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_675), (false, vertices_341), (false, vertices_229), (false, vertices_901), (false, vertices_809), (false, vertices_353), (true, vertices_26), (true, vertices_42), (true, vertices_330), (true, vertices_82), (true, vertices_146), (true, vertices_530), (true, vertices_98), (true, vertices_194), (true, vertices_148), (true, vertices_280), (true, vertices_536), (true, vertices_400), (true, vertices_656)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 13 16 20 22 23 24 25 26 27
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_675) then 14 else
  if p.val = (false, vertices_341) then 17 else
  if p.val = (false, vertices_229) then 18 else
  if p.val = (false, vertices_901) then 19 else
  if p.val = (false, vertices_809) then 21 else
  if p.val = (false, vertices_353) then 0 else
  if p.val = (true, vertices_26) then 1 else
  if p.val = (true, vertices_42) then 2 else
  if p.val = (true, vertices_330) then 15 else
  if p.val = (true, vertices_82) then 3 else
  if p.val = (true, vertices_146) then 4 else
  if p.val = (true, vertices_530) then 5 else
  if p.val = (true, vertices_98) then 6 else
  if p.val = (true, vertices_194) then 7 else
  if p.val = (true, vertices_148) then 8 else
  if p.val = (true, vertices_280) then 9 else
  if p.val = (true, vertices_536) then 10 else
  if p.val = (true, vertices_400) then 11 else
  if p.val = (true, vertices_656) then 12 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_353), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_26), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_42), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_82), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_146), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_530), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_98), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_194), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_148), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_280), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_536), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_400), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_656), by decide +kernel⟩
  | 13 => Sum.inl 0
  | 14 => Sum.inr ⟨(false, vertices_675), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_330), by decide +kernel⟩
  | 16 => Sum.inl 1
  | 17 => Sum.inr ⟨(false, vertices_341), by decide +kernel⟩
  | 18 => Sum.inr ⟨(false, vertices_229), by decide +kernel⟩
  | 19 => Sum.inr ⟨(false, vertices_901), by decide +kernel⟩
  | 20 => Sum.inl 2
  | 21 => Sum.inr ⟨(false, vertices_809), by decide +kernel⟩
  | 22 => Sum.inl 3
  | 23 => Sum.inl 4
  | 24 => Sum.inl 5
  | 25 => Sum.inl 6
  | 26 => Sum.inl 7
  | 27 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 3 5 6 214 82 1
cert_row_2 1 0 2 5 7 330
cert_row_4 2 0 2 3 4 8 570 26 3
cert_row_4 3 2 3 6 7 8 920 280 2
cert_rows
cert_pivot_2 1 5 0 2
cert_heightProof 4
cert_coverFacet 0 214
cert_cover_5 0 0 0 1 3 5 82 214 1
cert_coverFacet 1 570
cert_cover_5 1 2 0 2 3 4 26 570 3
cert_coverFacet 2 346
cert_cover_5 2 1 0 2 3 5 26 346 3
cert_coverFacet 3 362
cert_cover_5 3 1 0 2 4 5 42 362 3
cert_coverFacet 4 658
cert_cover_2 4 3 0 6 8 146 658 3
cert_coverFacet 5 226
cert_cover_2 5 4 0 5 6 98 226 3
cert_coverFacet 6 404
cert_cover_2 6 3 1 6 7 148 404 3
cert_coverFacet 7 920
cert_cover_5 7 3 2 3 6 7 280 920 2
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0560

end
end BundlePart29
-- Explicit facial frame witnesses.

-- Public target certificates; internal witness data stays private.
namespace Nonrational.TerminalVerification
open Papers.RationalityTen.ChirotopeDensity.FiniteProjection
open Nonrational.TerminalData
set_option maxRecDepth 100000
set_option maxHeartbeats 0

public theorem projection_0300 : Certifies 300 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0355.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0301 : Certifies 301 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0370.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0302 : Certifies 302 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0382.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0303 : Certifies 303 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0389.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0304 : Certifies 304 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0390.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0305 : Certifies 305 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0391.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0306 : Certifies 306 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0393.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0307 : Certifies 307 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0399.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0308 : Certifies 308 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0400.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0309 : Certifies 309 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0406.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0310 : Certifies 310 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0407.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0311 : Certifies 311 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0444.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0312 : Certifies 312 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0465.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0313 : Certifies 313 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0495.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0314 : Certifies 314 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0505.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0315 : Certifies 315 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0508.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0316 : Certifies 316 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0510.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0317 : Certifies 317 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0513.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0318 : Certifies 318 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0522.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0319 : Certifies 319 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0534.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0320 : Certifies 320 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0538.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0321 : Certifies 321 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0541.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0322 : Certifies 322 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0543.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0323 : Certifies 323 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0544.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0324 : Certifies 324 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0546.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0325 : Certifies 325 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0547.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0326 : Certifies 326 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0548.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0327 : Certifies 327 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0549.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0328 : Certifies 328 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0559.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0329 : Certifies 329 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0560.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem certified_B010 (j : Fin 30) :
    Certifies (300 + j.val) := by
  fin_cases j
  · exact projection_0300
  · exact projection_0301
  · exact projection_0302
  · exact projection_0303
  · exact projection_0304
  · exact projection_0305
  · exact projection_0306
  · exact projection_0307
  · exact projection_0308
  · exact projection_0309
  · exact projection_0310
  · exact projection_0311
  · exact projection_0312
  · exact projection_0313
  · exact projection_0314
  · exact projection_0315
  · exact projection_0316
  · exact projection_0317
  · exact projection_0318
  · exact projection_0319
  · exact projection_0320
  · exact projection_0321
  · exact projection_0322
  · exact projection_0323
  · exact projection_0324
  · exact projection_0325
  · exact projection_0326
  · exact projection_0327
  · exact projection_0328
  · exact projection_0329

end Nonrational.TerminalVerification
