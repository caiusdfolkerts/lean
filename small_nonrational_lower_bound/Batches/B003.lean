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
/- Source: ProjectionCertificates/P0_163.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_163

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [611, 309, 597, 101, 793, 929, 230, 218, 602, 906, 674, 412, 212, 420, 21, 37, 69, 273, 529, 97, 289, 545, 577, 769, 90, 138, 522, 98, 162, 546, 194, 578, 642, 84, 148, 276, 100, 164, 292, 196, 388, 152, 280, 536, 392, 776, 208, 592, 416, 672, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_611, vertices_309, vertices_597, vertices_101, vertices_793, vertices_929, vertices_230, vertices_218, vertices_602, vertices_906, vertices_674, vertices_412, vertices_212, vertices_420] (by decide +kernel)
  polygons := literalFinset [vertices_21, vertices_37, vertices_69, vertices_273, vertices_529, vertices_97, vertices_289, vertices_545, vertices_577, vertices_769, vertices_90, vertices_138, vertices_522, vertices_98, vertices_162, vertices_546, vertices_194, vertices_578, vertices_642, vertices_84, vertices_148, vertices_276, vertices_100, vertices_164, vertices_292, vertices_196, vertices_388, vertices_152, vertices_280, vertices_536, vertices_392, vertices_776, vertices_208, vertices_592, vertices_416, vertices_672, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_611), (false, vertices_309), (false, vertices_597), (false, vertices_101), (false, vertices_793), (false, vertices_929), (true, vertices_90), (true, vertices_138), (true, vertices_522), (true, vertices_162), (true, vertices_194), (true, vertices_642), (true, vertices_148), (true, vertices_164), (true, vertices_196), (true, vertices_388), (true, vertices_152), (true, vertices_392), (true, vertices_208)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 13 16 19 21 22 24 25 26 27
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_611) then 14 else
  if p.val = (false, vertices_309) then 17 else
  if p.val = (false, vertices_597) then 18 else
  if p.val = (false, vertices_101) then 12 else
  if p.val = (false, vertices_793) then 20 else
  if p.val = (false, vertices_929) then 23 else
  if p.val = (true, vertices_90) then 15 else
  if p.val = (true, vertices_138) then 0 else
  if p.val = (true, vertices_522) then 1 else
  if p.val = (true, vertices_162) then 2 else
  if p.val = (true, vertices_194) then 3 else
  if p.val = (true, vertices_642) then 4 else
  if p.val = (true, vertices_148) then 5 else
  if p.val = (true, vertices_164) then 6 else
  if p.val = (true, vertices_196) then 7 else
  if p.val = (true, vertices_388) then 8 else
  if p.val = (true, vertices_152) then 9 else
  if p.val = (true, vertices_392) then 10 else
  if p.val = (true, vertices_208) then 11 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_138), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_522), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_162), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_194), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_642), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_148), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_164), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_196), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_388), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_152), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_392), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_208), by decide +kernel⟩
  | 12 => Sum.inr ⟨(false, vertices_101), by decide +kernel⟩
  | 13 => Sum.inl 0
  | 14 => Sum.inr ⟨(false, vertices_611), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_90), by decide +kernel⟩
  | 16 => Sum.inl 1
  | 17 => Sum.inr ⟨(false, vertices_309), by decide +kernel⟩
  | 18 => Sum.inr ⟨(false, vertices_597), by decide +kernel⟩
  | 19 => Sum.inl 2
  | 20 => Sum.inr ⟨(false, vertices_793), by decide +kernel⟩
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
cert_row_4 0 0 1 5 6 4 230 194 1
cert_row_4 1 0 2 6 7 8 906 138 3
cert_row_4 2 2 3 6 7 1 412 152 3
cert_row_2 3 2 3 5 0 90
cert_rows
cert_pivot_2 4 8 1 0
cert_heightProof 4
cert_coverFacet 0 230
cert_cover_5 0 0 0 1 4 5 98 230 1
cert_coverFacet 1 218
cert_cover_5 1 3 0 2 3 6 90 218 3
cert_coverFacet 2 602
cert_cover_5 2 3 0 2 3 8 90 602 3
cert_coverFacet 3 906
cert_cover_5 3 1 0 2 6 7 138 906 3
cert_coverFacet 4 674
cert_cover_2 4 4 0 6 8 162 674 3
cert_coverFacet 5 412
cert_cover_5 5 2 1 2 3 6 148 412 1
cert_coverFacet 6 212
cert_cover_2 6 3 1 5 6 84 212 3
cert_coverFacet 7 420
cert_cover_2 7 4 1 6 7 164 420 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_163

end
end BundlePart0

section BundlePart1
/- Source: ProjectionCertificates/P0_164.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_164

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [651, 613, 569, 153, 241, 961, 302, 558, 838, 394, 898, 372, 312, 472, 25, 137, 521, 49, 145, 97, 545, 193, 577, 641, 46, 262, 518, 138, 266, 522, 386, 642, 770, 100, 292, 548, 324, 580, 56, 152, 280, 296, 552, 392, 112, 304, 208, 336, 448, 832, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_651, vertices_613, vertices_569, vertices_153, vertices_241, vertices_961, vertices_302, vertices_558, vertices_838, vertices_394, vertices_898, vertices_372, vertices_312, vertices_472] (by decide +kernel)
  polygons := literalFinset [vertices_25, vertices_137, vertices_521, vertices_49, vertices_145, vertices_97, vertices_545, vertices_193, vertices_577, vertices_641, vertices_46, vertices_262, vertices_518, vertices_138, vertices_266, vertices_522, vertices_386, vertices_642, vertices_770, vertices_100, vertices_292, vertices_548, vertices_324, vertices_580, vertices_56, vertices_152, vertices_280, vertices_296, vertices_552, vertices_392, vertices_112, vertices_304, vertices_208, vertices_336, vertices_448, vertices_832, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_651), (false, vertices_613), (false, vertices_569), (false, vertices_153), (false, vertices_241), (false, vertices_961), (true, vertices_46), (true, vertices_262), (true, vertices_518), (true, vertices_266), (true, vertices_386), (true, vertices_770), (true, vertices_292), (true, vertices_324), (true, vertices_280), (true, vertices_296), (true, vertices_392), (true, vertices_304), (true, vertices_336)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 13 16 18 20 22 23 25 26 27
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_651) then 14 else
  if p.val = (false, vertices_613) then 17 else
  if p.val = (false, vertices_569) then 19 else
  if p.val = (false, vertices_153) then 12 else
  if p.val = (false, vertices_241) then 21 else
  if p.val = (false, vertices_961) then 24 else
  if p.val = (true, vertices_46) then 15 else
  if p.val = (true, vertices_262) then 0 else
  if p.val = (true, vertices_518) then 1 else
  if p.val = (true, vertices_266) then 2 else
  if p.val = (true, vertices_386) then 3 else
  if p.val = (true, vertices_770) then 4 else
  if p.val = (true, vertices_292) then 5 else
  if p.val = (true, vertices_324) then 6 else
  if p.val = (true, vertices_280) then 7 else
  if p.val = (true, vertices_296) then 8 else
  if p.val = (true, vertices_392) then 9 else
  if p.val = (true, vertices_304) then 10 else
  if p.val = (true, vertices_336) then 11 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_262), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_518), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_266), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_386), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_770), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_292), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_324), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_280), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_296), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_392), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_304), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_336), by decide +kernel⟩
  | 12 => Sum.inr ⟨(false, vertices_153), by decide +kernel⟩
  | 13 => Sum.inl 0
  | 14 => Sum.inr ⟨(false, vertices_651), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_46), by decide +kernel⟩
  | 16 => Sum.inl 1
  | 17 => Sum.inr ⟨(false, vertices_613), by decide +kernel⟩
  | 18 => Sum.inl 2
  | 19 => Sum.inr ⟨(false, vertices_569), by decide +kernel⟩
  | 20 => Sum.inl 3
  | 21 => Sum.inr ⟨(false, vertices_241), by decide +kernel⟩
  | 22 => Sum.inl 4
  | 23 => Sum.inl 5
  | 24 => Sum.inr ⟨(false, vertices_961), by decide +kernel⟩
  | 25 => Sum.inl 6
  | 26 => Sum.inl 7
  | 27 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 5 7 8 838 262 2
cert_row_4 1 2 3 5 7 6 472 280 2
cert_row_4 2 1 4 5 7 3 372 100 3
cert_row_2 3 1 2 4 0 46
cert_rows
cert_pivot_2 8 6 3 0
cert_heightProof 4
cert_coverFacet 0 302
cert_cover_5 0 3 0 1 2 7 46 302 3
cert_coverFacet 1 558
cert_cover_5 1 3 0 1 2 8 46 558 3
cert_coverFacet 2 838
cert_cover_5 2 0 0 1 5 7 262 838 2
cert_coverFacet 3 394
cert_cover_2 3 2 0 6 7 138 394 3
cert_coverFacet 4 898
cert_cover_2 4 6 0 7 8 386 898 3
cert_coverFacet 5 372
cert_cover_5 5 2 1 3 4 5 100 372 1
cert_coverFacet 6 312
cert_cover_2 6 3 2 4 7 56 312 3
cert_coverFacet 7 472
cert_cover_5 7 1 2 3 5 6 152 472 2
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_164

end
end BundlePart1

section BundlePart2
/- Source: ProjectionCertificates/P0_167.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_167

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [779, 805, 345, 617, 113, 433, 406, 678, 774, 218, 282, 714, 420, 752, 73, 265, 521, 49, 81, 273, 97, 289, 545, 769, 134, 262, 518, 26, 202, 266, 522, 146, 274, 642, 770, 164, 292, 548, 388, 772, 88, 280, 584, 112, 176, 208, 400, 608, 416, 672, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_779, vertices_805, vertices_345, vertices_617, vertices_113, vertices_433, vertices_406, vertices_678, vertices_774, vertices_218, vertices_282, vertices_714, vertices_420, vertices_752] (by decide +kernel)
  polygons := literalFinset [vertices_73, vertices_265, vertices_521, vertices_49, vertices_81, vertices_273, vertices_97, vertices_289, vertices_545, vertices_769, vertices_134, vertices_262, vertices_518, vertices_26, vertices_202, vertices_266, vertices_522, vertices_146, vertices_274, vertices_642, vertices_770, vertices_164, vertices_292, vertices_548, vertices_388, vertices_772, vertices_88, vertices_280, vertices_584, vertices_112, vertices_176, vertices_208, vertices_400, vertices_608, vertices_416, vertices_672, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_779), (false, vertices_805), (false, vertices_345), (false, vertices_617), (false, vertices_113), (false, vertices_433), (true, vertices_134), (true, vertices_262), (true, vertices_518), (true, vertices_26), (true, vertices_202), (true, vertices_146), (true, vertices_274), (true, vertices_642), (true, vertices_164), (true, vertices_388), (true, vertices_208), (true, vertices_672), (true, vertices_704)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 13 16 18 21 23 24 25 26 27
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_779) then 14 else
  if p.val = (false, vertices_805) then 17 else
  if p.val = (false, vertices_345) then 19 else
  if p.val = (false, vertices_617) then 20 else
  if p.val = (false, vertices_113) then 12 else
  if p.val = (false, vertices_433) then 22 else
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
  if p.val = (true, vertices_672) then 10 else
  if p.val = (true, vertices_704) then 11 else
  0
cert_priority
cert_nodeAtPriority_56 134 262 518 26 146 274 642 164 388 208 672 704 113 779 202 805 345 617 433
cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 3 6 7 406 134 2
cert_row_4 1 0 4 6 8 1 678 642 1
cert_row_4 2 4 5 6 8 3 752 608 2
cert_row_2 3 2 5 6 0 202
cert_rows
cert_pivot_2 7 1 3 0
cert_heightProof 4
cert_coverFacet 0 406
cert_cover_5 0 0 0 1 3 6 134 406 2
cert_coverFacet 1 678
cert_cover_5 1 1 0 1 4 6 134 678 2
cert_coverFacet 2 774
cert_cover_2 2 1 0 7 8 262 774 3
cert_coverFacet 3 218
cert_cover_5 3 3 0 2 3 5 26 218 3
cert_coverFacet 4 282
cert_cover_2 4 2 0 3 7 26 282 3
cert_coverFacet 5 714
cert_cover_5 5 3 0 2 5 8 202 714 3
cert_coverFacet 6 420
cert_cover_2 6 4 1 6 7 164 420 3
cert_coverFacet 7 752
cert_cover_5 7 2 3 4 5 6 112 752 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_167

end
end BundlePart2

section BundlePart3
/- Source: ProjectionCertificates/P0_168.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_168

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [299, 211, 339, 675, 709, 617, 329, 662, 306, 562, 844, 468, 788, 824, 83, 35, 131, 259, 41, 73, 265, 545, 193, 321, 577, 641, 50, 146, 274, 530, 290, 546, 642, 148, 276, 532, 196, 324, 580, 644, 772, 296, 552, 328, 584, 776, 304, 560, 208, 336, 784]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_299, vertices_211, vertices_339, vertices_675, vertices_709, vertices_617, vertices_329, vertices_662, vertices_306, vertices_562, vertices_844, vertices_468, vertices_788, vertices_824] (by decide +kernel)
  polygons := literalFinset [vertices_83, vertices_35, vertices_131, vertices_259, vertices_41, vertices_73, vertices_265, vertices_545, vertices_193, vertices_321, vertices_577, vertices_641, vertices_50, vertices_146, vertices_274, vertices_530, vertices_290, vertices_546, vertices_642, vertices_148, vertices_276, vertices_532, vertices_196, vertices_324, vertices_580, vertices_644, vertices_772, vertices_296, vertices_552, vertices_328, vertices_584, vertices_776, vertices_304, vertices_560, vertices_208, vertices_336, vertices_784] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_299), (false, vertices_211), (false, vertices_339), (false, vertices_675), (false, vertices_709), (false, vertices_617), (false, vertices_329), (true, vertices_50), (true, vertices_530), (true, vertices_148), (true, vertices_276), (true, vertices_532), (true, vertices_324), (true, vertices_772), (true, vertices_776), (true, vertices_304), (true, vertices_560), (true, vertices_784)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 17 12 14 21 22 23 24 25 26
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_299) then 15 else
  if p.val = (false, vertices_211) then 19 else
  if p.val = (false, vertices_339) then 20 else
  if p.val = (false, vertices_675) then 18 else
  if p.val = (false, vertices_709) then 13 else
  if p.val = (false, vertices_617) then 16 else
  if p.val = (false, vertices_329) then 11 else
  if p.val = (true, vertices_50) then 0 else
  if p.val = (true, vertices_530) then 1 else
  if p.val = (true, vertices_148) then 2 else
  if p.val = (true, vertices_276) then 3 else
  if p.val = (true, vertices_532) then 4 else
  if p.val = (true, vertices_324) then 5 else
  if p.val = (true, vertices_772) then 6 else
  if p.val = (true, vertices_776) then 7 else
  if p.val = (true, vertices_304) then 8 else
  if p.val = (true, vertices_560) then 9 else
  if p.val = (true, vertices_784) then 10 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_50), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_530), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_148), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_276), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_532), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_324), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_772), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_776), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_304), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_560), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_784), by decide +kernel⟩
  | 11 => Sum.inr ⟨(false, vertices_329), by decide +kernel⟩
  | 12 => Sum.inl 1
  | 13 => Sum.inr ⟨(false, vertices_709), by decide +kernel⟩
  | 14 => Sum.inl 2
  | 15 => Sum.inr ⟨(false, vertices_299), by decide +kernel⟩
  | 16 => Sum.inr ⟨(false, vertices_617), by decide +kernel⟩
  | 17 => Sum.inl 0
  | 18 => Sum.inr ⟨(false, vertices_675), by decide +kernel⟩
  | 19 => Sum.inr ⟨(false, vertices_211), by decide +kernel⟩
  | 20 => Sum.inr ⟨(false, vertices_339), by decide +kernel⟩
  | 21 => Sum.inl 3
  | 22 => Sum.inl 4
  | 23 => Sum.inl 5
  | 24 => Sum.inl 6
  | 25 => Sum.inl 7
  | 26 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 1 3 6 8 0 662 148 3
cert_row_4 1 1 3 5 7 6 468 276 2
cert_row_4 2 2 5 7 8 1 844 328 3
cert_row_4 3 3 4 7 8 2 824 304 3
cert_rows
cert_pivot_2 0 6 1 2
cert_heightProof 4
cert_coverFacet 0 662
cert_cover_5 0 0 0 1 3 6 146 662 1
cert_coverFacet 1 306
cert_cover_2 1 3 0 4 7 50 306 3
cert_coverFacet 2 562
cert_cover_2 2 3 0 4 8 50 562 3
cert_coverFacet 3 844
cert_cover_5 3 2 1 2 5 7 324 844 1
cert_coverFacet 4 468
cert_cover_5 4 1 1 3 5 6 148 468 2
cert_coverFacet 5 788
cert_cover_2 5 3 1 7 8 276 788 3
cert_coverFacet 6 824
cert_cover_5 6 3 2 3 4 7 296 824 1
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_168

end
end BundlePart3

section BundlePart4
/- Source: ProjectionCertificates/P0_169.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_169

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [155, 357, 345, 425, 625, 689, 902, 602, 394, 778, 658, 844, 740, 420, 25, 137, 265, 561, 81, 145, 97, 161, 289, 321, 26, 138, 266, 522, 146, 530, 386, 642, 770, 100, 164, 292, 324, 580, 388, 644, 772, 88, 328, 584, 392, 776, 592, 656, 608, 416, 672]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_155, vertices_357, vertices_345, vertices_425, vertices_625, vertices_689, vertices_902, vertices_602, vertices_394, vertices_778, vertices_658, vertices_844, vertices_740, vertices_420] (by decide +kernel)
  polygons := literalFinset [vertices_25, vertices_137, vertices_265, vertices_561, vertices_81, vertices_145, vertices_97, vertices_161, vertices_289, vertices_321, vertices_26, vertices_138, vertices_266, vertices_522, vertices_146, vertices_530, vertices_386, vertices_642, vertices_770, vertices_100, vertices_164, vertices_292, vertices_324, vertices_580, vertices_388, vertices_644, vertices_772, vertices_88, vertices_328, vertices_584, vertices_392, vertices_776, vertices_592, vertices_656, vertices_608, vertices_416, vertices_672] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_155), (false, vertices_357), (false, vertices_345), (false, vertices_425), (false, vertices_625), (false, vertices_689), (true, vertices_266), (true, vertices_522), (true, vertices_530), (true, vertices_386), (true, vertices_642), (true, vertices_770), (true, vertices_164), (true, vertices_580), (true, vertices_388), (true, vertices_644), (true, vertices_772), (true, vertices_584), (true, vertices_776)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 13 15 17 20 23 24 25 26 27
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_155) then 14 else
  if p.val = (false, vertices_357) then 16 else
  if p.val = (false, vertices_345) then 18 else
  if p.val = (false, vertices_425) then 19 else
  if p.val = (false, vertices_625) then 21 else
  if p.val = (false, vertices_689) then 22 else
  if p.val = (true, vertices_266) then 0 else
  if p.val = (true, vertices_522) then 1 else
  if p.val = (true, vertices_530) then 2 else
  if p.val = (true, vertices_386) then 3 else
  if p.val = (true, vertices_642) then 4 else
  if p.val = (true, vertices_770) then 5 else
  if p.val = (true, vertices_164) then 6 else
  if p.val = (true, vertices_580) then 7 else
  if p.val = (true, vertices_388) then 8 else
  if p.val = (true, vertices_644) then 9 else
  if p.val = (true, vertices_772) then 10 else
  if p.val = (true, vertices_584) then 11 else
  if p.val = (true, vertices_776) then 12 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_266), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_522), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_530), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_386), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_642), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_770), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_164), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_580), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_388), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_644), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_772), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_584), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_776), by decide +kernel⟩
  | 13 => Sum.inl 0
  | 14 => Sum.inr ⟨(false, vertices_155), by decide +kernel⟩
  | 15 => Sum.inl 1
  | 16 => Sum.inr ⟨(false, vertices_357), by decide +kernel⟩
  | 17 => Sum.inl 2
  | 18 => Sum.inr ⟨(false, vertices_345), by decide +kernel⟩
  | 19 => Sum.inr ⟨(false, vertices_425), by decide +kernel⟩
  | 20 => Sum.inl 3
  | 21 => Sum.inr ⟨(false, vertices_625), by decide +kernel⟩
  | 22 => Sum.inr ⟨(false, vertices_689), by decide +kernel⟩
  | 23 => Sum.inl 4
  | 24 => Sum.inl 5
  | 25 => Sum.inl 6
  | 26 => Sum.inl 7
  | 27 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 2 5 8 3 602 522 2
cert_row_4 1 1 6 7 8 0 902 388 3
cert_row_4 2 1 5 7 8 2 844 324 3
cert_row_4 3 4 5 6 8 1 740 608 2
cert_rows
cert_pivot_2 3 0 2 1
cert_heightProof 4
cert_coverFacet 0 902
cert_cover_5 0 1 0 1 6 7 386 902 1
cert_coverFacet 1 602
cert_cover_5 1 0 0 2 3 5 26 602 3
cert_coverFacet 2 394
cert_cover_2 2 2 0 6 7 138 394 3
cert_coverFacet 3 778
cert_cover_2 3 2 0 7 8 266 778 3
cert_coverFacet 4 658
cert_cover_2 4 3 0 6 8 146 658 3
cert_coverFacet 5 844
cert_cover_5 5 2 1 2 5 7 324 844 1
cert_coverFacet 6 740
cert_cover_5 6 3 1 4 5 6 100 740 3
cert_coverFacet 7 420
cert_cover_2 7 4 1 6 7 164 420 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_169

end
end BundlePart4

section BundlePart5
/- Source: ProjectionCertificates/P0_181.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_181

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [135, 775, 299, 163, 589, 229, 793, 105, 710, 914, 418, 632, 440, 752, 7, 35, 131, 259, 69, 133, 517, 41, 73, 265, 521, 97, 161, 769, 134, 518, 162, 290, 386, 642, 770, 196, 580, 56, 280, 536, 104, 296, 584, 624, 176, 400, 656, 784, 224, 416, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_135, vertices_775, vertices_299, vertices_163, vertices_589, vertices_229, vertices_793, vertices_105, vertices_710, vertices_914, vertices_418, vertices_632, vertices_440, vertices_752] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_35, vertices_131, vertices_259, vertices_69, vertices_133, vertices_517, vertices_41, vertices_73, vertices_265, vertices_521, vertices_97, vertices_161, vertices_769, vertices_134, vertices_518, vertices_162, vertices_290, vertices_386, vertices_642, vertices_770, vertices_196, vertices_580, vertices_56, vertices_280, vertices_536, vertices_104, vertices_296, vertices_584, vertices_624, vertices_176, vertices_400, vertices_656, vertices_784, vertices_224, vertices_416, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_135), (false, vertices_775), (false, vertices_299), (false, vertices_163), (false, vertices_589), (false, vertices_229), (false, vertices_793), (false, vertices_105), (true, vertices_386), (true, vertices_642), (true, vertices_56), (true, vertices_624), (true, vertices_176), (true, vertices_400), (true, vertices_656), (true, vertices_416), (true, vertices_704)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 11 14 17 19 21 22 23 24 25
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_135) then 8 else
  if p.val = (false, vertices_775) then 12 else
  if p.val = (false, vertices_299) then 13 else
  if p.val = (false, vertices_163) then 9 else
  if p.val = (false, vertices_589) then 15 else
  if p.val = (false, vertices_229) then 16 else
  if p.val = (false, vertices_793) then 18 else
  if p.val = (false, vertices_105) then 10 else
  if p.val = (true, vertices_386) then 0 else
  if p.val = (true, vertices_642) then 1 else
  if p.val = (true, vertices_56) then 2 else
  if p.val = (true, vertices_624) then 20 else
  if p.val = (true, vertices_176) then 3 else
  if p.val = (true, vertices_400) then 4 else
  if p.val = (true, vertices_656) then 5 else
  if p.val = (true, vertices_416) then 6 else
  if p.val = (true, vertices_704) then 7 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_386), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_642), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_56), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_176), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_400), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_656), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_416), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_704), by decide +kernel⟩
  | 8 => Sum.inr ⟨(false, vertices_135), by decide +kernel⟩
  | 9 => Sum.inr ⟨(false, vertices_163), by decide +kernel⟩
  | 10 => Sum.inr ⟨(false, vertices_105), by decide +kernel⟩
  | 11 => Sum.inl 0
  | 12 => Sum.inr ⟨(false, vertices_775), by decide +kernel⟩
  | 13 => Sum.inr ⟨(false, vertices_299), by decide +kernel⟩
  | 14 => Sum.inl 1
  | 15 => Sum.inr ⟨(false, vertices_589), by decide +kernel⟩
  | 16 => Sum.inr ⟨(false, vertices_229), by decide +kernel⟩
  | 17 => Sum.inl 2
  | 18 => Sum.inr ⟨(false, vertices_793), by decide +kernel⟩
  | 19 => Sum.inl 3
  | 20 => Sum.inr ⟨(true, vertices_624), by decide +kernel⟩
  | 21 => Sum.inl 4
  | 22 => Sum.inl 5
  | 23 => Sum.inl 6
  | 24 => Sum.inl 7
  | 25 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 5 6 8 1 710 642 1
cert_row_4 1 3 6 7 8 0 914 400 3
cert_row_4 2 3 4 6 7 2 440 176 3
cert_row_2 3 4 5 8 3 624
cert_rows
cert_pivot_2 1 0 2 3
cert_heightProof 4
cert_coverFacet 0 710
cert_cover_5 0 0 0 1 5 6 134 710 2
cert_coverFacet 1 914
cert_cover_5 1 1 0 3 6 7 386 914 1
cert_coverFacet 2 418
cert_cover_2 2 4 0 6 7 162 418 3
cert_coverFacet 3 632
cert_cover_5 3 3 2 3 4 5 56 632 3
cert_coverFacet 4 440
cert_cover_5 4 2 2 3 4 6 56 440 3
cert_coverFacet 5 752
cert_cover_5 5 3 3 4 5 6 624 752 3
cert_coveringFacets
cert_coveringProof_6
cert_certificate 4 6
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_181

end
end BundlePart5

section BundlePart6
/- Source: ProjectionCertificates/P0_184.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_184

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [675, 805, 217, 361, 905, 225, 598, 614, 666, 210, 226, 796, 372, 344, 73, 137, 265, 97, 161, 289, 545, 193, 641, 769, 582, 82, 146, 530, 98, 162, 546, 194, 642, 84, 276, 532, 100, 292, 548, 772, 88, 152, 280, 536, 328, 648, 776, 208, 336, 224, 352]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_675, vertices_805, vertices_217, vertices_361, vertices_905, vertices_225, vertices_598, vertices_614, vertices_666, vertices_210, vertices_226, vertices_796, vertices_372, vertices_344] (by decide +kernel)
  polygons := literalFinset [vertices_73, vertices_137, vertices_265, vertices_97, vertices_161, vertices_289, vertices_545, vertices_193, vertices_641, vertices_769, vertices_582, vertices_82, vertices_146, vertices_530, vertices_98, vertices_162, vertices_546, vertices_194, vertices_642, vertices_84, vertices_276, vertices_532, vertices_100, vertices_292, vertices_548, vertices_772, vertices_88, vertices_152, vertices_280, vertices_536, vertices_328, vertices_648, vertices_776, vertices_208, vertices_336, vertices_224, vertices_352] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_675), (false, vertices_805), (false, vertices_217), (false, vertices_361), (false, vertices_905), (false, vertices_225), (true, vertices_582), (true, vertices_82), (true, vertices_146), (true, vertices_530), (true, vertices_98), (true, vertices_194), (true, vertices_84), (true, vertices_276), (true, vertices_532), (true, vertices_100), (true, vertices_280), (true, vertices_536), (true, vertices_336)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 13 16 18 22 23 24 25 26 27
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_675) then 14 else
  if p.val = (false, vertices_805) then 17 else
  if p.val = (false, vertices_217) then 19 else
  if p.val = (false, vertices_361) then 20 else
  if p.val = (false, vertices_905) then 21 else
  if p.val = (false, vertices_225) then 12 else
  if p.val = (true, vertices_582) then 15 else
  if p.val = (true, vertices_82) then 0 else
  if p.val = (true, vertices_146) then 1 else
  if p.val = (true, vertices_530) then 2 else
  if p.val = (true, vertices_98) then 3 else
  if p.val = (true, vertices_194) then 4 else
  if p.val = (true, vertices_84) then 5 else
  if p.val = (true, vertices_276) then 6 else
  if p.val = (true, vertices_532) then 7 else
  if p.val = (true, vertices_100) then 8 else
  if p.val = (true, vertices_280) then 9 else
  if p.val = (true, vertices_536) then 10 else
  if p.val = (true, vertices_336) then 11 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_82), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_146), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_530), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_98), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_194), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_84), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_276), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_532), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_100), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_280), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_536), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_336), by decide +kernel⟩
  | 12 => Sum.inr ⟨(false, vertices_225), by decide +kernel⟩
  | 13 => Sum.inl 0
  | 14 => Sum.inr ⟨(false, vertices_675), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_582), by decide +kernel⟩
  | 16 => Sum.inl 1
  | 17 => Sum.inr ⟨(false, vertices_805), by decide +kernel⟩
  | 18 => Sum.inl 2
  | 19 => Sum.inr ⟨(false, vertices_217), by decide +kernel⟩
  | 20 => Sum.inr ⟨(false, vertices_361), by decide +kernel⟩
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
cert_row_4 0 0 2 3 8 6 666 530 1
cert_row_4 1 1 3 7 8 2 796 276 3
cert_row_4 2 1 4 5 7 3 372 100 3
cert_row_2 3 1 5 8 0 582
cert_rows
cert_pivot_2 6 2 3 0
cert_heightProof 4
cert_coverFacet 0 598
cert_cover_5 0 3 0 1 3 5 582 598 2
cert_coverFacet 1 614
cert_cover_5 1 3 0 1 4 5 582 614 2
cert_coverFacet 2 666
cert_cover_5 2 0 0 2 3 6 146 666 1
cert_coverFacet 3 210
cert_cover_2 3 3 0 5 6 82 210 3
cert_coverFacet 4 226
cert_cover_2 4 4 0 5 6 98 226 3
cert_coverFacet 5 796
cert_cover_5 5 1 1 2 3 7 276 796 1
cert_coverFacet 6 372
cert_cover_5 6 2 1 3 4 5 84 372 2
cert_coverFacet 7 344
cert_cover_2 7 3 2 5 7 88 344 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_184

end
end BundlePart6

section BundlePart7
/- Source: ProjectionCertificates/P0_195.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_195

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [803, 301, 205, 613, 601, 777, 422, 794, 242, 626, 402, 396, 228, 472, 13, 37, 69, 73, 265, 521, 289, 545, 577, 769, 114, 146, 274, 530, 162, 290, 546, 386, 770, 140, 268, 100, 164, 292, 196, 388, 88, 280, 536, 200, 392, 776, 208, 592, 400, 224, 608]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_803, vertices_301, vertices_205, vertices_613, vertices_601, vertices_777, vertices_422, vertices_794, vertices_242, vertices_626, vertices_402, vertices_396, vertices_228, vertices_472] (by decide +kernel)
  polygons := literalFinset [vertices_13, vertices_37, vertices_69, vertices_73, vertices_265, vertices_521, vertices_289, vertices_545, vertices_577, vertices_769, vertices_114, vertices_146, vertices_274, vertices_530, vertices_162, vertices_290, vertices_546, vertices_386, vertices_770, vertices_140, vertices_268, vertices_100, vertices_164, vertices_292, vertices_196, vertices_388, vertices_88, vertices_280, vertices_536, vertices_200, vertices_392, vertices_776, vertices_208, vertices_592, vertices_400, vertices_224, vertices_608] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_803), (false, vertices_301), (false, vertices_205), (false, vertices_613), (false, vertices_601), (false, vertices_777), (true, vertices_114), (true, vertices_146), (true, vertices_274), (true, vertices_530), (true, vertices_162), (true, vertices_386), (true, vertices_164), (true, vertices_388), (true, vertices_280), (true, vertices_392), (true, vertices_208), (true, vertices_400), (true, vertices_224)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 13 16 20 22 23 24 25 26 27
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_803) then 14 else
  if p.val = (false, vertices_301) then 17 else
  if p.val = (false, vertices_205) then 18 else
  if p.val = (false, vertices_613) then 19 else
  if p.val = (false, vertices_601) then 21 else
  if p.val = (false, vertices_777) then 12 else
  if p.val = (true, vertices_114) then 15 else
  if p.val = (true, vertices_146) then 0 else
  if p.val = (true, vertices_274) then 1 else
  if p.val = (true, vertices_530) then 2 else
  if p.val = (true, vertices_162) then 3 else
  if p.val = (true, vertices_386) then 4 else
  if p.val = (true, vertices_164) then 5 else
  if p.val = (true, vertices_388) then 6 else
  if p.val = (true, vertices_280) then 7 else
  if p.val = (true, vertices_392) then 8 else
  if p.val = (true, vertices_208) then 9 else
  if p.val = (true, vertices_400) then 10 else
  if p.val = (true, vertices_224) then 11 else
  0
cert_priority
cert_nodeAtPriority_57 146 274 530 162 386 164 388 280 392 208 400 224 777 803 114 301 205 613 601
cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 4 6 7 1 422 162 3
cert_row_4 1 0 2 3 7 8 794 274 1
cert_row_4 2 3 5 6 7 2 472 208 3
cert_row_2 3 3 4 5 0 114
cert_rows
cert_pivot_2 1 8 2 0
cert_heightProof 4
cert_coverFacet 0 422
cert_cover_5 0 0 0 1 4 6 162 422 1
cert_coverFacet 1 794
cert_cover_5 1 1 0 2 3 7 274 794 1
cert_coverFacet 2 242
cert_cover_5 2 3 0 3 4 6 114 242 3
cert_coverFacet 3 626
cert_cover_5 3 3 0 3 4 8 114 626 3
cert_coverFacet 4 402
cert_cover_2 4 3 0 6 7 146 402 3
cert_coverFacet 5 396
cert_cover_2 5 2 1 6 7 140 396 3
cert_coverFacet 6 228
cert_cover_2 6 4 1 5 6 100 228 3
cert_coverFacet 7 472
cert_cover_5 7 2 2 3 5 6 88 472 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_195

end
end BundlePart7

section BundlePart8
/- Source: ProjectionCertificates/P0_197.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_197

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [899, 285, 181, 805, 409, 737, 334, 218, 394, 866, 706, 124, 356, 240, 21, 37, 261, 281, 145, 161, 545, 385, 641, 769, 74, 138, 266, 194, 322, 578, 386, 642, 770, 28, 76, 268, 52, 100, 292, 324, 88, 152, 392, 112, 176, 208, 224, 352, 608, 800, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_899, vertices_285, vertices_181, vertices_805, vertices_409, vertices_737, vertices_334, vertices_218, vertices_394, vertices_866, vertices_706, vertices_124, vertices_356, vertices_240] (by decide +kernel)
  polygons := literalFinset [vertices_21, vertices_37, vertices_261, vertices_281, vertices_145, vertices_161, vertices_545, vertices_385, vertices_641, vertices_769, vertices_74, vertices_138, vertices_266, vertices_194, vertices_322, vertices_578, vertices_386, vertices_642, vertices_770, vertices_28, vertices_76, vertices_268, vertices_52, vertices_100, vertices_292, vertices_324, vertices_88, vertices_152, vertices_392, vertices_112, vertices_176, vertices_208, vertices_224, vertices_352, vertices_608, vertices_800, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_899), (false, vertices_285), (false, vertices_181), (false, vertices_805), (false, vertices_409), (false, vertices_737), (true, vertices_74), (true, vertices_138), (true, vertices_266), (true, vertices_194), (true, vertices_322), (true, vertices_578), (true, vertices_76), (true, vertices_100), (true, vertices_324), (true, vertices_88), (true, vertices_112), (true, vertices_208), (true, vertices_352)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 13 15 18 21 22 24 25 26 27
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_899) then 14 else
  if p.val = (false, vertices_285) then 19 else
  if p.val = (false, vertices_181) then 16 else
  if p.val = (false, vertices_805) then 17 else
  if p.val = (false, vertices_409) then 20 else
  if p.val = (false, vertices_737) then 23 else
  if p.val = (true, vertices_74) then 0 else
  if p.val = (true, vertices_138) then 1 else
  if p.val = (true, vertices_266) then 2 else
  if p.val = (true, vertices_194) then 3 else
  if p.val = (true, vertices_322) then 4 else
  if p.val = (true, vertices_578) then 5 else
  if p.val = (true, vertices_76) then 6 else
  if p.val = (true, vertices_100) then 7 else
  if p.val = (true, vertices_324) then 8 else
  if p.val = (true, vertices_88) then 9 else
  if p.val = (true, vertices_112) then 10 else
  if p.val = (true, vertices_208) then 11 else
  if p.val = (true, vertices_352) then 12 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_74), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_138), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_266), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_194), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_322), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_578), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_76), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_100), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_324), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_88), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_112), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_208), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_352), by decide +kernel⟩
  | 13 => Sum.inl 0
  | 14 => Sum.inr ⟨(false, vertices_899), by decide +kernel⟩
  | 15 => Sum.inl 1
  | 16 => Sum.inr ⟨(false, vertices_181), by decide +kernel⟩
  | 17 => Sum.inr ⟨(false, vertices_805), by decide +kernel⟩
  | 18 => Sum.inl 2
  | 19 => Sum.inr ⟨(false, vertices_285), by decide +kernel⟩
  | 20 => Sum.inr ⟨(false, vertices_409), by decide +kernel⟩
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
cert_row_4 0 0 2 3 5 6 218 74 2
cert_row_4 1 0 4 5 7 8 866 322 1
cert_row_4 2 1 2 5 7 0 334 76 3
cert_row_4 3 2 3 4 5 1 124 88 2
cert_rows
cert_pivot_2 6 8 0 1
cert_heightProof 4
cert_coverFacet 0 334
cert_cover_5 0 2 0 1 2 5 74 334 1
cert_coverFacet 1 218
cert_cover_5 1 0 0 2 3 5 74 218 2
cert_coverFacet 2 394
cert_cover_2 2 2 0 6 7 138 394 3
cert_coverFacet 3 866
cert_cover_5 3 1 0 4 5 7 322 866 1
cert_coverFacet 4 706
cert_cover_2 4 5 0 6 8 194 706 3
cert_coverFacet 5 124
cert_cover_5 5 3 1 2 3 4 28 124 3
cert_coverFacet 6 356
cert_cover_2 6 4 1 5 7 100 356 3
cert_coverFacet 7 240
cert_cover_2 7 4 3 5 6 112 240 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_197

end
end BundlePart8

section BundlePart9
/- Source: ProjectionCertificates/P0_198.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_198

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [651, 595, 195, 781, 457, 865, 182, 662, 114, 482, 428, 652, 628, 804, 67, 131, 515, 137, 265, 521, 193, 321, 577, 769, 150, 50, 82, 530, 98, 162, 194, 642, 140, 268, 524, 52, 532, 164, 292, 548, 644, 772, 392, 648, 112, 592, 352, 608, 416, 800, 448]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_651, vertices_595, vertices_195, vertices_781, vertices_457, vertices_865, vertices_182, vertices_662, vertices_114, vertices_482, vertices_428, vertices_652, vertices_628, vertices_804] (by decide +kernel)
  polygons := literalFinset [vertices_67, vertices_131, vertices_515, vertices_137, vertices_265, vertices_521, vertices_193, vertices_321, vertices_577, vertices_769, vertices_150, vertices_50, vertices_82, vertices_530, vertices_98, vertices_162, vertices_194, vertices_642, vertices_140, vertices_268, vertices_524, vertices_52, vertices_532, vertices_164, vertices_292, vertices_548, vertices_644, vertices_772, vertices_392, vertices_648, vertices_112, vertices_592, vertices_352, vertices_608, vertices_416, vertices_800, vertices_448] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_651), (false, vertices_595), (false, vertices_195), (false, vertices_781), (false, vertices_457), (false, vertices_865), (true, vertices_150), (true, vertices_50), (true, vertices_98), (true, vertices_162), (true, vertices_140), (true, vertices_52), (true, vertices_532), (true, vertices_164), (true, vertices_292), (true, vertices_548), (true, vertices_644), (true, vertices_112), (true, vertices_416)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 16 13 19 21 22 24 25 26 27
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_651) then 17 else
  if p.val = (false, vertices_595) then 18 else
  if p.val = (false, vertices_195) then 12 else
  if p.val = (false, vertices_781) then 14 else
  if p.val = (false, vertices_457) then 20 else
  if p.val = (false, vertices_865) then 23 else
  if p.val = (true, vertices_150) then 15 else
  if p.val = (true, vertices_50) then 0 else
  if p.val = (true, vertices_98) then 1 else
  if p.val = (true, vertices_162) then 2 else
  if p.val = (true, vertices_140) then 3 else
  if p.val = (true, vertices_52) then 4 else
  if p.val = (true, vertices_532) then 5 else
  if p.val = (true, vertices_164) then 6 else
  if p.val = (true, vertices_292) then 7 else
  if p.val = (true, vertices_548) then 8 else
  if p.val = (true, vertices_644) then 9 else
  if p.val = (true, vertices_112) then 10 else
  if p.val = (true, vertices_416) then 11 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_50), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_98), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_162), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_140), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_52), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_532), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_164), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_292), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_548), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_644), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_112), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_416), by decide +kernel⟩
  | 12 => Sum.inr ⟨(false, vertices_195), by decide +kernel⟩
  | 13 => Sum.inl 1
  | 14 => Sum.inr ⟨(false, vertices_781), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_150), by decide +kernel⟩
  | 16 => Sum.inl 0
  | 17 => Sum.inr ⟨(false, vertices_651), by decide +kernel⟩
  | 18 => Sum.inr ⟨(false, vertices_595), by decide +kernel⟩
  | 19 => Sum.inl 2
  | 20 => Sum.inr ⟨(false, vertices_457), by decide +kernel⟩
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
cert_row_4 0 1 4 6 7 2 428 164 3
cert_row_4 1 0 4 5 6 7 482 98 3
cert_row_4 2 1 3 5 8 4 628 532 2
cert_row_2 3 1 3 6 0 150
cert_rows
cert_pivot_2 2 7 4 0
cert_heightProof 4
cert_coverFacet 0 182
cert_cover_5 0 3 0 1 3 4 150 182 3
cert_coverFacet 1 662
cert_cover_5 1 3 0 1 3 8 150 662 3
cert_coverFacet 2 114
cert_cover_2 2 3 0 4 5 50 114 3
cert_coverFacet 3 482
cert_cover_5 3 1 0 4 5 6 98 482 3
cert_coverFacet 4 428
cert_cover_5 4 0 1 2 4 6 140 428 2
cert_coverFacet 5 652
cert_cover_2 5 2 1 6 8 140 652 3
cert_coverFacet 6 628
cert_cover_5 6 2 1 3 4 5 52 628 3
cert_coverFacet 7 804
cert_cover_2 7 4 1 7 8 292 804 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_198

end
end BundlePart9

section BundlePart10
/- Source: ProjectionCertificates/P0_199.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_199

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [451, 557, 361, 713, 689, 417, 334, 214, 278, 434, 300, 588, 820, 724, 41, 73, 521, 161, 289, 545, 193, 321, 385, 641, 22, 70, 262, 146, 274, 194, 322, 386, 44, 76, 268, 524, 212, 276, 532, 292, 548, 580, 296, 328, 584, 176, 304, 560, 656, 416, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_451, vertices_557, vertices_361, vertices_713, vertices_689, vertices_417, vertices_334, vertices_214, vertices_278, vertices_434, vertices_300, vertices_588, vertices_820, vertices_724] (by decide +kernel)
  polygons := literalFinset [vertices_41, vertices_73, vertices_521, vertices_161, vertices_289, vertices_545, vertices_193, vertices_321, vertices_385, vertices_641, vertices_22, vertices_70, vertices_262, vertices_146, vertices_274, vertices_194, vertices_322, vertices_386, vertices_44, vertices_76, vertices_268, vertices_524, vertices_212, vertices_276, vertices_532, vertices_292, vertices_548, vertices_580, vertices_296, vertices_328, vertices_584, vertices_176, vertices_304, vertices_560, vertices_656, vertices_416, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_451), (false, vertices_557), (false, vertices_361), (false, vertices_713), (false, vertices_689), (false, vertices_417), (true, vertices_22), (true, vertices_70), (true, vertices_262), (true, vertices_146), (true, vertices_274), (true, vertices_76), (true, vertices_268), (true, vertices_212), (true, vertices_276), (true, vertices_532), (true, vertices_292), (true, vertices_580), (true, vertices_304)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 13 15 18 21 23 24 25 26 27
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_451) then 14 else
  if p.val = (false, vertices_557) then 16 else
  if p.val = (false, vertices_361) then 19 else
  if p.val = (false, vertices_713) then 20 else
  if p.val = (false, vertices_689) then 22 else
  if p.val = (false, vertices_417) then 12 else
  if p.val = (true, vertices_22) then 0 else
  if p.val = (true, vertices_70) then 1 else
  if p.val = (true, vertices_262) then 2 else
  if p.val = (true, vertices_146) then 3 else
  if p.val = (true, vertices_274) then 4 else
  if p.val = (true, vertices_76) then 5 else
  if p.val = (true, vertices_268) then 6 else
  if p.val = (true, vertices_212) then 17 else
  if p.val = (true, vertices_276) then 7 else
  if p.val = (true, vertices_532) then 8 else
  if p.val = (true, vertices_292) then 9 else
  if p.val = (true, vertices_580) then 10 else
  if p.val = (true, vertices_304) then 11 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_22), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_70), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_262), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_146), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_274), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_76), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_268), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_276), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_532), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_292), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_580), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_304), by decide +kernel⟩
  | 12 => Sum.inr ⟨(false, vertices_417), by decide +kernel⟩
  | 13 => Sum.inl 0
  | 14 => Sum.inr ⟨(false, vertices_451), by decide +kernel⟩
  | 15 => Sum.inl 1
  | 16 => Sum.inr ⟨(false, vertices_557), by decide +kernel⟩
  | 17 => Sum.inr ⟨(true, vertices_212), by decide +kernel⟩
  | 18 => Sum.inl 2
  | 19 => Sum.inr ⟨(false, vertices_361), by decide +kernel⟩
  | 20 => Sum.inr ⟨(false, vertices_713), by decide +kernel⟩
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
cert_row_4 0 0 1 5 7 2 334 70 3
cert_row_4 1 3 4 6 7 0 434 176 3
cert_row_4 2 1 3 7 8 4 820 276 3
cert_row_2 3 3 5 6 1 212
cert_rows
cert_pivot_2 2 0 4 1
cert_heightProof 4
cert_coverFacet 0 334
cert_cover_5 0 0 0 1 2 5 70 334 2
cert_coverFacet 1 214
cert_cover_5 1 3 0 1 3 5 22 214 3
cert_coverFacet 2 278
cert_cover_2 2 1 0 3 7 22 278 3
cert_coverFacet 3 434
cert_cover_5 3 1 0 3 4 6 146 434 2
cert_coverFacet 4 300
cert_cover_2 4 2 1 4 7 44 300 3
cert_coverFacet 5 588
cert_cover_2 5 2 1 5 8 76 588 3
cert_coverFacet 6 820
cert_cover_5 6 2 1 3 4 7 276 820 2
cert_coverFacet 7 724
cert_cover_5 7 3 1 3 5 8 212 724 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_199

end
end BundlePart10

section BundlePart11
/- Source: ProjectionCertificates/P0_200.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_200

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [647, 779, 403, 181, 597, 849, 682, 394, 620, 372, 676, 488, 840, 432, 131, 259, 515, 21, 133, 517, 593, 145, 273, 769, 138, 266, 522, 386, 642, 52, 84, 100, 164, 548, 580, 644, 104, 168, 552, 328, 584, 392, 776, 176, 304, 336, 400, 352, 416, 672, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_647, vertices_779, vertices_403, vertices_181, vertices_597, vertices_849, vertices_682, vertices_394, vertices_620, vertices_372, vertices_676, vertices_488, vertices_840, vertices_432] (by decide +kernel)
  polygons := literalFinset [vertices_131, vertices_259, vertices_515, vertices_21, vertices_133, vertices_517, vertices_593, vertices_145, vertices_273, vertices_769, vertices_138, vertices_266, vertices_522, vertices_386, vertices_642, vertices_52, vertices_84, vertices_100, vertices_164, vertices_548, vertices_580, vertices_644, vertices_104, vertices_168, vertices_552, vertices_328, vertices_584, vertices_392, vertices_776, vertices_176, vertices_304, vertices_336, vertices_400, vertices_352, vertices_416, vertices_672, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_647), (false, vertices_779), (false, vertices_403), (false, vertices_181), (false, vertices_597), (false, vertices_849), (true, vertices_138), (true, vertices_100), (true, vertices_548), (true, vertices_104), (true, vertices_168), (true, vertices_552), (true, vertices_328), (true, vertices_584), (true, vertices_392), (true, vertices_304), (true, vertices_352), (true, vertices_416), (true, vertices_672)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 13 17 19 20 23 24 25 26 27
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_647) then 14 else
  if p.val = (false, vertices_779) then 15 else
  if p.val = (false, vertices_403) then 16 else
  if p.val = (false, vertices_181) then 18 else
  if p.val = (false, vertices_597) then 21 else
  if p.val = (false, vertices_849) then 22 else
  if p.val = (true, vertices_138) then 0 else
  if p.val = (true, vertices_100) then 1 else
  if p.val = (true, vertices_548) then 2 else
  if p.val = (true, vertices_104) then 3 else
  if p.val = (true, vertices_168) then 4 else
  if p.val = (true, vertices_552) then 5 else
  if p.val = (true, vertices_328) then 6 else
  if p.val = (true, vertices_584) then 7 else
  if p.val = (true, vertices_392) then 8 else
  if p.val = (true, vertices_304) then 9 else
  if p.val = (true, vertices_352) then 10 else
  if p.val = (true, vertices_416) then 11 else
  if p.val = (true, vertices_672) then 12 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_138), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_100), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_548), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_104), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_168), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_552), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_328), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_584), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_392), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_304), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_352), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_416), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_672), by decide +kernel⟩
  | 13 => Sum.inl 0
  | 14 => Sum.inr ⟨(false, vertices_647), by decide +kernel⟩
  | 15 => Sum.inr ⟨(false, vertices_779), by decide +kernel⟩
  | 16 => Sum.inr ⟨(false, vertices_403), by decide +kernel⟩
  | 17 => Sum.inl 1
  | 18 => Sum.inr ⟨(false, vertices_181), by decide +kernel⟩
  | 19 => Sum.inl 2
  | 20 => Sum.inl 3
  | 21 => Sum.inr ⟨(false, vertices_597), by decide +kernel⟩
  | 22 => Sum.inr ⟨(false, vertices_849), by decide +kernel⟩
  | 23 => Sum.inl 4
  | 24 => Sum.inl 5
  | 25 => Sum.inl 6
  | 26 => Sum.inl 7
  | 27 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 2 4 6 8 0 682 168 3
cert_row_4 1 1 2 4 5 8 620 100 1
cert_row_4 2 3 4 5 7 1 372 304 2
cert_row_4 3 4 5 6 7 2 488 352 2
cert_rows
cert_pivot_2 0 8 1 2
cert_heightProof 4
cert_coverFacet 0 682
cert_cover_5 0 0 0 2 4 6 138 682 2
cert_coverFacet 1 394
cert_cover_2 1 2 0 6 7 138 394 3
cert_coverFacet 2 620
cert_cover_5 2 1 1 2 4 5 100 620 1
cert_coverFacet 3 372
cert_cover_5 3 2 1 3 4 5 52 372 3
cert_coverFacet 4 676
cert_cover_2 4 4 1 6 8 164 676 3
cert_coverFacet 5 488
cert_cover_5 5 3 2 4 5 6 104 488 3
cert_coverFacet 6 840
cert_cover_2 6 5 2 7 8 328 840 3
cert_coverFacet 7 432
cert_cover_2 7 4 3 6 7 176 432 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_200

end
end BundlePart11

section BundlePart12
/- Source: ProjectionCertificates/P0_201.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_201

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [899, 117, 149, 837, 645, 361, 433, 662, 314, 570, 842, 402, 620, 564, 21, 69, 133, 517, 49, 145, 97, 289, 321, 385, 641, 769, 58, 266, 522, 146, 274, 530, 386, 642, 770, 52, 148, 532, 100, 548, 580, 644, 104, 296, 552, 328, 584, 304, 560, 400, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_899, vertices_117, vertices_149, vertices_837, vertices_645, vertices_361, vertices_433, vertices_662, vertices_314, vertices_570, vertices_842, vertices_402, vertices_620, vertices_564] (by decide +kernel)
  polygons := literalFinset [vertices_21, vertices_69, vertices_133, vertices_517, vertices_49, vertices_145, vertices_97, vertices_289, vertices_321, vertices_385, vertices_641, vertices_769, vertices_58, vertices_266, vertices_522, vertices_146, vertices_274, vertices_530, vertices_386, vertices_642, vertices_770, vertices_52, vertices_148, vertices_532, vertices_100, vertices_548, vertices_580, vertices_644, vertices_104, vertices_296, vertices_552, vertices_328, vertices_584, vertices_304, vertices_560, vertices_400, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_899), (false, vertices_117), (false, vertices_149), (false, vertices_837), (false, vertices_645), (false, vertices_361), (false, vertices_433), (true, vertices_58), (true, vertices_266), (true, vertices_522), (true, vertices_146), (true, vertices_274), (true, vertices_530), (true, vertices_532), (true, vertices_548), (true, vertices_552), (true, vertices_584), (true, vertices_560)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 12 15 18 20 22 23 24 25 26
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_899) then 13 else
  if p.val = (false, vertices_117) then 16 else
  if p.val = (false, vertices_149) then 10 else
  if p.val = (false, vertices_837) then 17 else
  if p.val = (false, vertices_645) then 11 else
  if p.val = (false, vertices_361) then 19 else
  if p.val = (false, vertices_433) then 21 else
  if p.val = (true, vertices_58) then 14 else
  if p.val = (true, vertices_266) then 0 else
  if p.val = (true, vertices_522) then 1 else
  if p.val = (true, vertices_146) then 2 else
  if p.val = (true, vertices_274) then 3 else
  if p.val = (true, vertices_530) then 4 else
  if p.val = (true, vertices_532) then 5 else
  if p.val = (true, vertices_548) then 6 else
  if p.val = (true, vertices_552) then 7 else
  if p.val = (true, vertices_584) then 8 else
  if p.val = (true, vertices_560) then 9 else
  0
cert_priority
cert_nodeAtPriority_7 0 266 1 522 2 146 274 530 532 548 552 584 560 149 645 899 58 117 837 361 433
cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 3 8 6 662 530 1
cert_row_4 1 0 2 5 8 7 842 522 2
cert_row_4 2 2 4 5 8 1 620 104 3
cert_row_2 3 2 3 4 0 58
cert_rows
cert_pivot_2 6 7 1 0
cert_heightProof 4
cert_coverFacet 0 662
cert_cover_5 0 0 0 1 3 6 146 662 1
cert_coverFacet 1 314
cert_cover_5 1 3 0 2 3 7 58 314 3
cert_coverFacet 2 570
cert_cover_5 2 3 0 2 3 8 58 570 3
cert_coverFacet 3 842
cert_cover_5 3 1 0 2 5 7 266 842 2
cert_coverFacet 4 402
cert_cover_2 4 3 0 6 7 146 402 3
cert_coverFacet 5 620
cert_cover_5 5 2 1 2 4 5 100 620 1
cert_coverFacet 6 564
cert_cover_2 6 3 1 4 8 52 564 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_201

end
end BundlePart12

section BundlePart13
/- Source: ProjectionCertificates/P0_202.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_202

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [835, 229, 805, 581, 425, 465, 598, 410, 666, 810, 338, 684, 212, 660, 37, 69, 517, 161, 289, 193, 321, 577, 385, 769, 154, 266, 522, 82, 274, 530, 322, 578, 770, 84, 148, 532, 164, 548, 196, 580, 644, 168, 296, 552, 392, 648, 208, 336, 400, 656, 800]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_835, vertices_229, vertices_805, vertices_581, vertices_425, vertices_465, vertices_598, vertices_410, vertices_666, vertices_810, vertices_338, vertices_684, vertices_212, vertices_660] (by decide +kernel)
  polygons := literalFinset [vertices_37, vertices_69, vertices_517, vertices_161, vertices_289, vertices_193, vertices_321, vertices_577, vertices_385, vertices_769, vertices_154, vertices_266, vertices_522, vertices_82, vertices_274, vertices_530, vertices_322, vertices_578, vertices_770, vertices_84, vertices_148, vertices_532, vertices_164, vertices_548, vertices_196, vertices_580, vertices_644, vertices_168, vertices_296, vertices_552, vertices_392, vertices_648, vertices_208, vertices_336, vertices_400, vertices_656, vertices_800] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_835), (false, vertices_229), (false, vertices_805), (false, vertices_581), (false, vertices_425), (false, vertices_465), (true, vertices_154), (true, vertices_266), (true, vertices_522), (true, vertices_82), (true, vertices_274), (true, vertices_530), (true, vertices_84), (true, vertices_148), (true, vertices_532), (true, vertices_644), (true, vertices_552), (true, vertices_648), (true, vertices_656)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 13 16 19 21 23 24 25 26 27
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_835) then 14 else
  if p.val = (false, vertices_229) then 17 else
  if p.val = (false, vertices_805) then 18 else
  if p.val = (false, vertices_581) then 12 else
  if p.val = (false, vertices_425) then 20 else
  if p.val = (false, vertices_465) then 22 else
  if p.val = (true, vertices_154) then 15 else
  if p.val = (true, vertices_266) then 0 else
  if p.val = (true, vertices_522) then 1 else
  if p.val = (true, vertices_82) then 2 else
  if p.val = (true, vertices_274) then 3 else
  if p.val = (true, vertices_530) then 4 else
  if p.val = (true, vertices_84) then 5 else
  if p.val = (true, vertices_148) then 6 else
  if p.val = (true, vertices_532) then 7 else
  if p.val = (true, vertices_644) then 8 else
  if p.val = (true, vertices_552) then 9 else
  if p.val = (true, vertices_648) then 10 else
  if p.val = (true, vertices_656) then 11 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_266), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_522), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_82), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_274), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_530), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_84), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_148), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_532), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_644), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_552), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_648), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_656), by decide +kernel⟩
  | 12 => Sum.inr ⟨(false, vertices_581), by decide +kernel⟩
  | 13 => Sum.inl 0
  | 14 => Sum.inr ⟨(false, vertices_835), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_154), by decide +kernel⟩
  | 16 => Sum.inl 1
  | 17 => Sum.inr ⟨(false, vertices_229), by decide +kernel⟩
  | 18 => Sum.inr ⟨(false, vertices_805), by decide +kernel⟩
  | 19 => Sum.inl 2
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
cert_row_4 0 0 1 3 8 5 598 530 1
cert_row_4 1 0 2 4 8 7 810 522 2
cert_row_4 2 2 4 6 8 1 684 168 3
cert_row_2 3 2 3 6 0 154
cert_rows
cert_pivot_2 5 7 1 0
cert_heightProof 4
cert_coverFacet 0 598
cert_cover_5 0 0 0 1 3 5 82 598 1
cert_coverFacet 1 410
cert_cover_5 1 3 0 2 3 7 154 410 3
cert_coverFacet 2 666
cert_cover_5 2 3 0 2 3 8 154 666 3
cert_coverFacet 3 810
cert_cover_5 3 1 0 2 4 7 266 810 2
cert_coverFacet 4 338
cert_cover_2 4 3 0 5 7 82 338 3
cert_coverFacet 5 684
cert_cover_5 5 2 1 2 4 6 164 684 1
cert_coverFacet 6 212
cert_cover_2 6 3 1 5 6 84 212 3
cert_coverFacet 7 660
cert_cover_2 7 3 1 6 8 148 660 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_202

end
end BundlePart13

section BundlePart14
/- Source: ProjectionCertificates/P0_209.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_209

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [835, 205, 781, 581, 425, 465, 598, 810, 434, 562, 338, 188, 572, 212, 13, 69, 517, 137, 265, 193, 321, 577, 385, 769, 50, 82, 274, 530, 290, 546, 322, 578, 770, 60, 140, 524, 84, 148, 532, 196, 580, 168, 296, 552, 776, 176, 560, 208, 336, 400, 416]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_835, vertices_205, vertices_781, vertices_581, vertices_425, vertices_465, vertices_598, vertices_810, vertices_434, vertices_562, vertices_338, vertices_188, vertices_572, vertices_212] (by decide +kernel)
  polygons := literalFinset [vertices_13, vertices_69, vertices_517, vertices_137, vertices_265, vertices_193, vertices_321, vertices_577, vertices_385, vertices_769, vertices_50, vertices_82, vertices_274, vertices_530, vertices_290, vertices_546, vertices_322, vertices_578, vertices_770, vertices_60, vertices_140, vertices_524, vertices_84, vertices_148, vertices_532, vertices_196, vertices_580, vertices_168, vertices_296, vertices_552, vertices_776, vertices_176, vertices_560, vertices_208, vertices_336, vertices_400, vertices_416] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_835), (false, vertices_205), (false, vertices_781), (false, vertices_581), (false, vertices_425), (false, vertices_465), (true, vertices_50), (true, vertices_82), (true, vertices_274), (true, vertices_530), (true, vertices_290), (true, vertices_546), (true, vertices_60), (true, vertices_84), (true, vertices_148), (true, vertices_532), (true, vertices_552), (true, vertices_176), (true, vertices_560)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 13 18 21 15 23 24 25 26 27
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_835) then 14 else
  if p.val = (false, vertices_205) then 19 else
  if p.val = (false, vertices_781) then 20 else
  if p.val = (false, vertices_581) then 12 else
  if p.val = (false, vertices_425) then 22 else
  if p.val = (false, vertices_465) then 16 else
  if p.val = (true, vertices_50) then 0 else
  if p.val = (true, vertices_82) then 1 else
  if p.val = (true, vertices_274) then 2 else
  if p.val = (true, vertices_530) then 3 else
  if p.val = (true, vertices_290) then 4 else
  if p.val = (true, vertices_546) then 5 else
  if p.val = (true, vertices_60) then 17 else
  if p.val = (true, vertices_84) then 6 else
  if p.val = (true, vertices_148) then 7 else
  if p.val = (true, vertices_532) then 8 else
  if p.val = (true, vertices_552) then 9 else
  if p.val = (true, vertices_176) then 10 else
  if p.val = (true, vertices_560) then 11 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_50), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_82), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_274), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_530), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_290), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_546), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_84), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_148), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_532), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_552), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_176), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_560), by decide +kernel⟩
  | 12 => Sum.inr ⟨(false, vertices_581), by decide +kernel⟩
  | 13 => Sum.inl 0
  | 14 => Sum.inr ⟨(false, vertices_835), by decide +kernel⟩
  | 15 => Sum.inl 3
  | 16 => Sum.inr ⟨(false, vertices_465), by decide +kernel⟩
  | 17 => Sum.inr ⟨(true, vertices_60), by decide +kernel⟩
  | 18 => Sum.inl 1
  | 19 => Sum.inr ⟨(false, vertices_205), by decide +kernel⟩
  | 20 => Sum.inr ⟨(false, vertices_781), by decide +kernel⟩
  | 21 => Sum.inl 2
  | 22 => Sum.inr ⟨(false, vertices_425), by decide +kernel⟩
  | 23 => Sum.inl 4
  | 24 => Sum.inl 5
  | 25 => Sum.inl 6
  | 26 => Sum.inl 7
  | 27 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 3 8 5 598 530 1
cert_row_4 1 0 2 4 7 8 810 290 1
cert_row_4 2 3 4 6 7 0 434 176 3
cert_row_2 3 2 3 4 1 60
cert_rows
cert_pivot_2 5 8 0 1
cert_heightProof 4
cert_coverFacet 0 598
cert_cover_5 0 0 0 1 3 5 82 598 1
cert_coverFacet 1 810
cert_cover_5 1 1 0 2 4 7 290 810 1
cert_coverFacet 2 434
cert_cover_5 2 2 0 3 4 6 50 434 3
cert_coverFacet 3 562
cert_cover_2 3 3 0 4 8 50 562 3
cert_coverFacet 4 338
cert_cover_2 4 3 0 5 7 82 338 3
cert_coverFacet 5 188
cert_cover_5 5 3 1 2 3 6 60 188 3
cert_coverFacet 6 572
cert_cover_5 6 3 1 2 3 8 60 572 3
cert_coverFacet 7 212
cert_cover_2 7 3 1 5 6 84 212 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_209

end
end BundlePart14

section BundlePart15
/- Source: ProjectionCertificates/P0_210.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_210

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [787, 109, 781, 661, 229, 313, 177, 710, 842, 434, 658, 450, 588, 488, 13, 101, 133, 517, 41, 265, 49, 145, 273, 529, 161, 769, 146, 274, 530, 194, 322, 578, 386, 642, 770, 76, 524, 196, 580, 644, 104, 296, 328, 584, 776, 176, 304, 656, 224, 416, 448]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_787, vertices_109, vertices_781, vertices_661, vertices_229, vertices_313, vertices_177, vertices_710, vertices_842, vertices_434, vertices_658, vertices_450, vertices_588, vertices_488] (by decide +kernel)
  polygons := literalFinset [vertices_13, vertices_101, vertices_133, vertices_517, vertices_41, vertices_265, vertices_49, vertices_145, vertices_273, vertices_529, vertices_161, vertices_769, vertices_146, vertices_274, vertices_530, vertices_194, vertices_322, vertices_578, vertices_386, vertices_642, vertices_770, vertices_76, vertices_524, vertices_196, vertices_580, vertices_644, vertices_104, vertices_296, vertices_328, vertices_584, vertices_776, vertices_176, vertices_304, vertices_656, vertices_224, vertices_416, vertices_448] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_787), (false, vertices_109), (false, vertices_781), (false, vertices_661), (false, vertices_229), (false, vertices_313), (false, vertices_177), (true, vertices_146), (true, vertices_194), (true, vertices_322), (true, vertices_578), (true, vertices_386), (true, vertices_642), (true, vertices_580), (true, vertices_328), (true, vertices_584), (true, vertices_416), (true, vertices_448)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 12 17 14 21 22 23 24 25 26
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_787) then 13 else
  if p.val = (false, vertices_109) then 19 else
  if p.val = (false, vertices_781) then 15 else
  if p.val = (false, vertices_661) then 18 else
  if p.val = (false, vertices_229) then 20 else
  if p.val = (false, vertices_313) then 16 else
  if p.val = (false, vertices_177) then 11 else
  if p.val = (true, vertices_146) then 0 else
  if p.val = (true, vertices_194) then 1 else
  if p.val = (true, vertices_322) then 2 else
  if p.val = (true, vertices_578) then 3 else
  if p.val = (true, vertices_386) then 4 else
  if p.val = (true, vertices_642) then 5 else
  if p.val = (true, vertices_580) then 6 else
  if p.val = (true, vertices_328) then 7 else
  if p.val = (true, vertices_584) then 8 else
  if p.val = (true, vertices_416) then 9 else
  if p.val = (true, vertices_448) then 10 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_146), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_194), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_322), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_578), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_386), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_642), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_580), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_328), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_584), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_416), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_448), by decide +kernel⟩
  | 11 => Sum.inr ⟨(false, vertices_177), by decide +kernel⟩
  | 12 => Sum.inl 0
  | 13 => Sum.inr ⟨(false, vertices_787), by decide +kernel⟩
  | 14 => Sum.inl 2
  | 15 => Sum.inr ⟨(false, vertices_781), by decide +kernel⟩
  | 16 => Sum.inr ⟨(false, vertices_313), by decide +kernel⟩
  | 17 => Sum.inl 1
  | 18 => Sum.inr ⟨(false, vertices_661), by decide +kernel⟩
  | 19 => Sum.inr ⟨(false, vertices_109), by decide +kernel⟩
  | 20 => Sum.inr ⟨(false, vertices_229), by decide +kernel⟩
  | 21 => Sum.inl 3
  | 22 => Sum.inl 4
  | 23 => Sum.inl 5
  | 24 => Sum.inl 6
  | 25 => Sum.inl 7
  | 26 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 5 6 8 1 710 194 3
cert_row_4 1 0 2 5 7 8 842 322 1
cert_row_4 2 3 4 6 7 0 434 176 3
cert_row_4 3 4 5 6 7 2 488 224 3
cert_rows
cert_pivot_2 1 8 0 2
cert_heightProof 4
cert_coverFacet 0 710
cert_cover_5 0 0 0 1 5 6 194 710 1
cert_coverFacet 1 842
cert_cover_5 1 1 0 2 5 7 322 842 1
cert_coverFacet 2 434
cert_cover_5 2 2 0 3 4 6 146 434 2
cert_coverFacet 3 658
cert_cover_2 3 3 0 6 8 146 658 3
cert_coverFacet 4 450
cert_cover_2 4 5 0 6 7 194 450 3
cert_coverFacet 5 588
cert_cover_2 5 2 1 5 8 76 588 3
cert_coverFacet 6 488
cert_cover_5 6 3 2 4 5 6 104 488 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_210

end
end BundlePart15

section BundlePart16
/- Source: ProjectionCertificates/P0_214.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_214

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [899, 117, 661, 805, 185, 425, 710, 218, 810, 586, 394, 620, 212, 120, 21, 37, 517, 169, 49, 145, 289, 385, 641, 769, 74, 138, 266, 522, 194, 578, 386, 642, 770, 84, 148, 100, 548, 196, 580, 644, 56, 88, 152, 104, 296, 552, 584, 392, 112, 208, 800]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_899, vertices_117, vertices_661, vertices_805, vertices_185, vertices_425, vertices_710, vertices_218, vertices_810, vertices_586, vertices_394, vertices_620, vertices_212, vertices_120] (by decide +kernel)
  polygons := literalFinset [vertices_21, vertices_37, vertices_517, vertices_169, vertices_49, vertices_145, vertices_289, vertices_385, vertices_641, vertices_769, vertices_74, vertices_138, vertices_266, vertices_522, vertices_194, vertices_578, vertices_386, vertices_642, vertices_770, vertices_84, vertices_148, vertices_100, vertices_548, vertices_196, vertices_580, vertices_644, vertices_56, vertices_88, vertices_152, vertices_104, vertices_296, vertices_552, vertices_584, vertices_392, vertices_112, vertices_208, vertices_800] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_899), (false, vertices_117), (false, vertices_661), (false, vertices_805), (false, vertices_185), (false, vertices_425), (true, vertices_74), (true, vertices_138), (true, vertices_266), (true, vertices_522), (true, vertices_194), (true, vertices_578), (true, vertices_196), (true, vertices_580), (true, vertices_88), (true, vertices_104), (true, vertices_552), (true, vertices_584), (true, vertices_208)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 13 15 19 22 23 24 25 26 27
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_899) then 14 else
  if p.val = (false, vertices_117) then 16 else
  if p.val = (false, vertices_661) then 17 else
  if p.val = (false, vertices_805) then 18 else
  if p.val = (false, vertices_185) then 20 else
  if p.val = (false, vertices_425) then 21 else
  if p.val = (true, vertices_74) then 0 else
  if p.val = (true, vertices_138) then 1 else
  if p.val = (true, vertices_266) then 2 else
  if p.val = (true, vertices_522) then 3 else
  if p.val = (true, vertices_194) then 4 else
  if p.val = (true, vertices_578) then 5 else
  if p.val = (true, vertices_196) then 6 else
  if p.val = (true, vertices_580) then 7 else
  if p.val = (true, vertices_88) then 8 else
  if p.val = (true, vertices_104) then 9 else
  if p.val = (true, vertices_552) then 10 else
  if p.val = (true, vertices_584) then 11 else
  if p.val = (true, vertices_208) then 12 else
  0
cert_priority
cert_nodeAtPriority 0 74 1 138 2 266 522 194 578 196 580 88 104 552 584 208 899 117 661 805 185 425
cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 2 5 6 3 218 74 3
cert_row_4 1 0 1 5 8 6 710 578 1
cert_row_4 2 2 4 7 8 0 810 296 3
cert_row_4 3 2 4 5 8 1 620 104 3
cert_rows
cert_pivot_2 3 6 0 1
cert_heightProof 4
cert_coverFacet 0 710
cert_cover_5 0 1 0 1 5 6 194 710 1
cert_coverFacet 1 218
cert_cover_5 1 0 0 2 3 5 74 218 2
cert_coverFacet 2 810
cert_cover_5 2 2 0 2 4 7 266 810 2
cert_coverFacet 3 586
cert_cover_2 3 2 0 5 8 74 586 3
cert_coverFacet 4 394
cert_cover_2 4 2 0 6 7 138 394 3
cert_coverFacet 5 620
cert_cover_5 5 3 1 2 4 5 100 620 1
cert_coverFacet 6 212
cert_cover_2 6 3 1 5 6 84 212 3
cert_coverFacet 7 120
cert_cover_2 7 3 2 4 5 56 120 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_214

end
end BundlePart16

section BundlePart17
/- Source: ProjectionCertificates/P0_217.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_217

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [803, 661, 217, 793, 425, 673, 598, 422, 678, 326, 842, 460, 212, 600, 25, 137, 265, 145, 529, 161, 289, 545, 641, 769, 166, 70, 262, 518, 290, 546, 322, 578, 770, 84, 148, 532, 196, 324, 388, 644, 88, 536, 200, 328, 584, 392, 776, 208, 592, 416, 672]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_803, vertices_661, vertices_217, vertices_793, vertices_425, vertices_673, vertices_598, vertices_422, vertices_678, vertices_326, vertices_842, vertices_460, vertices_212, vertices_600] (by decide +kernel)
  polygons := literalFinset [vertices_25, vertices_137, vertices_265, vertices_145, vertices_529, vertices_161, vertices_289, vertices_545, vertices_641, vertices_769, vertices_166, vertices_70, vertices_262, vertices_518, vertices_290, vertices_546, vertices_322, vertices_578, vertices_770, vertices_84, vertices_148, vertices_532, vertices_196, vertices_324, vertices_388, vertices_644, vertices_88, vertices_536, vertices_200, vertices_328, vertices_584, vertices_392, vertices_776, vertices_208, vertices_592, vertices_416, vertices_672] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_803), (false, vertices_661), (false, vertices_217), (false, vertices_793), (false, vertices_425), (false, vertices_673), (true, vertices_166), (true, vertices_70), (true, vertices_262), (true, vertices_518), (true, vertices_322), (true, vertices_578), (true, vertices_84), (true, vertices_196), (true, vertices_324), (true, vertices_388), (true, vertices_328), (true, vertices_584), (true, vertices_592)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 13 16 18 22 23 24 25 26 27
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_803) then 14 else
  if p.val = (false, vertices_661) then 17 else
  if p.val = (false, vertices_217) then 19 else
  if p.val = (false, vertices_793) then 20 else
  if p.val = (false, vertices_425) then 21 else
  if p.val = (false, vertices_673) then 12 else
  if p.val = (true, vertices_166) then 15 else
  if p.val = (true, vertices_70) then 0 else
  if p.val = (true, vertices_262) then 1 else
  if p.val = (true, vertices_518) then 2 else
  if p.val = (true, vertices_322) then 3 else
  if p.val = (true, vertices_578) then 4 else
  if p.val = (true, vertices_84) then 5 else
  if p.val = (true, vertices_196) then 6 else
  if p.val = (true, vertices_324) then 7 else
  if p.val = (true, vertices_388) then 8 else
  if p.val = (true, vertices_328) then 9 else
  if p.val = (true, vertices_584) then 10 else
  if p.val = (true, vertices_592) then 11 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_70), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_262), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_518), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_322), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_578), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_84), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_196), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_324), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_388), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_328), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_584), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_592), by decide +kernel⟩
  | 12 => Sum.inr ⟨(false, vertices_673), by decide +kernel⟩
  | 13 => Sum.inl 0
  | 14 => Sum.inr ⟨(false, vertices_803), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_166), by decide +kernel⟩
  | 16 => Sum.inl 1
  | 17 => Sum.inr ⟨(false, vertices_661), by decide +kernel⟩
  | 18 => Sum.inl 2
  | 19 => Sum.inr ⟨(false, vertices_217), by decide +kernel⟩
  | 20 => Sum.inr ⟨(false, vertices_793), by decide +kernel⟩
  | 21 => Sum.inr ⟨(false, vertices_425), by decide +kernel⟩
  | 22 => Sum.inl 3
  | 23 => Sum.inl 4
  | 24 => Sum.inl 5
  | 25 => Sum.inl 6
  | 26 => Sum.inl 7
  | 27 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 5 8 3 598 70 3
cert_row_4 1 0 2 5 7 8 842 322 1
cert_row_4 2 1 5 6 7 2 460 196 3
cert_row_2 3 1 4 6 0 166
cert_rows
cert_pivot_2 3 8 2 0
cert_heightProof 4
cert_coverFacet 0 598
cert_cover_5 0 0 0 1 3 5 70 598 2
cert_coverFacet 1 422
cert_cover_5 1 3 0 1 4 7 166 422 3
cert_coverFacet 2 678
cert_cover_5 2 3 0 1 4 8 166 678 3
cert_coverFacet 3 326
cert_cover_2 3 1 0 5 7 70 326 3
cert_coverFacet 4 842
cert_cover_5 4 1 0 2 5 7 322 842 1
cert_coverFacet 5 460
cert_cover_5 5 2 1 2 5 6 196 460 1
cert_coverFacet 6 212
cert_cover_2 6 3 1 5 6 84 212 3
cert_coverFacet 7 600
cert_cover_2 7 3 2 5 8 88 600 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_217

end
end BundlePart17

section BundlePart18
/- Source: ProjectionCertificates/P0_219.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_219

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [707, 405, 677, 837, 345, 209, 570, 90, 842, 690, 210, 812, 420, 440, 133, 261, 517, 81, 145, 273, 193, 321, 577, 641, 26, 74, 522, 562, 82, 146, 194, 578, 642, 164, 292, 548, 388, 772, 56, 88, 280, 296, 552, 328, 776, 176, 208, 400, 416, 672, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_707, vertices_405, vertices_677, vertices_837, vertices_345, vertices_209, vertices_570, vertices_90, vertices_842, vertices_690, vertices_210, vertices_812, vertices_420, vertices_440] (by decide +kernel)
  polygons := literalFinset [vertices_133, vertices_261, vertices_517, vertices_81, vertices_145, vertices_273, vertices_193, vertices_321, vertices_577, vertices_641, vertices_26, vertices_74, vertices_522, vertices_562, vertices_82, vertices_146, vertices_194, vertices_578, vertices_642, vertices_164, vertices_292, vertices_548, vertices_388, vertices_772, vertices_56, vertices_88, vertices_280, vertices_296, vertices_552, vertices_328, vertices_776, vertices_176, vertices_208, vertices_400, vertices_416, vertices_672, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_707), (false, vertices_405), (false, vertices_677), (false, vertices_837), (false, vertices_345), (false, vertices_209), (true, vertices_26), (true, vertices_74), (true, vertices_522), (true, vertices_562), (true, vertices_82), (true, vertices_146), (true, vertices_292), (true, vertices_56), (true, vertices_296), (true, vertices_552), (true, vertices_776), (true, vertices_176), (true, vertices_416)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 13 16 20 22 23 24 25 26 27
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_707) then 14 else
  if p.val = (false, vertices_405) then 17 else
  if p.val = (false, vertices_677) then 18 else
  if p.val = (false, vertices_837) then 19 else
  if p.val = (false, vertices_345) then 21 else
  if p.val = (false, vertices_209) then 12 else
  if p.val = (true, vertices_26) then 0 else
  if p.val = (true, vertices_74) then 1 else
  if p.val = (true, vertices_522) then 2 else
  if p.val = (true, vertices_562) then 15 else
  if p.val = (true, vertices_82) then 3 else
  if p.val = (true, vertices_146) then 4 else
  if p.val = (true, vertices_292) then 5 else
  if p.val = (true, vertices_56) then 6 else
  if p.val = (true, vertices_296) then 7 else
  if p.val = (true, vertices_552) then 8 else
  if p.val = (true, vertices_776) then 9 else
  if p.val = (true, vertices_176) then 10 else
  if p.val = (true, vertices_416) then 11 else
  0
cert_priority
cert_nodeAtPriority_57 26 74 522 82 146 292 56 296 552 776 176 416 209 707 562 405 677 837 345
cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 2 7 8 5 842 522 2
cert_row_4 1 2 4 7 8 1 812 296 3
cert_row_4 2 3 4 6 7 2 440 176 3
cert_row_2 3 3 4 8 0 562
cert_rows
cert_pivot_2 5 1 2 0
cert_heightProof 4
cert_coverFacet 0 570
cert_cover_5 0 3 0 2 3 4 26 570 3
cert_coverFacet 1 90
cert_cover_2 1 2 0 3 5 26 90 3
cert_coverFacet 2 842
cert_cover_5 2 0 0 2 5 7 74 842 3
cert_coverFacet 3 690
cert_cover_5 3 3 0 3 4 6 562 690 3
cert_coverFacet 4 210
cert_cover_2 4 3 0 5 6 82 210 3
cert_coverFacet 5 812
cert_cover_5 5 1 1 2 4 7 292 812 1
cert_coverFacet 6 420
cert_cover_2 6 4 1 6 7 164 420 3
cert_coverFacet 7 440
cert_cover_5 7 2 2 3 4 6 56 440 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_219

end
end BundlePart18

section BundlePart19
/- Source: ProjectionCertificates/P0_220.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_220

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [651, 227, 835, 789, 345, 537, 201, 678, 610, 668, 284, 428, 868, 488, 67, 131, 515, 25, 73, 137, 521, 273, 529, 193, 321, 769, 98, 162, 546, 578, 642, 28, 140, 268, 276, 532, 164, 292, 548, 644, 772, 280, 536, 424, 200, 328, 648, 224, 352, 608, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_651, vertices_227, vertices_835, vertices_789, vertices_345, vertices_537, vertices_201, vertices_678, vertices_610, vertices_668, vertices_284, vertices_428, vertices_868, vertices_488] (by decide +kernel)
  polygons := literalFinset [vertices_67, vertices_131, vertices_515, vertices_25, vertices_73, vertices_137, vertices_521, vertices_273, vertices_529, vertices_193, vertices_321, vertices_769, vertices_98, vertices_162, vertices_546, vertices_578, vertices_642, vertices_28, vertices_140, vertices_268, vertices_276, vertices_532, vertices_164, vertices_292, vertices_548, vertices_644, vertices_772, vertices_280, vertices_536, vertices_424, vertices_200, vertices_328, vertices_648, vertices_224, vertices_352, vertices_608, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_651), (false, vertices_227), (false, vertices_835), (false, vertices_789), (false, vertices_345), (false, vertices_537), (false, vertices_201), (true, vertices_546), (true, vertices_28), (true, vertices_140), (true, vertices_268), (true, vertices_164), (true, vertices_292), (true, vertices_548), (true, vertices_644), (true, vertices_424), (true, vertices_352), (true, vertices_608)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 12 16 18 21 22 23 24 25 26
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_651) then 13 else
  if p.val = (false, vertices_227) then 14 else
  if p.val = (false, vertices_835) then 15 else
  if p.val = (false, vertices_789) then 17 else
  if p.val = (false, vertices_345) then 19 else
  if p.val = (false, vertices_537) then 10 else
  if p.val = (false, vertices_201) then 11 else
  if p.val = (true, vertices_546) then 0 else
  if p.val = (true, vertices_28) then 1 else
  if p.val = (true, vertices_140) then 2 else
  if p.val = (true, vertices_268) then 3 else
  if p.val = (true, vertices_164) then 4 else
  if p.val = (true, vertices_292) then 5 else
  if p.val = (true, vertices_548) then 6 else
  if p.val = (true, vertices_644) then 7 else
  if p.val = (true, vertices_424) then 20 else
  if p.val = (true, vertices_352) then 8 else
  if p.val = (true, vertices_608) then 9 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_546), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_28), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_140), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_268), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_164), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_292), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_548), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_644), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_352), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_608), by decide +kernel⟩
  | 10 => Sum.inr ⟨(false, vertices_537), by decide +kernel⟩
  | 11 => Sum.inr ⟨(false, vertices_201), by decide +kernel⟩
  | 12 => Sum.inl 0
  | 13 => Sum.inr ⟨(false, vertices_651), by decide +kernel⟩
  | 14 => Sum.inr ⟨(false, vertices_227), by decide +kernel⟩
  | 15 => Sum.inr ⟨(false, vertices_835), by decide +kernel⟩
  | 16 => Sum.inl 1
  | 17 => Sum.inr ⟨(false, vertices_789), by decide +kernel⟩
  | 18 => Sum.inl 2
  | 19 => Sum.inr ⟨(false, vertices_345), by decide +kernel⟩
  | 20 => Sum.inr ⟨(true, vertices_424), by decide +kernel⟩
  | 21 => Sum.inl 3
  | 22 => Sum.inl 4
  | 23 => Sum.inl 5
  | 24 => Sum.inl 6
  | 25 => Sum.inl 7
  | 26 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 1 4 6 8 0 678 164 3
cert_row_4 1 1 2 6 8 3 668 140 3
cert_row_4 2 4 5 7 8 1 868 352 3
cert_row_2 3 4 6 7 2 424
cert_rows
cert_pivot_2 0 3 1 2
cert_heightProof 4
cert_coverFacet 0 678
cert_cover_5 0 0 0 1 4 6 162 678 1
cert_coverFacet 1 610
cert_cover_2 1 4 0 5 8 98 610 3
cert_coverFacet 2 668
cert_cover_5 2 1 1 2 3 6 28 668 3
cert_coverFacet 3 284
cert_cover_2 3 2 1 3 7 28 284 3
cert_coverFacet 4 428
cert_cover_5 4 3 1 2 4 6 140 428 2
cert_coverFacet 5 868
cert_cover_5 5 2 1 4 5 7 292 868 2
cert_coverFacet 6 488
cert_cover_5 6 3 2 4 5 6 424 488 2
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_220

end
end BundlePart19

section BundlePart20
/- Source: ProjectionCertificates/P0_228.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_228

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [775, 213, 341, 677, 809, 433, 334, 710, 602, 778, 312, 568, 344, 752, 85, 133, 261, 517, 145, 273, 161, 289, 545, 769, 70, 262, 518, 74, 266, 522, 578, 770, 196, 324, 644, 56, 88, 280, 536, 296, 552, 328, 776, 176, 304, 560, 208, 336, 592, 672, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_775, vertices_213, vertices_341, vertices_677, vertices_809, vertices_433, vertices_334, vertices_710, vertices_602, vertices_778, vertices_312, vertices_568, vertices_344, vertices_752] (by decide +kernel)
  polygons := literalFinset [vertices_85, vertices_133, vertices_261, vertices_517, vertices_145, vertices_273, vertices_161, vertices_289, vertices_545, vertices_769, vertices_70, vertices_262, vertices_518, vertices_74, vertices_266, vertices_522, vertices_578, vertices_770, vertices_196, vertices_324, vertices_644, vertices_56, vertices_88, vertices_280, vertices_536, vertices_296, vertices_552, vertices_328, vertices_776, vertices_176, vertices_304, vertices_560, vertices_208, vertices_336, vertices_592, vertices_672, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_775), (false, vertices_213), (false, vertices_341), (false, vertices_677), (false, vertices_809), (false, vertices_433), (true, vertices_70), (true, vertices_74), (true, vertices_266), (true, vertices_522), (true, vertices_578), (true, vertices_56), (true, vertices_88), (true, vertices_280), (true, vertices_536), (true, vertices_328), (true, vertices_560), (true, vertices_592), (true, vertices_704)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 13 15 19 21 23 24 25 26 27
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_775) then 14 else
  if p.val = (false, vertices_213) then 17 else
  if p.val = (false, vertices_341) then 18 else
  if p.val = (false, vertices_677) then 16 else
  if p.val = (false, vertices_809) then 20 else
  if p.val = (false, vertices_433) then 22 else
  if p.val = (true, vertices_70) then 0 else
  if p.val = (true, vertices_74) then 1 else
  if p.val = (true, vertices_266) then 2 else
  if p.val = (true, vertices_522) then 3 else
  if p.val = (true, vertices_578) then 4 else
  if p.val = (true, vertices_56) then 5 else
  if p.val = (true, vertices_88) then 6 else
  if p.val = (true, vertices_280) then 7 else
  if p.val = (true, vertices_536) then 8 else
  if p.val = (true, vertices_328) then 9 else
  if p.val = (true, vertices_560) then 10 else
  if p.val = (true, vertices_592) then 11 else
  if p.val = (true, vertices_704) then 12 else
  0
cert_priority
cert_nodeAtPriority_11 70 74 266 522 578 56 88 280 536 328 560 592 704 775 677 213 341 809 433
cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 2 5 7 334 70 2
cert_row_4 1 0 5 6 8 1 710 578 2
cert_row_4 2 2 3 5 8 0 602 88 3
cert_row_4 3 4 5 6 8 3 752 672 1
cert_rows
cert_pivot_2 7 1 0 3
cert_heightProof 4
cert_coverFacet 0 334
cert_cover_5 0 0 0 1 2 5 70 334 2
cert_coverFacet 1 710
cert_cover_5 1 1 0 1 5 6 70 710 3
cert_coverFacet 2 602
cert_cover_5 2 2 0 2 3 5 74 602 2
cert_coverFacet 3 778
cert_cover_2 3 2 0 7 8 266 778 3
cert_coverFacet 4 312
cert_cover_2 4 3 2 4 7 56 312 3
cert_coverFacet 5 568
cert_cover_2 5 3 2 4 8 56 568 3
cert_coverFacet 6 344
cert_cover_2 6 3 2 5 7 88 344 3
cert_coverFacet 7 752
cert_cover_5 7 3 3 4 5 6 176 752 2
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_228

end
end BundlePart20

section BundlePart21
/- Source: ProjectionCertificates/P0_229.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_229

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [787, 837, 569, 153, 713, 465, 566, 358, 774, 186, 402, 482, 620, 232, 25, 137, 521, 145, 273, 529, 193, 321, 577, 769, 38, 262, 518, 50, 146, 274, 530, 354, 162, 386, 770, 100, 548, 324, 580, 772, 56, 152, 104, 168, 552, 200, 584, 560, 400, 224, 448]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_787, vertices_837, vertices_569, vertices_153, vertices_713, vertices_465, vertices_566, vertices_358, vertices_774, vertices_186, vertices_402, vertices_482, vertices_620, vertices_232] (by decide +kernel)
  polygons := literalFinset [vertices_25, vertices_137, vertices_521, vertices_145, vertices_273, vertices_529, vertices_193, vertices_321, vertices_577, vertices_769, vertices_38, vertices_262, vertices_518, vertices_50, vertices_146, vertices_274, vertices_530, vertices_354, vertices_162, vertices_386, vertices_770, vertices_100, vertices_548, vertices_324, vertices_580, vertices_772, vertices_56, vertices_152, vertices_104, vertices_168, vertices_552, vertices_200, vertices_584, vertices_560, vertices_400, vertices_224, vertices_448] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_787), (false, vertices_837), (false, vertices_569), (false, vertices_153), (false, vertices_713), (false, vertices_465), (true, vertices_38), (true, vertices_262), (true, vertices_518), (true, vertices_50), (true, vertices_146), (true, vertices_354), (true, vertices_162), (true, vertices_386), (true, vertices_100), (true, vertices_548), (true, vertices_104), (true, vertices_168), (true, vertices_224)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 13 16 18 21 23 24 25 26 27
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_787) then 14 else
  if p.val = (false, vertices_837) then 17 else
  if p.val = (false, vertices_569) then 19 else
  if p.val = (false, vertices_153) then 12 else
  if p.val = (false, vertices_713) then 20 else
  if p.val = (false, vertices_465) then 22 else
  if p.val = (true, vertices_38) then 0 else
  if p.val = (true, vertices_262) then 1 else
  if p.val = (true, vertices_518) then 2 else
  if p.val = (true, vertices_50) then 3 else
  if p.val = (true, vertices_146) then 4 else
  if p.val = (true, vertices_354) then 15 else
  if p.val = (true, vertices_162) then 5 else
  if p.val = (true, vertices_386) then 6 else
  if p.val = (true, vertices_100) then 7 else
  if p.val = (true, vertices_548) then 8 else
  if p.val = (true, vertices_104) then 9 else
  if p.val = (true, vertices_168) then 10 else
  if p.val = (true, vertices_224) then 11 else
  0
cert_priority
cert_nodeAtPriority_56 38 262 518 50 146 162 386 100 548 104 168 224 153 787 354 837 569 713 465
cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 2 3 4 6 186 50 1
cert_row_4 1 0 1 4 8 3 566 38 3
cert_row_4 2 2 4 5 8 1 620 104 3
cert_row_2 3 4 5 7 0 354
cert_rows
cert_pivot_2 6 3 1 0
cert_heightProof 4
cert_coverFacet 0 566
cert_cover_5 0 1 0 1 3 4 38 566 2
cert_coverFacet 1 358
cert_cover_5 1 3 0 1 4 5 38 358 3
cert_coverFacet 2 774
cert_cover_2 2 1 0 7 8 262 774 3
cert_coverFacet 3 186
cert_cover_5 3 0 0 2 3 4 50 186 1
cert_coverFacet 4 402
cert_cover_2 4 3 0 6 7 146 402 3
cert_coverFacet 5 482
cert_cover_5 5 3 0 4 5 6 354 482 3
cert_coverFacet 6 620
cert_cover_5 6 2 1 2 4 5 100 620 1
cert_coverFacet 7 232
cert_cover_2 7 4 2 5 6 104 232 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_229

end
end BundlePart21

section BundlePart22
/- Source: ProjectionCertificates/P0_234.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_234

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [787, 837, 665, 617, 457, 401, 406, 614, 166, 774, 682, 658, 364, 428, 73, 137, 521, 145, 273, 529, 321, 577, 385, 769, 38, 134, 262, 518, 146, 274, 530, 162, 546, 642, 770, 300, 100, 164, 324, 580, 388, 772, 104, 168, 552, 328, 392, 648, 400, 656, 608]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_787, vertices_837, vertices_665, vertices_617, vertices_457, vertices_401, vertices_406, vertices_614, vertices_166, vertices_774, vertices_682, vertices_658, vertices_364, vertices_428] (by decide +kernel)
  polygons := literalFinset [vertices_73, vertices_137, vertices_521, vertices_145, vertices_273, vertices_529, vertices_321, vertices_577, vertices_385, vertices_769, vertices_38, vertices_134, vertices_262, vertices_518, vertices_146, vertices_274, vertices_530, vertices_162, vertices_546, vertices_642, vertices_770, vertices_300, vertices_100, vertices_164, vertices_324, vertices_580, vertices_388, vertices_772, vertices_104, vertices_168, vertices_552, vertices_328, vertices_392, vertices_648, vertices_400, vertices_656, vertices_608] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_787), (false, vertices_837), (false, vertices_665), (false, vertices_617), (false, vertices_457), (false, vertices_401), (true, vertices_38), (true, vertices_134), (true, vertices_262), (true, vertices_518), (true, vertices_146), (true, vertices_162), (true, vertices_546), (true, vertices_642), (true, vertices_300), (true, vertices_100), (true, vertices_164), (true, vertices_388), (true, vertices_168)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 13 15 18 22 23 24 25 26 27
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_787) then 14 else
  if p.val = (false, vertices_837) then 16 else
  if p.val = (false, vertices_665) then 19 else
  if p.val = (false, vertices_617) then 20 else
  if p.val = (false, vertices_457) then 21 else
  if p.val = (false, vertices_401) then 12 else
  if p.val = (true, vertices_38) then 0 else
  if p.val = (true, vertices_134) then 1 else
  if p.val = (true, vertices_262) then 2 else
  if p.val = (true, vertices_518) then 3 else
  if p.val = (true, vertices_146) then 4 else
  if p.val = (true, vertices_162) then 5 else
  if p.val = (true, vertices_546) then 6 else
  if p.val = (true, vertices_642) then 7 else
  if p.val = (true, vertices_300) then 17 else
  if p.val = (true, vertices_100) then 8 else
  if p.val = (true, vertices_164) then 9 else
  if p.val = (true, vertices_388) then 10 else
  if p.val = (true, vertices_168) then 11 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_38), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_134), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_262), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_518), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_146), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_162), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_546), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_642), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_100), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_164), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_388), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_168), by decide +kernel⟩
  | 12 => Sum.inr ⟨(false, vertices_401), by decide +kernel⟩
  | 13 => Sum.inl 0
  | 14 => Sum.inr ⟨(false, vertices_787), by decide +kernel⟩
  | 15 => Sum.inl 1
  | 16 => Sum.inr ⟨(false, vertices_837), by decide +kernel⟩
  | 17 => Sum.inr ⟨(true, vertices_300), by decide +kernel⟩
  | 18 => Sum.inl 2
  | 19 => Sum.inr ⟨(false, vertices_665), by decide +kernel⟩
  | 20 => Sum.inr ⟨(false, vertices_617), by decide +kernel⟩
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
cert_row_4 0 0 1 6 7 3 406 134 3
cert_row_4 1 0 1 4 8 5 614 38 3
cert_row_4 2 2 4 6 8 0 682 168 3
cert_row_2 3 2 4 7 1 300
cert_rows
cert_pivot_2 3 5 0 1
cert_heightProof 4
cert_coverFacet 0 406
cert_cover_5 0 0 0 1 3 6 134 406 2
cert_coverFacet 1 614
cert_cover_5 1 1 0 1 4 5 38 614 3
cert_coverFacet 2 166
cert_cover_2 2 1 0 4 6 38 166 3
cert_coverFacet 3 774
cert_cover_2 3 1 0 7 8 262 774 3
cert_coverFacet 4 682
cert_cover_5 4 2 0 2 4 6 162 682 1
cert_coverFacet 5 658
cert_cover_2 5 3 0 6 8 146 658 3
cert_coverFacet 6 364
cert_cover_5 6 3 1 2 4 5 300 364 3
cert_coverFacet 7 428
cert_cover_5 7 3 1 2 4 6 300 428 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_234

end
end BundlePart22

section BundlePart23
/- Source: ProjectionCertificates/P0_235.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_235

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [203, 587, 181, 569, 409, 737, 454, 794, 394, 866, 372, 404, 228, 816, 75, 25, 137, 521, 49, 145, 161, 545, 193, 577, 138, 266, 522, 194, 322, 578, 386, 770, 52, 148, 276, 100, 164, 196, 324, 388, 280, 536, 392, 304, 560, 400, 784, 224, 352, 608, 800]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_203, vertices_587, vertices_181, vertices_569, vertices_409, vertices_737, vertices_454, vertices_794, vertices_394, vertices_866, vertices_372, vertices_404, vertices_228, vertices_816] (by decide +kernel)
  polygons := literalFinset [vertices_75, vertices_25, vertices_137, vertices_521, vertices_49, vertices_145, vertices_161, vertices_545, vertices_193, vertices_577, vertices_138, vertices_266, vertices_522, vertices_194, vertices_322, vertices_578, vertices_386, vertices_770, vertices_52, vertices_148, vertices_276, vertices_100, vertices_164, vertices_196, vertices_324, vertices_388, vertices_280, vertices_536, vertices_392, vertices_304, vertices_560, vertices_400, vertices_784, vertices_224, vertices_352, vertices_608, vertices_800] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_203), (false, vertices_587), (false, vertices_181), (false, vertices_569), (false, vertices_409), (false, vertices_737), (true, vertices_266), (true, vertices_322), (true, vertices_386), (true, vertices_770), (true, vertices_276), (true, vertices_100), (true, vertices_196), (true, vertices_324), (true, vertices_388), (true, vertices_304), (true, vertices_784), (true, vertices_352), (true, vertices_800)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 13 16 18 21 22 24 25 26 27
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_203) then 14 else
  if p.val = (false, vertices_587) then 15 else
  if p.val = (false, vertices_181) then 17 else
  if p.val = (false, vertices_569) then 19 else
  if p.val = (false, vertices_409) then 20 else
  if p.val = (false, vertices_737) then 23 else
  if p.val = (true, vertices_266) then 0 else
  if p.val = (true, vertices_322) then 1 else
  if p.val = (true, vertices_386) then 2 else
  if p.val = (true, vertices_770) then 3 else
  if p.val = (true, vertices_276) then 4 else
  if p.val = (true, vertices_100) then 5 else
  if p.val = (true, vertices_196) then 6 else
  if p.val = (true, vertices_324) then 7 else
  if p.val = (true, vertices_388) then 8 else
  if p.val = (true, vertices_304) then 9 else
  if p.val = (true, vertices_784) then 10 else
  if p.val = (true, vertices_352) then 11 else
  if p.val = (true, vertices_800) then 12 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_266), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_322), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_386), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_770), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_276), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_100), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_196), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_324), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_388), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_304), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_784), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_352), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_800), by decide +kernel⟩
  | 13 => Sum.inl 0
  | 14 => Sum.inr ⟨(false, vertices_203), by decide +kernel⟩
  | 15 => Sum.inr ⟨(false, vertices_587), by decide +kernel⟩
  | 16 => Sum.inl 1
  | 17 => Sum.inr ⟨(false, vertices_181), by decide +kernel⟩
  | 18 => Sum.inl 2
  | 19 => Sum.inr ⟨(false, vertices_569), by decide +kernel⟩
  | 20 => Sum.inr ⟨(false, vertices_409), by decide +kernel⟩
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
cert_row_4 0 0 1 5 7 6 454 322 1
cert_row_4 1 0 3 7 8 2 794 770 1
cert_row_4 2 4 5 7 8 0 866 352 3
cert_row_4 3 3 4 5 7 1 372 304 2
cert_rows
cert_pivot_2 6 2 0 1
cert_heightProof 4
cert_coverFacet 0 454
cert_cover_5 0 0 0 1 5 6 194 454 1
cert_coverFacet 1 794
cert_cover_5 1 1 0 2 3 7 266 794 2
cert_coverFacet 2 394
cert_cover_2 2 2 0 6 7 138 394 3
cert_coverFacet 3 866
cert_cover_5 3 2 0 4 5 7 322 866 1
cert_coverFacet 4 372
cert_cover_5 4 3 1 3 4 5 52 372 3
cert_coverFacet 5 404
cert_cover_2 5 3 1 6 7 148 404 3
cert_coverFacet 6 228
cert_cover_2 6 4 1 5 6 100 228 3
cert_coverFacet 7 816
cert_cover_2 7 4 3 7 8 304 816 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_235

end
end BundlePart23

section BundlePart24
/- Source: ProjectionCertificates/P0_236.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_236

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [339, 565, 277, 165, 453, 681, 721, 790, 810, 458, 714, 594, 428, 804, 21, 37, 133, 261, 81, 273, 529, 161, 545, 193, 321, 641, 202, 266, 522, 82, 274, 530, 322, 578, 770, 276, 532, 164, 292, 548, 388, 772, 168, 296, 552, 392, 648, 592, 800, 448, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_339, vertices_565, vertices_277, vertices_165, vertices_453, vertices_681, vertices_721, vertices_790, vertices_810, vertices_458, vertices_714, vertices_594, vertices_428, vertices_804] (by decide +kernel)
  polygons := literalFinset [vertices_21, vertices_37, vertices_133, vertices_261, vertices_81, vertices_273, vertices_529, vertices_161, vertices_545, vertices_193, vertices_321, vertices_641, vertices_202, vertices_266, vertices_522, vertices_82, vertices_274, vertices_530, vertices_322, vertices_578, vertices_770, vertices_276, vertices_532, vertices_164, vertices_292, vertices_548, vertices_388, vertices_772, vertices_168, vertices_296, vertices_552, vertices_392, vertices_648, vertices_592, vertices_800, vertices_448, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_339), (false, vertices_565), (false, vertices_277), (false, vertices_165), (false, vertices_453), (false, vertices_681), (false, vertices_721), (true, vertices_202), (true, vertices_266), (true, vertices_522), (true, vertices_530), (true, vertices_578), (true, vertices_770), (true, vertices_292), (true, vertices_772), (true, vertices_296), (true, vertices_392), (true, vertices_800)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 12 15 18 20 22 23 24 25 26
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_339) then 13 else
  if p.val = (false, vertices_565) then 16 else
  if p.val = (false, vertices_277) then 10 else
  if p.val = (false, vertices_165) then 11 else
  if p.val = (false, vertices_453) then 17 else
  if p.val = (false, vertices_681) then 19 else
  if p.val = (false, vertices_721) then 21 else
  if p.val = (true, vertices_202) then 14 else
  if p.val = (true, vertices_266) then 0 else
  if p.val = (true, vertices_522) then 1 else
  if p.val = (true, vertices_530) then 2 else
  if p.val = (true, vertices_578) then 3 else
  if p.val = (true, vertices_770) then 4 else
  if p.val = (true, vertices_292) then 5 else
  if p.val = (true, vertices_772) then 6 else
  if p.val = (true, vertices_296) then 7 else
  if p.val = (true, vertices_392) then 8 else
  if p.val = (true, vertices_800) then 9 else
  0
cert_priority
cert_nodeAtPriority_7 0 266 1 522 2 530 578 770 292 772 296 392 800 277 165 339 202 565 453 681 721
cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 7 8 3 790 770 1
cert_row_4 1 0 2 4 7 8 810 266 2
cert_row_4 2 2 4 6 7 1 428 168 3
cert_row_2 3 2 5 6 0 202
cert_rows
cert_pivot_2 3 8 1 0
cert_heightProof 4
cert_coverFacet 0 790
cert_cover_5 0 0 0 1 3 7 274 790 1
cert_coverFacet 1 810
cert_cover_5 1 1 0 2 4 7 266 810 2
cert_coverFacet 2 458
cert_cover_5 2 3 0 2 5 7 202 458 3
cert_coverFacet 3 714
cert_cover_5 3 3 0 2 5 8 202 714 3
cert_coverFacet 4 594
cert_cover_2 4 3 0 5 8 82 594 3
cert_coverFacet 5 428
cert_cover_5 5 2 1 2 4 6 164 428 1
cert_coverFacet 6 804
cert_cover_2 6 4 1 7 8 292 804 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_236

end
end BundlePart24

section BundlePart25
/- Source: ProjectionCertificates/P0_237.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_237

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [647, 587, 195, 301, 525, 165, 457, 433, 690, 466, 850, 844, 820, 676, 67, 131, 515, 13, 37, 133, 517, 73, 265, 521, 161, 289, 193, 385, 338, 146, 530, 194, 578, 642, 268, 524, 164, 292, 548, 644, 772, 328, 584, 176, 304, 560, 400, 784, 672, 448, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_647, vertices_587, vertices_195, vertices_301, vertices_525, vertices_165, vertices_457, vertices_433, vertices_690, vertices_466, vertices_850, vertices_844, vertices_820, vertices_676] (by decide +kernel)
  polygons := literalFinset [vertices_67, vertices_131, vertices_515, vertices_13, vertices_37, vertices_133, vertices_517, vertices_73, vertices_265, vertices_521, vertices_161, vertices_289, vertices_193, vertices_385, vertices_338, vertices_146, vertices_530, vertices_194, vertices_578, vertices_642, vertices_268, vertices_524, vertices_164, vertices_292, vertices_548, vertices_644, vertices_772, vertices_328, vertices_584, vertices_176, vertices_304, vertices_560, vertices_400, vertices_784, vertices_672, vertices_448, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_647), (false, vertices_587), (false, vertices_195), (false, vertices_301), (false, vertices_525), (false, vertices_165), (false, vertices_457), (false, vertices_433), (true, vertices_338), (true, vertices_146), (true, vertices_530), (true, vertices_548), (true, vertices_772), (true, vertices_560), (true, vertices_784), (true, vertices_672), (true, vertices_832)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 14 11 17 19 21 22 23 24 25
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_647) then 12 else
  if p.val = (false, vertices_587) then 15 else
  if p.val = (false, vertices_195) then 8 else
  if p.val = (false, vertices_301) then 13 else
  if p.val = (false, vertices_525) then 9 else
  if p.val = (false, vertices_165) then 10 else
  if p.val = (false, vertices_457) then 18 else
  if p.val = (false, vertices_433) then 20 else
  if p.val = (true, vertices_338) then 16 else
  if p.val = (true, vertices_146) then 0 else
  if p.val = (true, vertices_530) then 1 else
  if p.val = (true, vertices_548) then 2 else
  if p.val = (true, vertices_772) then 3 else
  if p.val = (true, vertices_560) then 4 else
  if p.val = (true, vertices_784) then 5 else
  if p.val = (true, vertices_672) then 6 else
  if p.val = (true, vertices_832) then 7 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_146), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_530), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_548), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_772), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_560), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_784), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_672), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_832), by decide +kernel⟩
  | 8 => Sum.inr ⟨(false, vertices_195), by decide +kernel⟩
  | 9 => Sum.inr ⟨(false, vertices_525), by decide +kernel⟩
  | 10 => Sum.inr ⟨(false, vertices_165), by decide +kernel⟩
  | 11 => Sum.inl 1
  | 12 => Sum.inr ⟨(false, vertices_647), by decide +kernel⟩
  | 13 => Sum.inr ⟨(false, vertices_301), by decide +kernel⟩
  | 14 => Sum.inl 0
  | 15 => Sum.inr ⟨(false, vertices_587), by decide +kernel⟩
  | 16 => Sum.inr ⟨(true, vertices_338), by decide +kernel⟩
  | 17 => Sum.inl 2
  | 18 => Sum.inr ⟨(false, vertices_457), by decide +kernel⟩
  | 19 => Sum.inl 3
  | 20 => Sum.inr ⟨(false, vertices_433), by decide +kernel⟩
  | 21 => Sum.inl 4
  | 22 => Sum.inl 5
  | 23 => Sum.inl 6
  | 24 => Sum.inl 7
  | 25 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 3 4 8 6 690 530 2
cert_row_4 1 1 5 7 8 2 844 772 1
cert_row_4 2 3 4 7 8 1 820 304 3
cert_row_2 3 3 5 7 0 338
cert_rows
cert_pivot_2 6 2 1 0
cert_heightProof 4
cert_coverFacet 0 690
cert_cover_5 0 0 0 3 4 6 146 690 2
cert_coverFacet 1 466
cert_cover_5 1 3 0 3 5 6 338 466 3
cert_coverFacet 2 850
cert_cover_5 2 3 0 3 5 8 338 850 3
cert_coverFacet 3 844
cert_cover_5 3 1 1 2 5 7 268 844 2
cert_coverFacet 4 820
cert_cover_5 4 2 1 3 4 7 292 820 1
cert_coverFacet 5 676
cert_cover_2 5 4 1 6 8 164 676 3
cert_coveringFacets
cert_coveringProof_6
cert_certificate 4 6
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_237

end
end BundlePart25

section BundlePart26
/- Source: ProjectionCertificates/P0_238.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_238

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [551, 587, 99, 541, 277, 357, 409, 457, 914, 482, 802, 706, 820, 728, 35, 67, 515, 21, 37, 261, 517, 25, 73, 393, 521, 273, 97, 321, 98, 290, 546, 194, 578, 386, 642, 770, 276, 532, 292, 548, 152, 536, 200, 584, 400, 656, 784, 352, 800, 448, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_551, vertices_587, vertices_99, vertices_541, vertices_277, vertices_357, vertices_409, vertices_457, vertices_914, vertices_482, vertices_802, vertices_706, vertices_820, vertices_728] (by decide +kernel)
  polygons := literalFinset [vertices_35, vertices_67, vertices_515, vertices_21, vertices_37, vertices_261, vertices_517, vertices_25, vertices_73, vertices_393, vertices_521, vertices_273, vertices_97, vertices_321, vertices_98, vertices_290, vertices_546, vertices_194, vertices_578, vertices_386, vertices_642, vertices_770, vertices_276, vertices_532, vertices_292, vertices_548, vertices_152, vertices_536, vertices_200, vertices_584, vertices_400, vertices_656, vertices_784, vertices_352, vertices_800, vertices_448, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_551), (false, vertices_587), (false, vertices_99), (false, vertices_541), (false, vertices_277), (false, vertices_357), (false, vertices_409), (false, vertices_457), (true, vertices_290), (true, vertices_194), (true, vertices_386), (true, vertices_642), (true, vertices_770), (true, vertices_656), (true, vertices_784), (true, vertices_800), (true, vertices_704)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 11 14 17 20 21 22 23 24 25
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_551) then 12 else
  if p.val = (false, vertices_587) then 13 else
  if p.val = (false, vertices_99) then 9 else
  if p.val = (false, vertices_541) then 15 else
  if p.val = (false, vertices_277) then 10 else
  if p.val = (false, vertices_357) then 16 else
  if p.val = (false, vertices_409) then 18 else
  if p.val = (false, vertices_457) then 19 else
  if p.val = (true, vertices_290) then 0 else
  if p.val = (true, vertices_194) then 1 else
  if p.val = (true, vertices_386) then 2 else
  if p.val = (true, vertices_642) then 3 else
  if p.val = (true, vertices_770) then 4 else
  if p.val = (true, vertices_656) then 5 else
  if p.val = (true, vertices_784) then 6 else
  if p.val = (true, vertices_800) then 7 else
  if p.val = (true, vertices_704) then 8 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_290), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_194), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_386), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_642), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_770), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_656), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_784), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_800), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_704), by decide +kernel⟩
  | 9 => Sum.inr ⟨(false, vertices_99), by decide +kernel⟩
  | 10 => Sum.inr ⟨(false, vertices_277), by decide +kernel⟩
  | 11 => Sum.inl 0
  | 12 => Sum.inr ⟨(false, vertices_551), by decide +kernel⟩
  | 13 => Sum.inr ⟨(false, vertices_587), by decide +kernel⟩
  | 14 => Sum.inl 1
  | 15 => Sum.inr ⟨(false, vertices_541), by decide +kernel⟩
  | 16 => Sum.inr ⟨(false, vertices_357), by decide +kernel⟩
  | 17 => Sum.inl 2
  | 18 => Sum.inr ⟨(false, vertices_409), by decide +kernel⟩
  | 19 => Sum.inr ⟨(false, vertices_457), by decide +kernel⟩
  | 20 => Sum.inl 3
  | 21 => Sum.inl 4
  | 22 => Sum.inl 5
  | 23 => Sum.inl 6
  | 24 => Sum.inl 7
  | 25 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 3 4 7 8 1 820 784 1
cert_row_4 1 0 5 6 7 4 482 194 3
cert_row_4 2 3 6 7 8 0 914 400 3
cert_row_4 3 3 5 6 8 2 728 656 1
cert_rows
cert_pivot_2 1 4 0 2
cert_heightProof 4
cert_coverFacet 0 914
cert_cover_5 0 2 0 3 6 7 386 914 1
cert_coverFacet 1 482
cert_cover_5 1 1 0 4 5 6 98 482 3
cert_coverFacet 2 802
cert_cover_2 2 4 0 7 8 290 802 3
cert_coverFacet 3 706
cert_cover_2 3 5 0 6 8 194 706 3
cert_coverFacet 4 820
cert_cover_5 4 0 1 3 4 7 276 820 2
cert_coverFacet 5 728
cert_cover_5 5 3 2 3 5 6 152 728 2
cert_coveringFacets
cert_coveringProof_6
cert_certificate 4 6
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_238

end
end BundlePart26

section BundlePart27
/- Source: ProjectionCertificates/P0_239.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_239

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [647, 285, 141, 837, 89, 713, 369, 398, 806, 426, 738, 248, 312, 864, 13, 133, 261, 517, 25, 73, 137, 81, 273, 321, 577, 641, 134, 262, 518, 394, 162, 290, 546, 642, 140, 268, 772, 56, 88, 280, 168, 296, 200, 112, 304, 224, 352, 608, 800, 704, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_647, vertices_285, vertices_141, vertices_837, vertices_89, vertices_713, vertices_369, vertices_398, vertices_806, vertices_426, vertices_738, vertices_248, vertices_312, vertices_864] (by decide +kernel)
  polygons := literalFinset [vertices_13, vertices_133, vertices_261, vertices_517, vertices_25, vertices_73, vertices_137, vertices_81, vertices_273, vertices_321, vertices_577, vertices_641, vertices_134, vertices_262, vertices_518, vertices_394, vertices_162, vertices_290, vertices_546, vertices_642, vertices_140, vertices_268, vertices_772, vertices_56, vertices_88, vertices_280, vertices_168, vertices_296, vertices_200, vertices_112, vertices_304, vertices_224, vertices_352, vertices_608, vertices_800, vertices_704, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_647), (false, vertices_285), (false, vertices_141), (false, vertices_837), (false, vertices_89), (false, vertices_713), (false, vertices_369), (true, vertices_262), (true, vertices_394), (true, vertices_162), (true, vertices_290), (true, vertices_546), (true, vertices_56), (true, vertices_168), (true, vertices_296), (true, vertices_224), (true, vertices_608), (true, vertices_800)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 12 15 18 20 22 23 24 25 26
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_647) then 13 else
  if p.val = (false, vertices_285) then 16 else
  if p.val = (false, vertices_141) then 10 else
  if p.val = (false, vertices_837) then 17 else
  if p.val = (false, vertices_89) then 11 else
  if p.val = (false, vertices_713) then 19 else
  if p.val = (false, vertices_369) then 21 else
  if p.val = (true, vertices_262) then 0 else
  if p.val = (true, vertices_394) then 14 else
  if p.val = (true, vertices_162) then 1 else
  if p.val = (true, vertices_290) then 2 else
  if p.val = (true, vertices_546) then 3 else
  if p.val = (true, vertices_56) then 4 else
  if p.val = (true, vertices_168) then 5 else
  if p.val = (true, vertices_296) then 6 else
  if p.val = (true, vertices_224) then 7 else
  if p.val = (true, vertices_608) then 8 else
  if p.val = (true, vertices_800) then 9 else
  0
cert_priority
cert_nodeAtPriority_7 0 262 1 162 2 290 546 56 168 296 224 608 800 141 89 647 394 285 837 713 369
cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 4 7 8 1 806 290 3
cert_row_4 1 0 4 5 6 8 738 162 2
cert_row_4 2 2 4 5 6 3 248 168 2
cert_row_2 3 2 6 7 0 394
cert_rows
cert_pivot_2 1 8 3 0
cert_heightProof 4
cert_coverFacet 0 398
cert_cover_5 0 3 0 1 2 6 134 398 2
cert_coverFacet 1 806
cert_cover_5 1 0 0 1 4 7 262 806 2
cert_coverFacet 2 426
cert_cover_5 2 3 0 2 4 6 394 426 2
cert_coverFacet 3 738
cert_cover_5 3 1 0 4 5 6 162 738 2
cert_coverFacet 4 248
cert_cover_5 4 2 2 3 4 5 56 248 3
cert_coverFacet 5 312
cert_cover_2 5 3 2 4 7 56 312 3
cert_coverFacet 6 864
cert_cover_2 6 5 4 7 8 352 864 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_239

end
end BundlePart27

section BundlePart28
/- Source: ProjectionCertificates/P0_240.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_240

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [115, 659, 803, 901, 425, 241, 598, 618, 220, 812, 588, 396, 660, 232, 19, 35, 515, 113, 145, 161, 289, 385, 641, 769, 82, 530, 98, 546, 578, 76, 140, 268, 524, 84, 148, 532, 580, 388, 644, 772, 104, 168, 296, 552, 200, 584, 392, 208, 656, 224, 800]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_115, vertices_659, vertices_803, vertices_901, vertices_425, vertices_241, vertices_598, vertices_618, vertices_220, vertices_812, vertices_588, vertices_396, vertices_660, vertices_232] (by decide +kernel)
  polygons := literalFinset [vertices_19, vertices_35, vertices_515, vertices_113, vertices_145, vertices_161, vertices_289, vertices_385, vertices_641, vertices_769, vertices_82, vertices_530, vertices_98, vertices_546, vertices_578, vertices_76, vertices_140, vertices_268, vertices_524, vertices_84, vertices_148, vertices_532, vertices_580, vertices_388, vertices_644, vertices_772, vertices_104, vertices_168, vertices_296, vertices_552, vertices_200, vertices_584, vertices_392, vertices_208, vertices_656, vertices_224, vertices_800] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_115), (false, vertices_659), (false, vertices_803), (false, vertices_901), (false, vertices_425), (false, vertices_241), (true, vertices_578), (true, vertices_76), (true, vertices_140), (true, vertices_268), (true, vertices_524), (true, vertices_84), (true, vertices_148), (true, vertices_532), (true, vertices_580), (true, vertices_104), (true, vertices_552), (true, vertices_200), (true, vertices_584)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 13 16 18 20 23 24 25 26 27
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_115) then 21 else
  if p.val = (false, vertices_659) then 14 else
  if p.val = (false, vertices_803) then 15 else
  if p.val = (false, vertices_901) then 17 else
  if p.val = (false, vertices_425) then 19 else
  if p.val = (false, vertices_241) then 22 else
  if p.val = (true, vertices_578) then 0 else
  if p.val = (true, vertices_76) then 1 else
  if p.val = (true, vertices_140) then 2 else
  if p.val = (true, vertices_268) then 3 else
  if p.val = (true, vertices_524) then 4 else
  if p.val = (true, vertices_84) then 5 else
  if p.val = (true, vertices_148) then 6 else
  if p.val = (true, vertices_532) then 7 else
  if p.val = (true, vertices_580) then 8 else
  if p.val = (true, vertices_104) then 9 else
  if p.val = (true, vertices_552) then 10 else
  if p.val = (true, vertices_200) then 11 else
  if p.val = (true, vertices_584) then 12 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_578), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_76), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_140), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_268), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_524), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_84), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_148), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_532), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_580), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_104), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_552), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_200), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_584), by decide +kernel⟩
  | 13 => Sum.inl 0
  | 14 => Sum.inr ⟨(false, vertices_659), by decide +kernel⟩
  | 15 => Sum.inr ⟨(false, vertices_803), by decide +kernel⟩
  | 16 => Sum.inl 1
  | 17 => Sum.inr ⟨(false, vertices_901), by decide +kernel⟩
  | 18 => Sum.inl 2
  | 19 => Sum.inr ⟨(false, vertices_425), by decide +kernel⟩
  | 20 => Sum.inl 3
  | 21 => Sum.inr ⟨(false, vertices_115), by decide +kernel⟩
  | 22 => Sum.inr ⟨(false, vertices_241), by decide +kernel⟩
  | 23 => Sum.inl 4
  | 24 => Sum.inl 5
  | 25 => Sum.inl 6
  | 26 => Sum.inl 7
  | 27 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 1 2 3 5 6 220 76 2
cert_row_4 1 0 1 5 8 3 598 578 1
cert_row_4 2 2 4 5 8 0 618 104 3
cert_row_4 3 2 4 7 8 1 812 296 3
cert_rows
cert_pivot_2 6 3 0 1
cert_heightProof 4
cert_coverFacet 0 598
cert_cover_5 0 1 0 1 3 5 82 598 1
cert_coverFacet 1 618
cert_cover_5 1 2 0 2 4 5 98 618 1
cert_coverFacet 2 220
cert_cover_5 2 0 1 2 3 5 76 220 2
cert_coverFacet 3 812
cert_cover_5 3 3 1 2 4 7 268 812 2
cert_coverFacet 4 588
cert_cover_2 4 2 1 5 8 76 588 3
cert_coverFacet 5 396
cert_cover_2 5 2 1 6 7 140 396 3
cert_coverFacet 6 660
cert_cover_2 6 3 1 6 8 148 660 3
cert_coverFacet 7 232
cert_cover_2 7 4 2 5 6 104 232 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_240

end
end BundlePart28

section BundlePart29
/- Source: ProjectionCertificates/P0_241.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_241

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [551, 659, 227, 309, 533, 409, 481, 714, 866, 668, 284, 844, 804, 456, 35, 131, 515, 21, 37, 517, 145, 273, 529, 225, 289, 385, 98, 546, 194, 578, 642, 28, 268, 524, 276, 532, 292, 548, 772, 152, 280, 200, 328, 584, 392, 648, 656, 352, 800, 448, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_551, vertices_659, vertices_227, vertices_309, vertices_533, vertices_409, vertices_481, vertices_714, vertices_866, vertices_668, vertices_284, vertices_844, vertices_804, vertices_456] (by decide +kernel)
  polygons := literalFinset [vertices_35, vertices_131, vertices_515, vertices_21, vertices_37, vertices_517, vertices_145, vertices_273, vertices_529, vertices_225, vertices_289, vertices_385, vertices_98, vertices_546, vertices_194, vertices_578, vertices_642, vertices_28, vertices_268, vertices_524, vertices_276, vertices_532, vertices_292, vertices_548, vertices_772, vertices_152, vertices_280, vertices_200, vertices_328, vertices_584, vertices_392, vertices_648, vertices_656, vertices_352, vertices_800, vertices_448, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_551), (false, vertices_659), (false, vertices_227), (false, vertices_309), (false, vertices_533), (false, vertices_409), (false, vertices_481), (true, vertices_578), (true, vertices_28), (true, vertices_268), (true, vertices_524), (true, vertices_772), (true, vertices_200), (true, vertices_328), (true, vertices_584), (true, vertices_648), (true, vertices_800), (true, vertices_832)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 12 15 17 19 20 23 24 25 26
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_551) then 13 else
  if p.val = (false, vertices_659) then 14 else
  if p.val = (false, vertices_227) then 21 else
  if p.val = (false, vertices_309) then 16 else
  if p.val = (false, vertices_533) then 11 else
  if p.val = (false, vertices_409) then 18 else
  if p.val = (false, vertices_481) then 22 else
  if p.val = (true, vertices_578) then 0 else
  if p.val = (true, vertices_28) then 1 else
  if p.val = (true, vertices_268) then 2 else
  if p.val = (true, vertices_524) then 3 else
  if p.val = (true, vertices_772) then 4 else
  if p.val = (true, vertices_200) then 5 else
  if p.val = (true, vertices_328) then 6 else
  if p.val = (true, vertices_584) then 7 else
  if p.val = (true, vertices_648) then 8 else
  if p.val = (true, vertices_800) then 9 else
  if p.val = (true, vertices_832) then 10 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_578), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_28), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_268), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_524), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_772), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_200), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_328), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_584), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_648), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_800), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_832), by decide +kernel⟩
  | 11 => Sum.inr ⟨(false, vertices_533), by decide +kernel⟩
  | 12 => Sum.inl 0
  | 13 => Sum.inr ⟨(false, vertices_551), by decide +kernel⟩
  | 14 => Sum.inr ⟨(false, vertices_659), by decide +kernel⟩
  | 15 => Sum.inl 1
  | 16 => Sum.inr ⟨(false, vertices_309), by decide +kernel⟩
  | 17 => Sum.inl 2
  | 18 => Sum.inr ⟨(false, vertices_409), by decide +kernel⟩
  | 19 => Sum.inl 3
  | 20 => Sum.inl 4
  | 21 => Sum.inr ⟨(false, vertices_227), by decide +kernel⟩
  | 22 => Sum.inr ⟨(false, vertices_481), by decide +kernel⟩
  | 23 => Sum.inl 5
  | 24 => Sum.inl 6
  | 25 => Sum.inl 7
  | 26 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 5 7 8 4 866 578 2
cert_row_4 1 2 5 6 8 0 714 200 3
cert_row_4 2 1 2 6 8 3 668 524 2
cert_row_4 3 2 5 7 8 1 844 328 3
cert_rows
cert_pivot_2 4 0 3 1
cert_heightProof 4
cert_coverFacet 0 714
cert_cover_5 0 1 0 2 5 6 194 714 1
cert_coverFacet 1 866
cert_cover_5 1 0 0 4 5 7 98 866 3
cert_coverFacet 2 668
cert_cover_5 2 2 1 2 3 6 28 668 3
cert_coverFacet 3 284
cert_cover_2 3 2 1 3 7 28 284 3
cert_coverFacet 4 844
cert_cover_5 4 3 1 2 5 7 268 844 2
cert_coverFacet 5 804
cert_cover_2 5 4 1 7 8 292 804 3
cert_coverFacet 6 456
cert_cover_2 6 5 2 6 7 200 456 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_241

end
end BundlePart29
-- Explicit facial frame witnesses.

-- Public target certificates; internal witness data stays private.
namespace Nonrational.TerminalVerification
open Papers.RationalityTen.ChirotopeDensity.FiniteProjection
open Nonrational.TerminalData
set_option maxRecDepth 100000
set_option maxHeartbeats 0

public theorem projection_0090 : Certifies 90 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_163.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0091 : Certifies 91 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_164.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0092 : Certifies 92 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_167.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0093 : Certifies 93 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_168.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0094 : Certifies 94 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_169.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0095 : Certifies 95 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_181.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0096 : Certifies 96 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_184.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0097 : Certifies 97 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_195.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0098 : Certifies 98 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_197.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0099 : Certifies 99 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_198.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0100 : Certifies 100 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_199.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0101 : Certifies 101 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_200.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0102 : Certifies 102 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_201.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0103 : Certifies 103 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_202.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0104 : Certifies 104 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_209.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0105 : Certifies 105 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_210.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0106 : Certifies 106 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_214.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0107 : Certifies 107 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_217.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0108 : Certifies 108 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_219.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0109 : Certifies 109 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_220.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0110 : Certifies 110 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_228.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0111 : Certifies 111 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_229.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0112 : Certifies 112 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_234.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0113 : Certifies 113 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_235.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0114 : Certifies 114 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_236.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0115 : Certifies 115 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_237.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0116 : Certifies 116 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_238.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0117 : Certifies 117 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_239.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0118 : Certifies 118 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_240.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0119 : Certifies 119 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_241.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem certified_B003 (j : Fin 30) :
    Certifies (90 + j.val) := by
  fin_cases j
  · exact projection_0090
  · exact projection_0091
  · exact projection_0092
  · exact projection_0093
  · exact projection_0094
  · exact projection_0095
  · exact projection_0096
  · exact projection_0097
  · exact projection_0098
  · exact projection_0099
  · exact projection_0100
  · exact projection_0101
  · exact projection_0102
  · exact projection_0103
  · exact projection_0104
  · exact projection_0105
  · exact projection_0106
  · exact projection_0107
  · exact projection_0108
  · exact projection_0109
  · exact projection_0110
  · exact projection_0111
  · exact projection_0112
  · exact projection_0113
  · exact projection_0114
  · exact projection_0115
  · exact projection_0116
  · exact projection_0117
  · exact projection_0118
  · exact projection_0119

end Nonrational.TerminalVerification
