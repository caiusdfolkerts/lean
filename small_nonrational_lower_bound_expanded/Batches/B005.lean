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
/- Source: ProjectionCertificates/R_m13e10q1_0086.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m13e10q1_0086

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [787, 163, 547, 387, 453, 569, 345, 233, 902, 682, 220, 668, 852, 35, 131, 259, 515, 25, 41, 73, 273, 529, 161, 545, 193, 321, 385, 162, 546, 386, 642, 770, 156, 84, 532, 196, 324, 388, 644, 772, 88, 536, 168, 552, 200, 648, 336, 784]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_787, vertices_163, vertices_547, vertices_387, vertices_453, vertices_569, vertices_345, vertices_233, vertices_902, vertices_682, vertices_220, vertices_668, vertices_852] (by decide +kernel)
  polygons := literalFinset [vertices_35, vertices_131, vertices_259, vertices_515, vertices_25, vertices_41, vertices_73, vertices_273, vertices_529, vertices_161, vertices_545, vertices_193, vertices_321, vertices_385, vertices_162, vertices_546, vertices_386, vertices_642, vertices_770, vertices_156, vertices_84, vertices_532, vertices_196, vertices_324, vertices_388, vertices_644, vertices_772, vertices_88, vertices_536, vertices_168, vertices_552, vertices_200, vertices_648, vertices_336, vertices_784] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_787), (false, vertices_163), (false, vertices_547), (false, vertices_387), (false, vertices_453), (false, vertices_569), (false, vertices_345), (false, vertices_233), (true, vertices_642), (true, vertices_156), (true, vertices_84), (true, vertices_532), (true, vertices_644), (true, vertices_772), (true, vertices_648)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 9 11 14 18 19 20 21 22 23
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_787) then 10 else
  if p.val = (false, vertices_163) then 0 else
  if p.val = (false, vertices_547) then 1 else
  if p.val = (false, vertices_387) then 2 else
  if p.val = (false, vertices_453) then 12 else
  if p.val = (false, vertices_569) then 15 else
  if p.val = (false, vertices_345) then 16 else
  if p.val = (false, vertices_233) then 17 else
  if p.val = (true, vertices_642) then 3 else
  if p.val = (true, vertices_156) then 13 else
  if p.val = (true, vertices_84) then 4 else
  if p.val = (true, vertices_532) then 5 else
  if p.val = (true, vertices_644) then 6 else
  if p.val = (true, vertices_772) then 7 else
  if p.val = (true, vertices_648) then 8 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_163), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_547), by decide +kernel⟩
  | 2 => Sum.inr ⟨(false, vertices_387), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_642), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_84), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_532), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_644), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_772), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_648), by decide +kernel⟩
  | 9 => Sum.inl 0
  | 10 => Sum.inr ⟨(false, vertices_787), by decide +kernel⟩
  | 11 => Sum.inl 1
  | 12 => Sum.inr ⟨(false, vertices_453), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_156), by decide +kernel⟩
  | 14 => Sum.inl 2
  | 15 => Sum.inr ⟨(false, vertices_569), by decide +kernel⟩
  | 16 => Sum.inr ⟨(false, vertices_345), by decide +kernel⟩
  | 17 => Sum.inr ⟨(false, vertices_233), by decide +kernel⟩
  | 18 => Sum.inl 3
  | 19 => Sum.inl 4
  | 20 => Sum.inl 5
  | 21 => Sum.inl 6
  | 22 => Sum.inl 7
  | 23 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 2 4 6 8 682 162 1
cert_row_2 1 1 2 3 6 156
cert_row_4 2 0 1 6 7 8 902 386 1
cert_row_4 3 1 3 5 7 8 852 84 3
cert_rows
cert_pivot_2 4 2 0 1
cert_heightProof 4
cert_coverFacet 0 902
cert_cover_5 0 2 0 1 6 7 386 902 1
cert_coverFacet 1 682
cert_cover_5 1 0 0 2 4 6 162 682 1
cert_coverFacet 2 220
cert_cover_5 2 1 1 2 3 5 156 220 3
cert_coverFacet 3 668
cert_cover_5 3 1 1 2 3 8 156 668 3
cert_coverFacet 4 852
cert_cover_5 4 3 1 3 5 7 84 852 3
cert_coveringFacets_3
cert_coveringProof_7
cert_certificate 4 5
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m13e10q1_0086

end
end BundlePart0

section BundlePart1
/- Source: ProjectionCertificates/R_m13e10q1_0101.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m13e10q1_0101

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [779, 659, 451, 341, 789, 241, 682, 394, 812, 628, 484, 424, 688, 131, 259, 515, 277, 81, 145, 529, 193, 321, 769, 138, 266, 522, 386, 642, 84, 532, 100, 292, 548, 324, 772, 168, 296, 552, 392, 776, 112, 176, 560, 656, 224, 416, 672, 448]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_779, vertices_659, vertices_451, vertices_341, vertices_789, vertices_241, vertices_682, vertices_394, vertices_812, vertices_628, vertices_484, vertices_424, vertices_688] (by decide +kernel)
  polygons := literalFinset [vertices_131, vertices_259, vertices_515, vertices_277, vertices_81, vertices_145, vertices_529, vertices_193, vertices_321, vertices_769, vertices_138, vertices_266, vertices_522, vertices_386, vertices_642, vertices_84, vertices_532, vertices_100, vertices_292, vertices_548, vertices_324, vertices_772, vertices_168, vertices_296, vertices_552, vertices_392, vertices_776, vertices_112, vertices_176, vertices_560, vertices_656, vertices_224, vertices_416, vertices_672, vertices_448] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_779), (false, vertices_659), (false, vertices_451), (false, vertices_341), (false, vertices_789), (false, vertices_241), (true, vertices_138), (true, vertices_100), (true, vertices_292), (true, vertices_548), (true, vertices_168), (true, vertices_296), (true, vertices_552), (true, vertices_392), (true, vertices_560), (true, vertices_416), (true, vertices_672)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 11 15 18 19 21 22 23 24 25
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_779) then 12 else
  if p.val = (false, vertices_659) then 13 else
  if p.val = (false, vertices_451) then 14 else
  if p.val = (false, vertices_341) then 16 else
  if p.val = (false, vertices_789) then 17 else
  if p.val = (false, vertices_241) then 20 else
  if p.val = (true, vertices_138) then 0 else
  if p.val = (true, vertices_100) then 1 else
  if p.val = (true, vertices_292) then 2 else
  if p.val = (true, vertices_548) then 3 else
  if p.val = (true, vertices_168) then 4 else
  if p.val = (true, vertices_296) then 5 else
  if p.val = (true, vertices_552) then 6 else
  if p.val = (true, vertices_392) then 7 else
  if p.val = (true, vertices_560) then 8 else
  if p.val = (true, vertices_416) then 9 else
  if p.val = (true, vertices_672) then 10 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_138), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_100), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_292), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_548), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_168), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_296), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_552), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_392), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_560), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_416), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_672), by decide +kernel⟩
  | 11 => Sum.inl 0
  | 12 => Sum.inr ⟨(false, vertices_779), by decide +kernel⟩
  | 13 => Sum.inr ⟨(false, vertices_659), by decide +kernel⟩
  | 14 => Sum.inr ⟨(false, vertices_451), by decide +kernel⟩
  | 15 => Sum.inl 1
  | 16 => Sum.inr ⟨(false, vertices_341), by decide +kernel⟩
  | 17 => Sum.inr ⟨(false, vertices_789), by decide +kernel⟩
  | 18 => Sum.inl 2
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
cert_row_4 0 0 2 4 6 8 682 138 2
cert_row_4 1 1 2 4 7 8 812 292 1
cert_row_4 2 1 3 4 5 8 628 84 2
cert_row_4 3 1 4 5 6 7 484 100 3
cert_rows
cert_pivot_2 0 2 3 1
cert_heightProof 4
cert_coverFacet 0 682
cert_cover_5 0 0 0 2 4 6 138 682 2
cert_coverFacet 1 394
cert_cover_2 1 2 0 6 7 138 394 3
cert_coverFacet 2 812
cert_cover_5 2 1 1 2 4 7 292 812 1
cert_coverFacet 3 628
cert_cover_5 3 2 1 3 4 5 84 628 2
cert_coverFacet 4 484
cert_cover_5 4 3 1 4 5 6 100 484 3
cert_coverFacet 5 424
cert_cover_2 5 4 2 6 7 168 424 3
cert_coverFacet 6 688
cert_cover_2 6 4 3 6 8 176 688 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m13e10q1_0101

end
end BundlePart1

section BundlePart2
/- Source: ProjectionCertificates/R_m13e10q1_0105.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m13e10q1_0105

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [659, 309, 405, 229, 713, 625, 842, 394, 650, 818, 402, 460, 868, 277, 37, 133, 49, 145, 529, 97, 193, 577, 641, 138, 266, 522, 146, 274, 530, 386, 642, 770, 100, 292, 196, 324, 388, 200, 328, 584, 392, 648, 304, 560, 400, 608, 800, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_659, vertices_309, vertices_405, vertices_229, vertices_713, vertices_625, vertices_842, vertices_394, vertices_650, vertices_818, vertices_402, vertices_460, vertices_868] (by decide +kernel)
  polygons := literalFinset [vertices_277, vertices_37, vertices_133, vertices_49, vertices_145, vertices_529, vertices_97, vertices_193, vertices_577, vertices_641, vertices_138, vertices_266, vertices_522, vertices_146, vertices_274, vertices_530, vertices_386, vertices_642, vertices_770, vertices_100, vertices_292, vertices_196, vertices_324, vertices_388, vertices_200, vertices_328, vertices_584, vertices_392, vertices_648, vertices_304, vertices_560, vertices_400, vertices_608, vertices_800, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_659), (false, vertices_309), (false, vertices_405), (false, vertices_229), (false, vertices_713), (false, vertices_625), (true, vertices_138), (true, vertices_266), (true, vertices_522), (true, vertices_274), (true, vertices_386), (true, vertices_770), (true, vertices_324), (true, vertices_328), (true, vertices_392), (true, vertices_800), (true, vertices_832)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 11 13 17 19 21 22 23 24 25
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_659) then 12 else
  if p.val = (false, vertices_309) then 14 else
  if p.val = (false, vertices_405) then 15 else
  if p.val = (false, vertices_229) then 16 else
  if p.val = (false, vertices_713) then 18 else
  if p.val = (false, vertices_625) then 20 else
  if p.val = (true, vertices_138) then 0 else
  if p.val = (true, vertices_266) then 1 else
  if p.val = (true, vertices_522) then 2 else
  if p.val = (true, vertices_274) then 3 else
  if p.val = (true, vertices_386) then 4 else
  if p.val = (true, vertices_770) then 5 else
  if p.val = (true, vertices_324) then 6 else
  if p.val = (true, vertices_328) then 7 else
  if p.val = (true, vertices_392) then 8 else
  if p.val = (true, vertices_800) then 9 else
  if p.val = (true, vertices_832) then 10 else
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
  | 7 => Sum.inr ⟨(true, vertices_328), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_392), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_800), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_832), by decide +kernel⟩
  | 11 => Sum.inl 0
  | 12 => Sum.inr ⟨(false, vertices_659), by decide +kernel⟩
  | 13 => Sum.inl 1
  | 14 => Sum.inr ⟨(false, vertices_309), by decide +kernel⟩
  | 15 => Sum.inr ⟨(false, vertices_405), by decide +kernel⟩
  | 16 => Sum.inr ⟨(false, vertices_229), by decide +kernel⟩
  | 17 => Sum.inl 2
  | 18 => Sum.inr ⟨(false, vertices_713), by decide +kernel⟩
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
cert_row_4 0 0 3 4 7 8 818 274 2
cert_row_4 1 0 2 5 7 8 842 266 2
cert_row_4 2 1 2 5 6 7 460 196 1
cert_row_4 3 1 4 5 7 8 868 100 3
cert_rows
cert_pivot_2 3 0 2 1
cert_heightProof 4
cert_coverFacet 0 842
cert_cover_5 0 1 0 2 5 7 266 842 2
cert_coverFacet 1 394
cert_cover_2 1 2 0 6 7 138 394 3
cert_coverFacet 2 650
cert_cover_2 2 2 0 6 8 138 650 3
cert_coverFacet 3 818
cert_cover_5 3 0 0 3 4 7 274 818 2
cert_coverFacet 4 402
cert_cover_2 4 3 0 6 7 146 402 3
cert_coverFacet 5 460
cert_cover_5 5 2 1 2 5 6 196 460 1
cert_coverFacet 6 868
cert_cover_5 6 3 1 4 5 7 100 868 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m13e10q1_0105

end
end BundlePart2

section BundlePart3
/- Source: ProjectionCertificates/R_m13e10q1_0126.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m13e10q1_0126

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [611, 397, 789, 677, 233, 841, 662, 362, 426, 850, 402, 674, 404, 133, 261, 517, 73, 137, 265, 97, 161, 545, 577, 769, 298, 146, 274, 530, 98, 162, 546, 322, 578, 386, 642, 148, 276, 532, 388, 644, 104, 168, 328, 392, 400, 784, 672, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_611, vertices_397, vertices_789, vertices_677, vertices_233, vertices_841, vertices_662, vertices_362, vertices_426, vertices_850, vertices_402, vertices_674, vertices_404] (by decide +kernel)
  polygons := literalFinset [vertices_133, vertices_261, vertices_517, vertices_73, vertices_137, vertices_265, vertices_97, vertices_161, vertices_545, vertices_577, vertices_769, vertices_298, vertices_146, vertices_274, vertices_530, vertices_98, vertices_162, vertices_546, vertices_322, vertices_578, vertices_386, vertices_642, vertices_148, vertices_276, vertices_532, vertices_388, vertices_644, vertices_104, vertices_168, vertices_328, vertices_392, vertices_400, vertices_784, vertices_672, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_611), (false, vertices_397), (false, vertices_789), (false, vertices_677), (false, vertices_233), (false, vertices_841), (true, vertices_298), (true, vertices_146), (true, vertices_274), (true, vertices_530), (true, vertices_162), (true, vertices_322), (true, vertices_386), (true, vertices_642), (true, vertices_148), (true, vertices_400)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 9 12 16 19 20 21 22 23 24
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_611) then 10 else
  if p.val = (false, vertices_397) then 13 else
  if p.val = (false, vertices_789) then 14 else
  if p.val = (false, vertices_677) then 15 else
  if p.val = (false, vertices_233) then 17 else
  if p.val = (false, vertices_841) then 18 else
  if p.val = (true, vertices_298) then 11 else
  if p.val = (true, vertices_146) then 0 else
  if p.val = (true, vertices_274) then 1 else
  if p.val = (true, vertices_530) then 2 else
  if p.val = (true, vertices_162) then 3 else
  if p.val = (true, vertices_322) then 4 else
  if p.val = (true, vertices_386) then 5 else
  if p.val = (true, vertices_642) then 6 else
  if p.val = (true, vertices_148) then 7 else
  if p.val = (true, vertices_400) then 8 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_146), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_274), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_530), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_162), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_322), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_386), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_642), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_148), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_400), by decide +kernel⟩
  | 9 => Sum.inl 0
  | 10 => Sum.inr ⟨(false, vertices_611), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_298), by decide +kernel⟩
  | 12 => Sum.inl 1
  | 13 => Sum.inr ⟨(false, vertices_397), by decide +kernel⟩
  | 14 => Sum.inr ⟨(false, vertices_789), by decide +kernel⟩
  | 15 => Sum.inr ⟨(false, vertices_677), by decide +kernel⟩
  | 16 => Sum.inl 2
  | 17 => Sum.inr ⟨(false, vertices_233), by decide +kernel⟩
  | 18 => Sum.inr ⟨(false, vertices_841), by decide +kernel⟩
  | 19 => Sum.inl 3
  | 20 => Sum.inl 4
  | 21 => Sum.inl 5
  | 22 => Sum.inl 6
  | 23 => Sum.inl 7
  | 24 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 2 4 7 298
cert_row_4 1 0 1 3 6 8 662 146 1
cert_row_4 2 0 3 5 7 8 850 274 2
cert_rows_3
cert_pivot_3 1 2 0
cert_heightProof 3
cert_coverFacet 0 662
cert_cover_5 0 1 0 1 3 6 146 662 1
cert_coverFacet 1 362
cert_cover_5 1 0 0 2 4 5 298 362 3
cert_coverFacet 2 426
cert_cover_5 2 0 0 2 4 6 298 426 3
cert_coverFacet 3 850
cert_cover_5 3 2 0 3 5 7 274 850 2
cert_coverFacet 4 402
cert_cover_2 4 3 0 6 7 146 402 3
cert_coverFacet 5 674
cert_cover_2 5 4 0 6 8 162 674 3
cert_coverFacet 6 404
cert_cover_2 6 3 1 6 7 148 404 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 3 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m13e10q1_0126

end
end BundlePart3

section BundlePart4
/- Source: ProjectionCertificates/R_m13e10q1_0141.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m13e10q1_0141

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [327, 171, 299, 195, 781, 597, 713, 370, 738, 820, 340, 936, 624, 43, 67, 131, 259, 69, 261, 517, 137, 265, 521, 193, 577, 98, 162, 290, 194, 322, 84, 276, 532, 324, 772, 168, 296, 648, 776, 112, 304, 560, 336, 592, 608, 672, 800, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_327, vertices_171, vertices_299, vertices_195, vertices_781, vertices_597, vertices_713, vertices_370, vertices_738, vertices_820, vertices_340, vertices_936, vertices_624] (by decide +kernel)
  polygons := literalFinset [vertices_43, vertices_67, vertices_131, vertices_259, vertices_69, vertices_261, vertices_517, vertices_137, vertices_265, vertices_521, vertices_193, vertices_577, vertices_98, vertices_162, vertices_290, vertices_194, vertices_322, vertices_84, vertices_276, vertices_532, vertices_324, vertices_772, vertices_168, vertices_296, vertices_648, vertices_776, vertices_112, vertices_304, vertices_560, vertices_336, vertices_592, vertices_608, vertices_672, vertices_800, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_327), (false, vertices_171), (false, vertices_299), (false, vertices_195), (false, vertices_781), (false, vertices_597), (false, vertices_713), (true, vertices_98), (true, vertices_276), (true, vertices_112), (true, vertices_304), (true, vertices_560), (true, vertices_336), (true, vertices_608), (true, vertices_672), (true, vertices_800)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 10 14 17 19 20 21 22 23 24
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_327) then 11 else
  if p.val = (false, vertices_171) then 12 else
  if p.val = (false, vertices_299) then 13 else
  if p.val = (false, vertices_195) then 0 else
  if p.val = (false, vertices_781) then 15 else
  if p.val = (false, vertices_597) then 16 else
  if p.val = (false, vertices_713) then 18 else
  if p.val = (true, vertices_98) then 1 else
  if p.val = (true, vertices_276) then 2 else
  if p.val = (true, vertices_112) then 3 else
  if p.val = (true, vertices_304) then 4 else
  if p.val = (true, vertices_560) then 5 else
  if p.val = (true, vertices_336) then 6 else
  if p.val = (true, vertices_608) then 7 else
  if p.val = (true, vertices_672) then 8 else
  if p.val = (true, vertices_800) then 9 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_195), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_98), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_276), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_112), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_304), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_560), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_336), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_608), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_672), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_800), by decide +kernel⟩
  | 10 => Sum.inl 0
  | 11 => Sum.inr ⟨(false, vertices_327), by decide +kernel⟩
  | 12 => Sum.inr ⟨(false, vertices_171), by decide +kernel⟩
  | 13 => Sum.inr ⟨(false, vertices_299), by decide +kernel⟩
  | 14 => Sum.inl 1
  | 15 => Sum.inr ⟨(false, vertices_781), by decide +kernel⟩
  | 16 => Sum.inr ⟨(false, vertices_597), by decide +kernel⟩
  | 17 => Sum.inl 2
  | 18 => Sum.inr ⟨(false, vertices_713), by decide +kernel⟩
  | 19 => Sum.inl 3
  | 20 => Sum.inl 4
  | 21 => Sum.inl 5
  | 22 => Sum.inl 6
  | 23 => Sum.inl 7
  | 24 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 1 3 4 7 8 820 276 2
cert_row_4 1 0 3 4 5 7 370 98 1
cert_row_4 2 0 4 5 6 8 738 98 3
cert_row_4 3 2 4 6 7 8 936 168 3
cert_rows
cert_pivot_2 1 3 0 2
cert_heightProof 4
cert_coverFacet 0 370
cert_cover_5 0 1 0 3 4 5 98 370 1
cert_coverFacet 1 738
cert_cover_5 1 2 0 4 5 6 98 738 3
cert_coverFacet 2 820
cert_cover_5 2 0 1 3 4 7 276 820 2
cert_coverFacet 3 340
cert_cover_2 3 3 1 5 7 84 340 3
cert_coverFacet 4 936
cert_cover_5 4 3 2 4 6 7 168 936 3
cert_coverFacet 5 624
cert_cover_2 5 4 3 5 8 112 624 3
cert_coveringFacets
cert_coveringProof_6
cert_certificate 4 6
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m13e10q1_0141

end
end BundlePart4

section BundlePart5
/- Source: ProjectionCertificates/R_m13e10q1_0151.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m13e10q1_0151

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [355, 653, 789, 421, 233, 841, 662, 618, 682, 850, 402, 418, 404, 133, 261, 517, 73, 137, 521, 97, 161, 289, 321, 769, 554, 146, 274, 530, 98, 162, 290, 322, 578, 386, 642, 148, 276, 532, 388, 644, 104, 168, 584, 648, 400, 784, 416, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_355, vertices_653, vertices_789, vertices_421, vertices_233, vertices_841, vertices_662, vertices_618, vertices_682, vertices_850, vertices_402, vertices_418, vertices_404] (by decide +kernel)
  polygons := literalFinset [vertices_133, vertices_261, vertices_517, vertices_73, vertices_137, vertices_521, vertices_97, vertices_161, vertices_289, vertices_321, vertices_769, vertices_554, vertices_146, vertices_274, vertices_530, vertices_98, vertices_162, vertices_290, vertices_322, vertices_578, vertices_386, vertices_642, vertices_148, vertices_276, vertices_532, vertices_388, vertices_644, vertices_104, vertices_168, vertices_584, vertices_648, vertices_400, vertices_784, vertices_416, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_355), (false, vertices_653), (false, vertices_789), (false, vertices_421), (false, vertices_233), (false, vertices_841), (true, vertices_554), (true, vertices_146), (true, vertices_274), (true, vertices_530), (true, vertices_162), (true, vertices_578), (true, vertices_386), (true, vertices_642), (true, vertices_148), (true, vertices_400)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 9 12 16 19 20 21 22 23 24
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_355) then 10 else
  if p.val = (false, vertices_653) then 13 else
  if p.val = (false, vertices_789) then 14 else
  if p.val = (false, vertices_421) then 15 else
  if p.val = (false, vertices_233) then 17 else
  if p.val = (false, vertices_841) then 18 else
  if p.val = (true, vertices_554) then 11 else
  if p.val = (true, vertices_146) then 0 else
  if p.val = (true, vertices_274) then 1 else
  if p.val = (true, vertices_530) then 2 else
  if p.val = (true, vertices_162) then 3 else
  if p.val = (true, vertices_578) then 4 else
  if p.val = (true, vertices_386) then 5 else
  if p.val = (true, vertices_642) then 6 else
  if p.val = (true, vertices_148) then 7 else
  if p.val = (true, vertices_400) then 8 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_146), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_274), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_530), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_162), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_578), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_386), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_642), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_148), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_400), by decide +kernel⟩
  | 9 => Sum.inl 0
  | 10 => Sum.inr ⟨(false, vertices_355), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_554), by decide +kernel⟩
  | 12 => Sum.inl 1
  | 13 => Sum.inr ⟨(false, vertices_653), by decide +kernel⟩
  | 14 => Sum.inr ⟨(false, vertices_789), by decide +kernel⟩
  | 15 => Sum.inr ⟨(false, vertices_421), by decide +kernel⟩
  | 16 => Sum.inl 2
  | 17 => Sum.inr ⟨(false, vertices_233), by decide +kernel⟩
  | 18 => Sum.inr ⟨(false, vertices_841), by decide +kernel⟩
  | 19 => Sum.inl 3
  | 20 => Sum.inl 4
  | 21 => Sum.inl 5
  | 22 => Sum.inl 6
  | 23 => Sum.inl 7
  | 24 => Sum.inl 8
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
cert_coverFacet 3 850
cert_cover_5 3 2 0 3 5 7 274 850 2
cert_coverFacet 4 402
cert_cover_2 4 3 0 6 7 146 402 3
cert_coverFacet 5 418
cert_cover_2 5 4 0 6 7 162 418 3
cert_coverFacet 6 404
cert_cover_2 6 3 1 6 7 148 404 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 3 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m13e10q1_0151

end
end BundlePart5

section BundlePart6
/- Source: ProjectionCertificates/R_m13e11q1_0000.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m13e11q1_0000

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [551, 539, 403, 163, 285, 589, 421, 690, 364, 612, 472, 728, 992, 19, 35, 131, 515, 13, 37, 261, 517, 25, 521, 273, 161, 385, 146, 530, 162, 546, 76, 268, 100, 292, 548, 580, 216, 280, 536, 328, 584, 400, 656, 352, 608, 416, 672, 448, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_551, vertices_539, vertices_403, vertices_163, vertices_285, vertices_589, vertices_421, vertices_690, vertices_364, vertices_612, vertices_472, vertices_728, vertices_992] (by decide +kernel)
  polygons := literalFinset [vertices_19, vertices_35, vertices_131, vertices_515, vertices_13, vertices_37, vertices_261, vertices_517, vertices_25, vertices_521, vertices_273, vertices_161, vertices_385, vertices_146, vertices_530, vertices_162, vertices_546, vertices_76, vertices_268, vertices_100, vertices_292, vertices_548, vertices_580, vertices_216, vertices_280, vertices_536, vertices_328, vertices_584, vertices_400, vertices_656, vertices_352, vertices_608, vertices_416, vertices_672, vertices_448, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_551), (false, vertices_539), (false, vertices_403), (false, vertices_163), (false, vertices_285), (false, vertices_589), (false, vertices_421), (true, vertices_100), (true, vertices_216), (true, vertices_328), (true, vertices_656), (true, vertices_352), (true, vertices_608), (true, vertices_672), (true, vertices_448), (true, vertices_704)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 9 13 17 19 20 21 22 23 24
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_551) then 10 else
  if p.val = (false, vertices_539) then 11 else
  if p.val = (false, vertices_403) then 12 else
  if p.val = (false, vertices_163) then 0 else
  if p.val = (false, vertices_285) then 14 else
  if p.val = (false, vertices_589) then 15 else
  if p.val = (false, vertices_421) then 16 else
  if p.val = (true, vertices_100) then 1 else
  if p.val = (true, vertices_216) then 18 else
  if p.val = (true, vertices_328) then 2 else
  if p.val = (true, vertices_656) then 3 else
  if p.val = (true, vertices_352) then 4 else
  if p.val = (true, vertices_608) then 5 else
  if p.val = (true, vertices_672) then 6 else
  if p.val = (true, vertices_448) then 7 else
  if p.val = (true, vertices_704) then 8 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_163), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_100), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_328), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_656), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_352), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_608), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_672), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_448), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_704), by decide +kernel⟩
  | 9 => Sum.inl 0
  | 10 => Sum.inr ⟨(false, vertices_551), by decide +kernel⟩
  | 11 => Sum.inr ⟨(false, vertices_539), by decide +kernel⟩
  | 12 => Sum.inr ⟨(false, vertices_403), by decide +kernel⟩
  | 13 => Sum.inl 1
  | 14 => Sum.inr ⟨(false, vertices_285), by decide +kernel⟩
  | 15 => Sum.inr ⟨(false, vertices_589), by decide +kernel⟩
  | 16 => Sum.inr ⟨(false, vertices_421), by decide +kernel⟩
  | 17 => Sum.inl 2
  | 18 => Sum.inr ⟨(true, vertices_216), by decide +kernel⟩
  | 19 => Sum.inl 3
  | 20 => Sum.inl 4
  | 21 => Sum.inl 5
  | 22 => Sum.inl 6
  | 23 => Sum.inl 7
  | 24 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 3 4 6 8 690 146 2
cert_row_2 1 2 3 5 6 216
cert_row_4 2 1 2 4 5 7 364 76 2
cert_row_4 3 4 5 6 7 8 992 352 2
cert_rows
cert_pivot_2 0 3 1 4
cert_heightProof 4
cert_coverFacet 0 690
cert_cover_5 0 0 0 3 4 6 146 690 2
cert_coverFacet 1 364
cert_cover_5 1 2 1 2 4 5 76 364 2
cert_coverFacet 2 612
cert_cover_2 2 4 1 5 8 100 612 3
cert_coverFacet 3 472
cert_cover_5 3 1 2 3 5 7 216 472 3
cert_coverFacet 4 728
cert_cover_5 4 1 2 3 5 8 216 728 3
cert_coverFacet 5 992
cert_cover_5 5 3 4 5 6 7 352 992 2
cert_coveringFacets
cert_coveringProof_6
cert_certificate 4 6
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m13e11q1_0000

end
end BundlePart6

section BundlePart7
/- Source: ProjectionCertificates/R_m13e11q1_0001.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m13e11q1_0001

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [143, 299, 51, 211, 781, 709, 817, 593, 186, 236, 364, 852, 496, 11, 19, 35, 131, 13, 133, 517, 265, 49, 81, 529, 289, 193, 577, 769, 42, 138, 50, 146, 108, 140, 268, 196, 324, 580, 772, 168, 296, 176, 304, 208, 336, 592, 784, 224, 352]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_143, vertices_299, vertices_51, vertices_211, vertices_781, vertices_709, vertices_817, vertices_593, vertices_186, vertices_236, vertices_364, vertices_852, vertices_496] (by decide +kernel)
  polygons := literalFinset [vertices_11, vertices_19, vertices_35, vertices_131, vertices_13, vertices_133, vertices_517, vertices_265, vertices_49, vertices_81, vertices_529, vertices_289, vertices_193, vertices_577, vertices_769, vertices_42, vertices_138, vertices_50, vertices_146, vertices_108, vertices_140, vertices_268, vertices_196, vertices_324, vertices_580, vertices_772, vertices_168, vertices_296, vertices_176, vertices_304, vertices_208, vertices_336, vertices_592, vertices_784, vertices_224, vertices_352] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_143), (false, vertices_299), (false, vertices_51), (false, vertices_211), (false, vertices_781), (false, vertices_709), (false, vertices_817), (false, vertices_593), (true, vertices_108), (true, vertices_324), (true, vertices_168), (true, vertices_176), (true, vertices_336), (true, vertices_224), (true, vertices_352)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 8 12 16 17 19 20 21 22 23
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_143) then 9 else
  if p.val = (false, vertices_299) then 10 else
  if p.val = (false, vertices_51) then 0 else
  if p.val = (false, vertices_211) then 11 else
  if p.val = (false, vertices_781) then 13 else
  if p.val = (false, vertices_709) then 14 else
  if p.val = (false, vertices_817) then 18 else
  if p.val = (false, vertices_593) then 1 else
  if p.val = (true, vertices_108) then 15 else
  if p.val = (true, vertices_324) then 2 else
  if p.val = (true, vertices_168) then 3 else
  if p.val = (true, vertices_176) then 4 else
  if p.val = (true, vertices_336) then 5 else
  if p.val = (true, vertices_224) then 6 else
  if p.val = (true, vertices_352) then 7 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_51), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_593), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_324), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_168), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_176), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_336), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_224), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_352), by decide +kernel⟩
  | 8 => Sum.inl 0
  | 9 => Sum.inr ⟨(false, vertices_143), by decide +kernel⟩
  | 10 => Sum.inr ⟨(false, vertices_299), by decide +kernel⟩
  | 11 => Sum.inr ⟨(false, vertices_211), by decide +kernel⟩
  | 12 => Sum.inl 1
  | 13 => Sum.inr ⟨(false, vertices_781), by decide +kernel⟩
  | 14 => Sum.inr ⟨(false, vertices_709), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_108), by decide +kernel⟩
  | 16 => Sum.inl 2
  | 17 => Sum.inl 3
  | 18 => Sum.inr ⟨(false, vertices_817), by decide +kernel⟩
  | 19 => Sum.inl 4
  | 20 => Sum.inl 5
  | 21 => Sum.inl 6
  | 22 => Sum.inl 7
  | 23 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 2 3 4 6 186 42 2
cert_row_2 1 1 2 4 5 108
cert_row_4 2 1 3 5 7 8 852 324 1
cert_row_4 3 3 4 5 6 7 496 176 2
cert_rows
cert_pivot_2 0 2 1 3
cert_heightProof 4
cert_coverFacet 0 186
cert_cover_5 0 0 0 2 3 4 42 186 2
cert_coverFacet 1 236
cert_cover_5 1 1 1 2 4 6 108 236 3
cert_coverFacet 2 364
cert_cover_5 2 1 1 2 4 7 108 364 3
cert_coverFacet 3 852
cert_cover_5 3 2 1 3 5 7 324 852 1
cert_coverFacet 4 496
cert_cover_5 4 3 3 4 5 6 176 496 2
cert_coveringFacets_3
cert_coveringProof_7
cert_certificate 4 5
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m13e11q1_0001

end
end BundlePart7

section BundlePart8
/- Source: ProjectionCertificates/R_m13e11q1_0002.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m13e11q1_0002

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [555, 51, 339, 899, 61, 653, 405, 118, 866, 236, 212, 744, 976, 19, 35, 259, 515, 13, 21, 133, 41, 521, 49, 273, 385, 641, 50, 82, 98, 546, 322, 770, 44, 140, 52, 84, 148, 100, 196, 232, 552, 648, 208, 336, 400, 608, 704, 832, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_555, vertices_51, vertices_339, vertices_899, vertices_61, vertices_653, vertices_405, vertices_118, vertices_866, vertices_236, vertices_212, vertices_744, vertices_976] (by decide +kernel)
  polygons := literalFinset [vertices_19, vertices_35, vertices_259, vertices_515, vertices_13, vertices_21, vertices_133, vertices_41, vertices_521, vertices_49, vertices_273, vertices_385, vertices_641, vertices_50, vertices_82, vertices_98, vertices_546, vertices_322, vertices_770, vertices_44, vertices_140, vertices_52, vertices_84, vertices_148, vertices_100, vertices_196, vertices_232, vertices_552, vertices_648, vertices_208, vertices_336, vertices_400, vertices_608, vertices_704, vertices_832, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_555), (false, vertices_51), (false, vertices_339), (false, vertices_899), (false, vertices_61), (false, vertices_653), (false, vertices_405), (true, vertices_98), (true, vertices_84), (true, vertices_100), (true, vertices_196), (true, vertices_232), (true, vertices_208), (true, vertices_608), (true, vertices_704), (true, vertices_832)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 9 13 17 19 20 21 22 23 24
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_555) then 10 else
  if p.val = (false, vertices_51) then 0 else
  if p.val = (false, vertices_339) then 11 else
  if p.val = (false, vertices_899) then 12 else
  if p.val = (false, vertices_61) then 14 else
  if p.val = (false, vertices_653) then 15 else
  if p.val = (false, vertices_405) then 16 else
  if p.val = (true, vertices_98) then 1 else
  if p.val = (true, vertices_84) then 2 else
  if p.val = (true, vertices_100) then 3 else
  if p.val = (true, vertices_196) then 4 else
  if p.val = (true, vertices_232) then 18 else
  if p.val = (true, vertices_208) then 5 else
  if p.val = (true, vertices_608) then 6 else
  if p.val = (true, vertices_704) then 7 else
  if p.val = (true, vertices_832) then 8 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_51), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_98), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_84), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_100), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_196), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_208), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_608), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_704), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_832), by decide +kernel⟩
  | 9 => Sum.inl 0
  | 10 => Sum.inr ⟨(false, vertices_555), by decide +kernel⟩
  | 11 => Sum.inr ⟨(false, vertices_339), by decide +kernel⟩
  | 12 => Sum.inr ⟨(false, vertices_899), by decide +kernel⟩
  | 13 => Sum.inl 1
  | 14 => Sum.inr ⟨(false, vertices_61), by decide +kernel⟩
  | 15 => Sum.inr ⟨(false, vertices_653), by decide +kernel⟩
  | 16 => Sum.inr ⟨(false, vertices_405), by decide +kernel⟩
  | 17 => Sum.inl 2
  | 18 => Sum.inr ⟨(true, vertices_232), by decide +kernel⟩
  | 19 => Sum.inl 3
  | 20 => Sum.inl 4
  | 21 => Sum.inl 5
  | 22 => Sum.inl 6
  | 23 => Sum.inl 7
  | 24 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 2 4 5 6 232
cert_row_4 1 0 1 3 4 5 118 50 1
cert_row_4 2 0 4 5 7 8 866 98 3
cert_row_4 3 3 5 6 7 8 976 208 3
cert_rows
cert_pivot_2 2 1 0 3
cert_heightProof 4
cert_coverFacet 0 118
cert_cover_5 0 1 0 1 3 4 50 118 1
cert_coverFacet 1 866
cert_cover_5 1 2 0 4 5 7 98 866 3
cert_coverFacet 2 236
cert_cover_5 2 0 1 2 4 5 44 236 3
cert_coverFacet 3 212
cert_cover_2 3 3 1 5 6 84 212 3
cert_coverFacet 4 744
cert_cover_5 4 0 2 4 5 8 232 744 3
cert_coverFacet 5 976
cert_cover_5 5 3 3 5 6 7 208 976 3
cert_coveringFacets
cert_coveringProof_6
cert_certificate 4 6
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m13e11q1_0002

end
end BundlePart8

section BundlePart9
/- Source: ProjectionCertificates/R_m13e11q1_0003.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m13e11q1_0003

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [787, 541, 205, 901, 345, 481, 558, 122, 538, 370, 930, 108, 740, 13, 133, 517, 25, 73, 273, 529, 193, 321, 385, 769, 26, 42, 522, 114, 274, 530, 290, 546, 770, 44, 76, 524, 100, 548, 196, 644, 88, 536, 104, 336, 224, 352, 416, 672, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_787, vertices_541, vertices_205, vertices_901, vertices_345, vertices_481, vertices_558, vertices_122, vertices_538, vertices_370, vertices_930, vertices_108, vertices_740] (by decide +kernel)
  polygons := literalFinset [vertices_13, vertices_133, vertices_517, vertices_25, vertices_73, vertices_273, vertices_529, vertices_193, vertices_321, vertices_385, vertices_769, vertices_26, vertices_42, vertices_522, vertices_114, vertices_274, vertices_530, vertices_290, vertices_546, vertices_770, vertices_44, vertices_76, vertices_524, vertices_100, vertices_548, vertices_196, vertices_644, vertices_88, vertices_536, vertices_104, vertices_336, vertices_224, vertices_352, vertices_416, vertices_672, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_787), (false, vertices_541), (false, vertices_205), (false, vertices_901), (false, vertices_345), (false, vertices_481), (true, vertices_26), (true, vertices_42), (true, vertices_522), (true, vertices_114), (true, vertices_290), (true, vertices_546), (true, vertices_44), (true, vertices_100), (true, vertices_548), (true, vertices_104), (true, vertices_672)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 10 13 17 19 20 22 23 24 25
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_787) then 11 else
  if p.val = (false, vertices_541) then 14 else
  if p.val = (false, vertices_205) then 15 else
  if p.val = (false, vertices_901) then 16 else
  if p.val = (false, vertices_345) then 18 else
  if p.val = (false, vertices_481) then 21 else
  if p.val = (true, vertices_26) then 0 else
  if p.val = (true, vertices_42) then 1 else
  if p.val = (true, vertices_522) then 2 else
  if p.val = (true, vertices_114) then 12 else
  if p.val = (true, vertices_290) then 3 else
  if p.val = (true, vertices_546) then 4 else
  if p.val = (true, vertices_44) then 5 else
  if p.val = (true, vertices_100) then 6 else
  if p.val = (true, vertices_548) then 7 else
  if p.val = (true, vertices_104) then 8 else
  if p.val = (true, vertices_672) then 9 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_26), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_42), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_522), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_290), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_546), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_44), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_100), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_548), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_104), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_672), by decide +kernel⟩
  | 10 => Sum.inl 0
  | 11 => Sum.inr ⟨(false, vertices_787), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_114), by decide +kernel⟩
  | 13 => Sum.inl 1
  | 14 => Sum.inr ⟨(false, vertices_541), by decide +kernel⟩
  | 15 => Sum.inr ⟨(false, vertices_205), by decide +kernel⟩
  | 16 => Sum.inr ⟨(false, vertices_901), by decide +kernel⟩
  | 17 => Sum.inl 2
  | 18 => Sum.inr ⟨(false, vertices_345), by decide +kernel⟩
  | 19 => Sum.inl 3
  | 20 => Sum.inl 4
  | 21 => Sum.inr ⟨(false, vertices_481), by decide +kernel⟩
  | 22 => Sum.inl 5
  | 23 => Sum.inl 6
  | 24 => Sum.inl 7
  | 25 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 3 4 5 114
cert_row_4 1 0 1 2 4 8 558 42 1
cert_row_4 2 0 4 6 7 8 930 290 2
cert_row_4 3 1 4 5 6 8 740 100 3
cert_rows
cert_pivot_2 3 2 0 1
cert_heightProof 4
cert_coverFacet 0 558
cert_cover_5 0 1 0 1 2 4 42 558 1
cert_coverFacet 1 122
cert_cover_5 1 0 0 2 3 4 26 122 3
cert_coverFacet 2 538
cert_cover_2 2 2 0 3 8 26 538 3
cert_coverFacet 3 370
cert_cover_5 3 0 0 3 4 7 114 370 3
cert_coverFacet 4 930
cert_cover_5 4 2 0 4 6 7 290 930 2
cert_coverFacet 5 108
cert_cover_2 5 2 1 4 5 44 108 3
cert_coverFacet 6 740
cert_cover_5 6 3 1 4 5 6 100 740 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m13e11q1_0003

end
end BundlePart9

section BundlePart10
/- Source: ProjectionCertificates/R_m13e11q1_0004.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m13e11q1_0004

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [155, 299, 339, 357, 233, 721, 654, 782, 658, 786, 428, 852, 740, 11, 19, 259, 41, 137, 81, 145, 97, 289, 193, 321, 526, 138, 266, 146, 274, 530, 642, 770, 140, 268, 100, 164, 292, 324, 580, 644, 772, 168, 296, 336, 592, 656, 784, 224, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_155, vertices_299, vertices_339, vertices_357, vertices_233, vertices_721, vertices_654, vertices_782, vertices_658, vertices_786, vertices_428, vertices_852, vertices_740] (by decide +kernel)
  polygons := literalFinset [vertices_11, vertices_19, vertices_259, vertices_41, vertices_137, vertices_81, vertices_145, vertices_97, vertices_289, vertices_193, vertices_321, vertices_526, vertices_138, vertices_266, vertices_146, vertices_274, vertices_530, vertices_642, vertices_770, vertices_140, vertices_268, vertices_100, vertices_164, vertices_292, vertices_324, vertices_580, vertices_644, vertices_772, vertices_168, vertices_296, vertices_336, vertices_592, vertices_656, vertices_784, vertices_224, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_155), (false, vertices_299), (false, vertices_339), (false, vertices_357), (false, vertices_233), (false, vertices_721), (true, vertices_526), (true, vertices_530), (true, vertices_642), (true, vertices_770), (true, vertices_140), (true, vertices_268), (true, vertices_164), (true, vertices_580), (true, vertices_644), (true, vertices_772), (true, vertices_784)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 13 10 17 19 21 22 23 24 25
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_155) then 14 else
  if p.val = (false, vertices_299) then 15 else
  if p.val = (false, vertices_339) then 16 else
  if p.val = (false, vertices_357) then 11 else
  if p.val = (false, vertices_233) then 18 else
  if p.val = (false, vertices_721) then 20 else
  if p.val = (true, vertices_526) then 12 else
  if p.val = (true, vertices_530) then 0 else
  if p.val = (true, vertices_642) then 1 else
  if p.val = (true, vertices_770) then 2 else
  if p.val = (true, vertices_140) then 3 else
  if p.val = (true, vertices_268) then 4 else
  if p.val = (true, vertices_164) then 5 else
  if p.val = (true, vertices_580) then 6 else
  if p.val = (true, vertices_644) then 7 else
  if p.val = (true, vertices_772) then 8 else
  if p.val = (true, vertices_784) then 9 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_530), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_642), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_770), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_140), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_268), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_164), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_580), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_644), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_772), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_784), by decide +kernel⟩
  | 10 => Sum.inl 1
  | 11 => Sum.inr ⟨(false, vertices_357), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_526), by decide +kernel⟩
  | 13 => Sum.inl 0
  | 14 => Sum.inr ⟨(false, vertices_155), by decide +kernel⟩
  | 15 => Sum.inr ⟨(false, vertices_299), by decide +kernel⟩
  | 16 => Sum.inr ⟨(false, vertices_339), by decide +kernel⟩
  | 17 => Sum.inl 2
  | 18 => Sum.inr ⟨(false, vertices_233), by decide +kernel⟩
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
cert_row_2 0 0 1 2 8 526
cert_row_4 1 1 2 4 6 7 428 140 2
cert_row_4 2 1 3 5 7 8 852 324 1
cert_row_4 3 1 4 5 6 8 740 100 3
cert_rows
cert_pivot_2 0 2 3 1
cert_heightProof 4
cert_coverFacet 0 654
cert_cover_5 0 0 0 1 2 6 526 654 3
cert_coverFacet 1 782
cert_cover_5 1 0 0 1 2 7 526 782 3
cert_coverFacet 2 658
cert_cover_2 2 3 0 6 8 146 658 3
cert_coverFacet 3 786
cert_cover_2 3 3 0 7 8 274 786 3
cert_coverFacet 4 428
cert_cover_5 4 1 1 2 4 6 140 428 2
cert_coverFacet 5 852
cert_cover_5 5 2 1 3 5 7 324 852 1
cert_coverFacet 6 740
cert_cover_5 6 3 1 4 5 6 100 740 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m13e11q1_0004

end
end BundlePart10

section BundlePart11
/- Source: ProjectionCertificates/R_m13e11q1_0005.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m13e11q1_0005

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [87, 203, 523, 563, 397, 309, 197, 809, 602, 244, 932, 968, 752, 11, 19, 67, 515, 21, 69, 133, 261, 137, 265, 521, 49, 289, 545, 193, 74, 522, 82, 530, 52, 84, 164, 292, 196, 388, 200, 584, 392, 776, 240, 560, 592, 672, 800, 704, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_87, vertices_203, vertices_523, vertices_563, vertices_397, vertices_309, vertices_197, vertices_809, vertices_602, vertices_244, vertices_932, vertices_968, vertices_752] (by decide +kernel)
  polygons := literalFinset [vertices_11, vertices_19, vertices_67, vertices_515, vertices_21, vertices_69, vertices_133, vertices_261, vertices_137, vertices_265, vertices_521, vertices_49, vertices_289, vertices_545, vertices_193, vertices_74, vertices_522, vertices_82, vertices_530, vertices_52, vertices_84, vertices_164, vertices_292, vertices_196, vertices_388, vertices_200, vertices_584, vertices_392, vertices_776, vertices_240, vertices_560, vertices_592, vertices_672, vertices_800, vertices_704, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_87), (false, vertices_203), (false, vertices_523), (false, vertices_563), (false, vertices_397), (false, vertices_309), (false, vertices_197), (false, vertices_809), (true, vertices_164), (true, vertices_584), (true, vertices_240), (true, vertices_592), (true, vertices_672), (true, vertices_704), (true, vertices_896)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 8 12 15 17 19 20 21 22 23
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_87) then 9 else
  if p.val = (false, vertices_203) then 10 else
  if p.val = (false, vertices_523) then 0 else
  if p.val = (false, vertices_563) then 11 else
  if p.val = (false, vertices_397) then 13 else
  if p.val = (false, vertices_309) then 14 else
  if p.val = (false, vertices_197) then 1 else
  if p.val = (false, vertices_809) then 16 else
  if p.val = (true, vertices_164) then 2 else
  if p.val = (true, vertices_584) then 3 else
  if p.val = (true, vertices_240) then 18 else
  if p.val = (true, vertices_592) then 4 else
  if p.val = (true, vertices_672) then 5 else
  if p.val = (true, vertices_704) then 6 else
  if p.val = (true, vertices_896) then 7 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_523), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_197), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_164), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_584), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_592), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_672), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_704), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_896), by decide +kernel⟩
  | 8 => Sum.inl 0
  | 9 => Sum.inr ⟨(false, vertices_87), by decide +kernel⟩
  | 10 => Sum.inr ⟨(false, vertices_203), by decide +kernel⟩
  | 11 => Sum.inr ⟨(false, vertices_563), by decide +kernel⟩
  | 12 => Sum.inl 1
  | 13 => Sum.inr ⟨(false, vertices_397), by decide +kernel⟩
  | 14 => Sum.inr ⟨(false, vertices_309), by decide +kernel⟩
  | 15 => Sum.inl 2
  | 16 => Sum.inr ⟨(false, vertices_809), by decide +kernel⟩
  | 17 => Sum.inl 3
  | 18 => Sum.inr ⟨(true, vertices_240), by decide +kernel⟩
  | 19 => Sum.inl 4
  | 20 => Sum.inl 5
  | 21 => Sum.inl 6
  | 22 => Sum.inl 7
  | 23 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 2 3 5 8 602 74 2
cert_row_2 1 3 4 5 6 240
cert_row_4 2 1 4 6 7 8 932 164 3
cert_row_4 3 2 5 6 7 8 968 200 3
cert_rows
cert_pivot_2 0 3 1 2
cert_heightProof 4
cert_coverFacet 0 602
cert_cover_5 0 0 0 2 3 5 74 602 2
cert_coverFacet 1 244
cert_cover_5 1 1 1 3 4 5 52 244 3
cert_coverFacet 2 932
cert_cover_5 2 2 1 4 6 7 164 932 3
cert_coverFacet 3 968
cert_cover_5 3 3 2 5 6 7 200 968 3
cert_coverFacet 4 752
cert_cover_5 4 1 3 4 5 8 240 752 3
cert_coveringFacets_3
cert_coveringProof_7
cert_certificate 4 5
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m13e11q1_0005

end
end BundlePart11

section BundlePart12
/- Source: ProjectionCertificates/R_m13e11q1_0008.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m13e11q1_0008

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [787, 541, 205, 677, 345, 961, 558, 122, 538, 370, 930, 108, 484, 13, 133, 517, 25, 73, 273, 529, 193, 321, 641, 769, 26, 42, 522, 114, 274, 530, 290, 546, 770, 44, 76, 524, 100, 164, 548, 196, 88, 536, 104, 336, 352, 416, 672, 448, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_787, vertices_541, vertices_205, vertices_677, vertices_345, vertices_961, vertices_558, vertices_122, vertices_538, vertices_370, vertices_930, vertices_108, vertices_484] (by decide +kernel)
  polygons := literalFinset [vertices_13, vertices_133, vertices_517, vertices_25, vertices_73, vertices_273, vertices_529, vertices_193, vertices_321, vertices_641, vertices_769, vertices_26, vertices_42, vertices_522, vertices_114, vertices_274, vertices_530, vertices_290, vertices_546, vertices_770, vertices_44, vertices_76, vertices_524, vertices_100, vertices_164, vertices_548, vertices_196, vertices_88, vertices_536, vertices_104, vertices_336, vertices_352, vertices_416, vertices_672, vertices_448, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_787), (false, vertices_541), (false, vertices_205), (false, vertices_677), (false, vertices_345), (false, vertices_961), (true, vertices_26), (true, vertices_42), (true, vertices_522), (true, vertices_114), (true, vertices_290), (true, vertices_546), (true, vertices_44), (true, vertices_100), (true, vertices_104), (true, vertices_352), (true, vertices_416)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 10 13 17 19 20 21 23 24 25
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_787) then 11 else
  if p.val = (false, vertices_541) then 14 else
  if p.val = (false, vertices_205) then 15 else
  if p.val = (false, vertices_677) then 16 else
  if p.val = (false, vertices_345) then 18 else
  if p.val = (false, vertices_961) then 22 else
  if p.val = (true, vertices_26) then 0 else
  if p.val = (true, vertices_42) then 1 else
  if p.val = (true, vertices_522) then 2 else
  if p.val = (true, vertices_114) then 12 else
  if p.val = (true, vertices_290) then 3 else
  if p.val = (true, vertices_546) then 4 else
  if p.val = (true, vertices_44) then 5 else
  if p.val = (true, vertices_100) then 6 else
  if p.val = (true, vertices_104) then 7 else
  if p.val = (true, vertices_352) then 8 else
  if p.val = (true, vertices_416) then 9 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_26), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_42), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_522), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_290), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_546), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_44), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_100), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_104), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_352), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_416), by decide +kernel⟩
  | 10 => Sum.inl 0
  | 11 => Sum.inr ⟨(false, vertices_787), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_114), by decide +kernel⟩
  | 13 => Sum.inl 1
  | 14 => Sum.inr ⟨(false, vertices_541), by decide +kernel⟩
  | 15 => Sum.inr ⟨(false, vertices_205), by decide +kernel⟩
  | 16 => Sum.inr ⟨(false, vertices_677), by decide +kernel⟩
  | 17 => Sum.inl 2
  | 18 => Sum.inr ⟨(false, vertices_345), by decide +kernel⟩
  | 19 => Sum.inl 3
  | 20 => Sum.inl 4
  | 21 => Sum.inl 5
  | 22 => Sum.inr ⟨(false, vertices_961), by decide +kernel⟩
  | 23 => Sum.inl 6
  | 24 => Sum.inl 7
  | 25 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 3 4 5 114
cert_row_4 1 0 1 2 4 8 558 42 1
cert_row_4 2 0 4 6 7 8 930 290 2
cert_row_4 3 1 4 5 6 7 484 100 3
cert_rows
cert_pivot_2 3 2 0 1
cert_heightProof 4
cert_coverFacet 0 558
cert_cover_5 0 1 0 1 2 4 42 558 1
cert_coverFacet 1 122
cert_cover_5 1 0 0 2 3 4 26 122 3
cert_coverFacet 2 538
cert_cover_2 2 2 0 3 8 26 538 3
cert_coverFacet 3 370
cert_cover_5 3 0 0 3 4 7 114 370 3
cert_coverFacet 4 930
cert_cover_5 4 2 0 4 6 7 290 930 2
cert_coverFacet 5 108
cert_cover_2 5 2 1 4 5 44 108 3
cert_coverFacet 6 484
cert_cover_5 6 3 1 4 5 6 100 484 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m13e11q1_0008

end
end BundlePart12

section BundlePart13
/- Source: ProjectionCertificates/R_m13e11q1_0009.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m13e11q1_0009

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [583, 787, 99, 419, 661, 229, 409, 618, 802, 220, 604, 824, 488, 35, 67, 259, 515, 69, 133, 517, 145, 273, 529, 97, 161, 385, 98, 290, 546, 578, 770, 92, 148, 532, 196, 580, 152, 280, 536, 104, 296, 552, 200, 584, 392, 784, 224, 416, 800]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_583, vertices_787, vertices_99, vertices_419, vertices_661, vertices_229, vertices_409, vertices_618, vertices_802, vertices_220, vertices_604, vertices_824, vertices_488] (by decide +kernel)
  polygons := literalFinset [vertices_35, vertices_67, vertices_259, vertices_515, vertices_69, vertices_133, vertices_517, vertices_145, vertices_273, vertices_529, vertices_97, vertices_161, vertices_385, vertices_98, vertices_290, vertices_546, vertices_578, vertices_770, vertices_92, vertices_148, vertices_532, vertices_196, vertices_580, vertices_152, vertices_280, vertices_536, vertices_104, vertices_296, vertices_552, vertices_200, vertices_584, vertices_392, vertices_784, vertices_224, vertices_416, vertices_800] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_583), (false, vertices_787), (false, vertices_99), (false, vertices_419), (false, vertices_661), (false, vertices_229), (false, vertices_409), (true, vertices_546), (true, vertices_92), (true, vertices_536), (true, vertices_104), (true, vertices_296), (true, vertices_552), (true, vertices_200), (true, vertices_584), (true, vertices_800)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 9 13 17 19 20 21 22 23 24
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_583) then 10 else
  if p.val = (false, vertices_787) then 11 else
  if p.val = (false, vertices_99) then 0 else
  if p.val = (false, vertices_419) then 12 else
  if p.val = (false, vertices_661) then 14 else
  if p.val = (false, vertices_229) then 15 else
  if p.val = (false, vertices_409) then 18 else
  if p.val = (true, vertices_546) then 1 else
  if p.val = (true, vertices_92) then 16 else
  if p.val = (true, vertices_536) then 2 else
  if p.val = (true, vertices_104) then 3 else
  if p.val = (true, vertices_296) then 4 else
  if p.val = (true, vertices_552) then 5 else
  if p.val = (true, vertices_200) then 6 else
  if p.val = (true, vertices_584) then 7 else
  if p.val = (true, vertices_800) then 8 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_99), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_546), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_536), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_104), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_296), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_552), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_200), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_584), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_800), by decide +kernel⟩
  | 9 => Sum.inl 0
  | 10 => Sum.inr ⟨(false, vertices_583), by decide +kernel⟩
  | 11 => Sum.inr ⟨(false, vertices_787), by decide +kernel⟩
  | 12 => Sum.inr ⟨(false, vertices_419), by decide +kernel⟩
  | 13 => Sum.inl 1
  | 14 => Sum.inr ⟨(false, vertices_661), by decide +kernel⟩
  | 15 => Sum.inr ⟨(false, vertices_229), by decide +kernel⟩
  | 16 => Sum.inr ⟨(true, vertices_92), by decide +kernel⟩
  | 17 => Sum.inl 2
  | 18 => Sum.inr ⟨(false, vertices_409), by decide +kernel⟩
  | 19 => Sum.inl 3
  | 20 => Sum.inl 4
  | 21 => Sum.inl 5
  | 22 => Sum.inl 6
  | 23 => Sum.inl 7
  | 24 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 1 2 3 5 92
cert_row_4 1 0 2 4 5 8 618 98 1
cert_row_4 2 2 3 4 7 8 824 280 2
cert_row_4 3 2 4 5 6 7 488 104 3
cert_rows
cert_pivot_2 1 0 3 2
cert_heightProof 4
cert_coverFacet 0 618
cert_cover_5 0 1 0 2 4 5 98 618 1
cert_coverFacet 1 802
cert_cover_2 1 4 0 7 8 290 802 3
cert_coverFacet 2 220
cert_cover_5 2 0 1 2 3 6 92 220 3
cert_coverFacet 3 604
cert_cover_5 3 0 1 2 3 8 92 604 3
cert_coverFacet 4 824
cert_cover_5 4 2 2 3 4 7 280 824 2
cert_coverFacet 5 488
cert_cover_5 5 3 2 4 5 6 104 488 3
cert_coveringFacets
cert_coveringProof_6
cert_certificate 4 6
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m13e11q1_0009

end
end BundlePart13

section BundlePart14
/- Source: ProjectionCertificates/R_m13e11q1_0010.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m13e11q1_0010

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [87, 779, 563, 451, 61, 397, 197, 553, 850, 684, 244, 968, 752, 19, 67, 259, 515, 13, 21, 69, 133, 41, 265, 521, 49, 545, 193, 385, 82, 530, 322, 770, 44, 140, 52, 84, 164, 196, 552, 392, 648, 776, 240, 560, 592, 672, 448, 704, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_87, vertices_779, vertices_563, vertices_451, vertices_61, vertices_397, vertices_197, vertices_553, vertices_850, vertices_684, vertices_244, vertices_968, vertices_752] (by decide +kernel)
  polygons := literalFinset [vertices_19, vertices_67, vertices_259, vertices_515, vertices_13, vertices_21, vertices_69, vertices_133, vertices_41, vertices_265, vertices_521, vertices_49, vertices_545, vertices_193, vertices_385, vertices_82, vertices_530, vertices_322, vertices_770, vertices_44, vertices_140, vertices_52, vertices_84, vertices_164, vertices_196, vertices_552, vertices_392, vertices_648, vertices_776, vertices_240, vertices_560, vertices_592, vertices_672, vertices_448, vertices_704, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_87), (false, vertices_779), (false, vertices_563), (false, vertices_451), (false, vertices_61), (false, vertices_397), (false, vertices_197), (false, vertices_553), (true, vertices_164), (true, vertices_648), (true, vertices_240), (true, vertices_592), (true, vertices_672), (true, vertices_704), (true, vertices_832)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 12 8 16 17 19 20 21 22 23
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_87) then 9 else
  if p.val = (false, vertices_779) then 13 else
  if p.val = (false, vertices_563) then 14 else
  if p.val = (false, vertices_451) then 15 else
  if p.val = (false, vertices_61) then 10 else
  if p.val = (false, vertices_397) then 11 else
  if p.val = (false, vertices_197) then 0 else
  if p.val = (false, vertices_553) then 1 else
  if p.val = (true, vertices_164) then 2 else
  if p.val = (true, vertices_648) then 3 else
  if p.val = (true, vertices_240) then 18 else
  if p.val = (true, vertices_592) then 4 else
  if p.val = (true, vertices_672) then 5 else
  if p.val = (true, vertices_704) then 6 else
  if p.val = (true, vertices_832) then 7 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_197), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_553), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_164), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_648), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_592), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_672), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_704), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_832), by decide +kernel⟩
  | 8 => Sum.inl 1
  | 9 => Sum.inr ⟨(false, vertices_87), by decide +kernel⟩
  | 10 => Sum.inr ⟨(false, vertices_61), by decide +kernel⟩
  | 11 => Sum.inr ⟨(false, vertices_397), by decide +kernel⟩
  | 12 => Sum.inl 0
  | 13 => Sum.inr ⟨(false, vertices_779), by decide +kernel⟩
  | 14 => Sum.inr ⟨(false, vertices_563), by decide +kernel⟩
  | 15 => Sum.inr ⟨(false, vertices_451), by decide +kernel⟩
  | 16 => Sum.inl 2
  | 17 => Sum.inl 3
  | 18 => Sum.inr ⟨(true, vertices_240), by decide +kernel⟩
  | 19 => Sum.inl 4
  | 20 => Sum.inl 5
  | 21 => Sum.inl 6
  | 22 => Sum.inl 7
  | 23 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 3 5 7 8 850 82 3
cert_row_2 1 3 4 5 6 240
cert_row_4 2 1 2 4 6 8 684 44 3
cert_row_4 3 2 5 6 7 8 968 392 1
cert_rows
cert_pivot_2 0 3 1 2
cert_heightProof 4
cert_coverFacet 0 850
cert_cover_5 0 0 0 3 5 7 82 850 3
cert_coverFacet 1 684
cert_cover_5 1 2 1 2 4 6 44 684 3
cert_coverFacet 2 244
cert_cover_5 2 1 1 3 4 5 52 244 3
cert_coverFacet 3 968
cert_cover_5 3 3 2 5 6 7 392 968 1
cert_coverFacet 4 752
cert_cover_5 4 1 3 4 5 8 240 752 3
cert_coveringFacets_3
cert_coveringProof_7
cert_certificate 4 5
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m13e11q1_0010

end
end BundlePart14

section BundlePart15
/- Source: ProjectionCertificates/R_m13e11q1_0011.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m13e11q1_0011

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [555, 51, 787, 61, 653, 405, 961, 118, 466, 866, 236, 212, 744, 19, 35, 515, 13, 21, 133, 41, 521, 49, 273, 385, 641, 769, 50, 82, 274, 98, 546, 322, 770, 44, 140, 52, 84, 148, 100, 196, 232, 552, 648, 208, 400, 608, 448, 704, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_555, vertices_51, vertices_787, vertices_61, vertices_653, vertices_405, vertices_961, vertices_118, vertices_466, vertices_866, vertices_236, vertices_212, vertices_744] (by decide +kernel)
  polygons := literalFinset [vertices_19, vertices_35, vertices_515, vertices_13, vertices_21, vertices_133, vertices_41, vertices_521, vertices_49, vertices_273, vertices_385, vertices_641, vertices_769, vertices_50, vertices_82, vertices_274, vertices_98, vertices_546, vertices_322, vertices_770, vertices_44, vertices_140, vertices_52, vertices_84, vertices_148, vertices_100, vertices_196, vertices_232, vertices_552, vertices_648, vertices_208, vertices_400, vertices_608, vertices_448, vertices_704, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_555), (false, vertices_51), (false, vertices_787), (false, vertices_61), (false, vertices_653), (false, vertices_405), (false, vertices_961), (true, vertices_82), (true, vertices_98), (true, vertices_322), (true, vertices_84), (true, vertices_100), (true, vertices_196), (true, vertices_232), (true, vertices_208), (true, vertices_608)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 9 12 16 18 19 20 22 23 24
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_555) then 10 else
  if p.val = (false, vertices_51) then 0 else
  if p.val = (false, vertices_787) then 11 else
  if p.val = (false, vertices_61) then 13 else
  if p.val = (false, vertices_653) then 14 else
  if p.val = (false, vertices_405) then 15 else
  if p.val = (false, vertices_961) then 21 else
  if p.val = (true, vertices_82) then 1 else
  if p.val = (true, vertices_98) then 2 else
  if p.val = (true, vertices_322) then 3 else
  if p.val = (true, vertices_84) then 4 else
  if p.val = (true, vertices_100) then 5 else
  if p.val = (true, vertices_196) then 6 else
  if p.val = (true, vertices_232) then 17 else
  if p.val = (true, vertices_208) then 7 else
  if p.val = (true, vertices_608) then 8 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_51), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_82), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_98), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_322), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_84), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_100), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_196), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_208), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_608), by decide +kernel⟩
  | 9 => Sum.inl 0
  | 10 => Sum.inr ⟨(false, vertices_555), by decide +kernel⟩
  | 11 => Sum.inr ⟨(false, vertices_787), by decide +kernel⟩
  | 12 => Sum.inl 1
  | 13 => Sum.inr ⟨(false, vertices_61), by decide +kernel⟩
  | 14 => Sum.inr ⟨(false, vertices_653), by decide +kernel⟩
  | 15 => Sum.inr ⟨(false, vertices_405), by decide +kernel⟩
  | 16 => Sum.inl 2
  | 17 => Sum.inr ⟨(true, vertices_232), by decide +kernel⟩
  | 18 => Sum.inl 3
  | 19 => Sum.inl 4
  | 20 => Sum.inl 5
  | 21 => Sum.inr ⟨(false, vertices_961), by decide +kernel⟩
  | 22 => Sum.inl 6
  | 23 => Sum.inl 7
  | 24 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 2 4 5 6 232
cert_row_4 1 0 1 3 4 5 118 50 1
cert_row_4 2 0 3 5 6 7 466 82 3
cert_row_4 3 0 4 5 7 8 866 98 3
cert_rows
cert_pivot_2 2 1 3 0
cert_heightProof 4
cert_coverFacet 0 118
cert_cover_5 0 1 0 1 3 4 50 118 1
cert_coverFacet 1 466
cert_cover_5 1 2 0 3 5 6 82 466 3
cert_coverFacet 2 866
cert_cover_5 2 3 0 4 5 7 98 866 3
cert_coverFacet 3 236
cert_cover_5 3 0 1 2 4 5 44 236 3
cert_coverFacet 4 212
cert_cover_2 4 3 1 5 6 84 212 3
cert_coverFacet 5 744
cert_cover_5 5 0 2 4 5 8 232 744 3
cert_coveringFacets
cert_coveringProof_6
cert_certificate 4 6
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m13e11q1_0011

end
end BundlePart15

section BundlePart16
/- Source: ProjectionCertificates/R_m13e11q1_0013.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m13e11q1_0013

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [155, 299, 339, 173, 721, 481, 654, 782, 658, 786, 364, 852, 740, 11, 19, 259, 41, 137, 81, 145, 161, 289, 193, 321, 526, 138, 266, 146, 274, 530, 642, 770, 44, 140, 268, 100, 164, 324, 580, 644, 772, 296, 336, 592, 656, 784, 224, 352, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_155, vertices_299, vertices_339, vertices_173, vertices_721, vertices_481, vertices_654, vertices_782, vertices_658, vertices_786, vertices_364, vertices_852, vertices_740] (by decide +kernel)
  polygons := literalFinset [vertices_11, vertices_19, vertices_259, vertices_41, vertices_137, vertices_81, vertices_145, vertices_161, vertices_289, vertices_193, vertices_321, vertices_526, vertices_138, vertices_266, vertices_146, vertices_274, vertices_530, vertices_642, vertices_770, vertices_44, vertices_140, vertices_268, vertices_100, vertices_164, vertices_324, vertices_580, vertices_644, vertices_772, vertices_296, vertices_336, vertices_592, vertices_656, vertices_784, vertices_224, vertices_352, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_155), (false, vertices_299), (false, vertices_339), (false, vertices_173), (false, vertices_721), (false, vertices_481), (true, vertices_526), (true, vertices_530), (true, vertices_642), (true, vertices_770), (true, vertices_268), (true, vertices_100), (true, vertices_324), (true, vertices_580), (true, vertices_644), (true, vertices_772), (true, vertices_784)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 13 10 17 18 20 22 23 24 25
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_155) then 14 else
  if p.val = (false, vertices_299) then 15 else
  if p.val = (false, vertices_339) then 16 else
  if p.val = (false, vertices_173) then 11 else
  if p.val = (false, vertices_721) then 19 else
  if p.val = (false, vertices_481) then 21 else
  if p.val = (true, vertices_526) then 12 else
  if p.val = (true, vertices_530) then 0 else
  if p.val = (true, vertices_642) then 1 else
  if p.val = (true, vertices_770) then 2 else
  if p.val = (true, vertices_268) then 3 else
  if p.val = (true, vertices_100) then 4 else
  if p.val = (true, vertices_324) then 5 else
  if p.val = (true, vertices_580) then 6 else
  if p.val = (true, vertices_644) then 7 else
  if p.val = (true, vertices_772) then 8 else
  if p.val = (true, vertices_784) then 9 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_530), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_642), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_770), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_268), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_100), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_324), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_580), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_644), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_772), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_784), by decide +kernel⟩
  | 10 => Sum.inl 1
  | 11 => Sum.inr ⟨(false, vertices_173), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_526), by decide +kernel⟩
  | 13 => Sum.inl 0
  | 14 => Sum.inr ⟨(false, vertices_155), by decide +kernel⟩
  | 15 => Sum.inr ⟨(false, vertices_299), by decide +kernel⟩
  | 16 => Sum.inr ⟨(false, vertices_339), by decide +kernel⟩
  | 17 => Sum.inl 2
  | 18 => Sum.inl 3
  | 19 => Sum.inr ⟨(false, vertices_721), by decide +kernel⟩
  | 20 => Sum.inl 4
  | 21 => Sum.inr ⟨(false, vertices_481), by decide +kernel⟩
  | 22 => Sum.inl 5
  | 23 => Sum.inl 6
  | 24 => Sum.inl 7
  | 25 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 1 2 8 526
cert_row_4 1 1 2 4 5 7 364 44 3
cert_row_4 2 1 3 5 7 8 852 324 1
cert_row_4 3 1 4 5 6 8 740 100 3
cert_rows
cert_pivot_2 0 2 3 1
cert_heightProof 4
cert_coverFacet 0 654
cert_cover_5 0 0 0 1 2 6 526 654 3
cert_coverFacet 1 782
cert_cover_5 1 0 0 1 2 7 526 782 3
cert_coverFacet 2 658
cert_cover_2 2 3 0 6 8 146 658 3
cert_coverFacet 3 786
cert_cover_2 3 3 0 7 8 274 786 3
cert_coverFacet 4 364
cert_cover_5 4 1 1 2 4 5 44 364 3
cert_coverFacet 5 852
cert_cover_5 5 2 1 3 5 7 324 852 1
cert_coverFacet 6 740
cert_cover_5 6 3 1 4 5 6 100 740 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m13e11q1_0013

end
end BundlePart16

section BundlePart17
/- Source: ProjectionCertificates/R_m13e11q2_0000.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m13e11q2_0000

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [647, 781, 213, 341, 361, 713, 182, 310, 774, 810, 738, 616, 496, 85, 133, 261, 517, 73, 265, 521, 193, 321, 641, 54, 134, 262, 518, 162, 290, 546, 642, 770, 148, 276, 772, 104, 296, 552, 584, 776, 176, 304, 208, 336, 224, 352, 608, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_647, vertices_781, vertices_213, vertices_341, vertices_361, vertices_713, vertices_182, vertices_310, vertices_774, vertices_810, vertices_738, vertices_616, vertices_496] (by decide +kernel)
  polygons := literalFinset [vertices_85, vertices_133, vertices_261, vertices_517, vertices_73, vertices_265, vertices_521, vertices_193, vertices_321, vertices_641, vertices_54, vertices_134, vertices_262, vertices_518, vertices_162, vertices_290, vertices_546, vertices_642, vertices_770, vertices_148, vertices_276, vertices_772, vertices_104, vertices_296, vertices_552, vertices_584, vertices_776, vertices_176, vertices_304, vertices_208, vertices_336, vertices_224, vertices_352, vertices_608, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_647), (false, vertices_781), (false, vertices_213), (false, vertices_341), (false, vertices_361), (false, vertices_713), (true, vertices_54), (true, vertices_262), (true, vertices_162), (true, vertices_290), (true, vertices_546), (true, vertices_770), (true, vertices_552), (true, vertices_176), (true, vertices_304), (true, vertices_224), (true, vertices_608)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 10 13 17 20 21 22 23 24 25
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_647) then 11 else
  if p.val = (false, vertices_781) then 14 else
  if p.val = (false, vertices_213) then 15 else
  if p.val = (false, vertices_341) then 16 else
  if p.val = (false, vertices_361) then 18 else
  if p.val = (false, vertices_713) then 19 else
  if p.val = (true, vertices_54) then 12 else
  if p.val = (true, vertices_262) then 0 else
  if p.val = (true, vertices_162) then 1 else
  if p.val = (true, vertices_290) then 2 else
  if p.val = (true, vertices_546) then 3 else
  if p.val = (true, vertices_770) then 4 else
  if p.val = (true, vertices_552) then 5 else
  if p.val = (true, vertices_176) then 6 else
  if p.val = (true, vertices_304) then 7 else
  if p.val = (true, vertices_224) then 8 else
  if p.val = (true, vertices_608) then 9 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_262), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_162), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_290), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_546), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_770), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_552), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_176), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_304), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_224), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_608), by decide +kernel⟩
  | 10 => Sum.inl 0
  | 11 => Sum.inr ⟨(false, vertices_647), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_54), by decide +kernel⟩
  | 13 => Sum.inl 1
  | 14 => Sum.inr ⟨(false, vertices_781), by decide +kernel⟩
  | 15 => Sum.inr ⟨(false, vertices_213), by decide +kernel⟩
  | 16 => Sum.inr ⟨(false, vertices_341), by decide +kernel⟩
  | 17 => Sum.inl 2
  | 18 => Sum.inr ⟨(false, vertices_361), by decide +kernel⟩
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
cert_row_2 0 0 1 3 4 54
cert_row_4 1 0 2 4 7 8 810 290 1
cert_row_4 2 0 4 5 6 8 738 162 2
cert_row_4 3 3 4 5 6 7 496 176 2
cert_rows
cert_pivot_2 1 2 0 3
cert_heightProof 4
cert_coverFacet 0 182
cert_cover_5 0 0 0 1 3 6 54 182 3
cert_coverFacet 1 310
cert_cover_5 1 0 0 1 3 7 54 310 3
cert_coverFacet 2 774
cert_cover_2 2 1 0 7 8 262 774 3
cert_coverFacet 3 810
cert_cover_5 3 1 0 2 4 7 290 810 1
cert_coverFacet 4 738
cert_cover_5 4 2 0 4 5 6 162 738 2
cert_coverFacet 5 616
cert_cover_2 5 4 2 5 8 104 616 3
cert_coverFacet 6 496
cert_cover_5 6 3 3 4 5 6 176 496 2
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m13e11q2_0000

end
end BundlePart17

section BundlePart18
/- Source: ProjectionCertificates/R_m13e11q2_0001.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m13e11q2_0001

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [803, 205, 333, 181, 789, 561, 481, 782, 362, 714, 738, 668, 688, 77, 21, 133, 261, 49, 529, 161, 289, 545, 193, 321, 769, 74, 266, 522, 98, 290, 546, 706, 770, 140, 268, 524, 148, 532, 772, 200, 328, 648, 176, 560, 656, 224, 352, 672]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_803, vertices_205, vertices_333, vertices_181, vertices_789, vertices_561, vertices_481, vertices_782, vertices_362, vertices_714, vertices_738, vertices_668, vertices_688] (by decide +kernel)
  polygons := literalFinset [vertices_77, vertices_21, vertices_133, vertices_261, vertices_49, vertices_529, vertices_161, vertices_289, vertices_545, vertices_193, vertices_321, vertices_769, vertices_74, vertices_266, vertices_522, vertices_98, vertices_290, vertices_546, vertices_706, vertices_770, vertices_140, vertices_268, vertices_524, vertices_148, vertices_532, vertices_772, vertices_200, vertices_328, vertices_648, vertices_176, vertices_560, vertices_656, vertices_224, vertices_352, vertices_672] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_803), (false, vertices_205), (false, vertices_333), (false, vertices_181), (false, vertices_789), (false, vertices_561), (false, vertices_481), (true, vertices_74), (true, vertices_266), (true, vertices_522), (true, vertices_98), (true, vertices_706), (true, vertices_524), (true, vertices_648), (true, vertices_656), (true, vertices_672)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 9 15 12 18 19 21 22 23 24
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_803) then 10 else
  if p.val = (false, vertices_205) then 13 else
  if p.val = (false, vertices_333) then 14 else
  if p.val = (false, vertices_181) then 16 else
  if p.val = (false, vertices_789) then 17 else
  if p.val = (false, vertices_561) then 0 else
  if p.val = (false, vertices_481) then 20 else
  if p.val = (true, vertices_74) then 1 else
  if p.val = (true, vertices_266) then 2 else
  if p.val = (true, vertices_522) then 3 else
  if p.val = (true, vertices_98) then 4 else
  if p.val = (true, vertices_706) then 11 else
  if p.val = (true, vertices_524) then 5 else
  if p.val = (true, vertices_648) then 6 else
  if p.val = (true, vertices_656) then 7 else
  if p.val = (true, vertices_672) then 8 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_561), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_74), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_266), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_522), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_98), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_524), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_648), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_656), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_672), by decide +kernel⟩
  | 9 => Sum.inl 0
  | 10 => Sum.inr ⟨(false, vertices_803), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_706), by decide +kernel⟩
  | 12 => Sum.inl 2
  | 13 => Sum.inr ⟨(false, vertices_205), by decide +kernel⟩
  | 14 => Sum.inr ⟨(false, vertices_333), by decide +kernel⟩
  | 15 => Sum.inl 1
  | 16 => Sum.inr ⟨(false, vertices_181), by decide +kernel⟩
  | 17 => Sum.inr ⟨(false, vertices_789), by decide +kernel⟩
  | 18 => Sum.inl 3
  | 19 => Sum.inl 4
  | 20 => Sum.inr ⟨(false, vertices_481), by decide +kernel⟩
  | 21 => Sum.inl 5
  | 22 => Sum.inl 6
  | 23 => Sum.inl 7
  | 24 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 2 4 5 7 362 74 2
cert_row_2 1 0 5 6 8 706
cert_row_4 2 0 1 2 7 8 782 266 1
cert_row_4 3 1 2 3 6 8 668 140 2
cert_rows
cert_pivot_2 4 5 0 1
cert_heightProof 4
cert_coverFacet 0 782
cert_cover_5 0 2 0 1 2 7 266 782 1
cert_coverFacet 1 362
cert_cover_5 1 0 0 2 4 5 74 362 2
cert_coverFacet 2 714
cert_cover_5 2 1 0 2 5 6 74 714 3
cert_coverFacet 3 738
cert_cover_5 3 1 0 4 5 6 98 738 3
cert_coverFacet 4 668
cert_cover_5 4 3 1 2 3 6 140 668 2
cert_coverFacet 5 688
cert_cover_2 5 4 3 6 8 176 688 3
cert_coveringFacets
cert_coveringProof_6
cert_certificate 4 6
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m13e11q2_0001

end
end BundlePart18

section BundlePart19
/- Source: ProjectionCertificates/R_m13e11q2_0003.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m13e11q2_0003

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [403, 333, 789, 613, 457, 721, 806, 426, 242, 626, 786, 236, 300, 69, 261, 517, 329, 145, 273, 529, 193, 577, 385, 114, 146, 274, 530, 162, 290, 546, 386, 770, 44, 76, 268, 100, 292, 548, 772, 168, 296, 200, 392, 208, 592, 784, 224, 608]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_403, vertices_333, vertices_789, vertices_613, vertices_457, vertices_721, vertices_806, vertices_426, vertices_242, vertices_626, vertices_786, vertices_236, vertices_300] (by decide +kernel)
  polygons := literalFinset [vertices_69, vertices_261, vertices_517, vertices_329, vertices_145, vertices_273, vertices_529, vertices_193, vertices_577, vertices_385, vertices_114, vertices_146, vertices_274, vertices_530, vertices_162, vertices_290, vertices_546, vertices_386, vertices_770, vertices_44, vertices_76, vertices_268, vertices_100, vertices_292, vertices_548, vertices_772, vertices_168, vertices_296, vertices_200, vertices_392, vertices_208, vertices_592, vertices_784, vertices_224, vertices_608] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_403), (false, vertices_333), (false, vertices_789), (false, vertices_613), (false, vertices_457), (false, vertices_721), (true, vertices_114), (true, vertices_530), (true, vertices_162), (true, vertices_290), (true, vertices_546), (true, vertices_770), (true, vertices_44), (true, vertices_292), (true, vertices_168), (true, vertices_296), (true, vertices_224)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 10 13 16 19 21 22 23 24 25
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_403) then 11 else
  if p.val = (false, vertices_333) then 17 else
  if p.val = (false, vertices_789) then 14 else
  if p.val = (false, vertices_613) then 15 else
  if p.val = (false, vertices_457) then 18 else
  if p.val = (false, vertices_721) then 20 else
  if p.val = (true, vertices_114) then 12 else
  if p.val = (true, vertices_530) then 0 else
  if p.val = (true, vertices_162) then 1 else
  if p.val = (true, vertices_290) then 2 else
  if p.val = (true, vertices_546) then 3 else
  if p.val = (true, vertices_770) then 4 else
  if p.val = (true, vertices_44) then 5 else
  if p.val = (true, vertices_292) then 6 else
  if p.val = (true, vertices_168) then 7 else
  if p.val = (true, vertices_296) then 8 else
  if p.val = (true, vertices_224) then 9 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_530), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_162), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_290), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_546), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_770), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_44), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_292), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_168), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_296), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_224), by decide +kernel⟩
  | 10 => Sum.inl 0
  | 11 => Sum.inr ⟨(false, vertices_403), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_114), by decide +kernel⟩
  | 13 => Sum.inl 1
  | 14 => Sum.inr ⟨(false, vertices_789), by decide +kernel⟩
  | 15 => Sum.inr ⟨(false, vertices_613), by decide +kernel⟩
  | 16 => Sum.inl 2
  | 17 => Sum.inr ⟨(false, vertices_333), by decide +kernel⟩
  | 18 => Sum.inr ⟨(false, vertices_457), by decide +kernel⟩
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
cert_row_2 0 0 3 4 5 114
cert_row_4 1 0 1 4 7 8 806 290 1
cert_row_4 2 0 2 4 6 7 426 162 1
cert_row_4 3 1 2 4 5 6 236 44 3
cert_rows
cert_pivot_2 3 8 0 1
cert_heightProof 4
cert_coverFacet 0 806
cert_cover_5 0 1 0 1 4 7 290 806 1
cert_coverFacet 1 426
cert_cover_5 1 2 0 2 4 6 162 426 1
cert_coverFacet 2 242
cert_cover_5 2 0 0 3 4 6 114 242 3
cert_coverFacet 3 626
cert_cover_5 3 0 0 3 4 8 114 626 3
cert_coverFacet 4 786
cert_cover_2 4 3 0 7 8 274 786 3
cert_coverFacet 5 236
cert_cover_5 5 3 1 2 4 5 44 236 3
cert_coverFacet 6 300
cert_cover_2 6 2 1 4 7 44 300 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m13e11q2_0003

end
end BundlePart19

section BundlePart20
/- Source: ProjectionCertificates/R_m13e11q2_0004.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m13e11q2_0004

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [779, 709, 837, 345, 665, 241, 806, 122, 538, 362, 562, 692, 484, 581, 25, 265, 521, 81, 145, 193, 321, 641, 769, 26, 106, 266, 522, 50, 530, 290, 546, 770, 164, 292, 548, 196, 324, 644, 772, 88, 536, 328, 112, 176, 560, 656, 224, 352]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_779, vertices_709, vertices_837, vertices_345, vertices_665, vertices_241, vertices_806, vertices_122, vertices_538, vertices_362, vertices_562, vertices_692, vertices_484] (by decide +kernel)
  polygons := literalFinset [vertices_581, vertices_25, vertices_265, vertices_521, vertices_81, vertices_145, vertices_193, vertices_321, vertices_641, vertices_769, vertices_26, vertices_106, vertices_266, vertices_522, vertices_50, vertices_530, vertices_290, vertices_546, vertices_770, vertices_164, vertices_292, vertices_548, vertices_196, vertices_324, vertices_644, vertices_772, vertices_88, vertices_536, vertices_328, vertices_112, vertices_176, vertices_560, vertices_656, vertices_224, vertices_352] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_779), (false, vertices_709), (false, vertices_837), (false, vertices_345), (false, vertices_665), (false, vertices_241), (true, vertices_26), (true, vertices_106), (true, vertices_50), (true, vertices_530), (true, vertices_290), (true, vertices_546), (true, vertices_164), (true, vertices_292), (true, vertices_548), (true, vertices_560), (true, vertices_352)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 10 13 16 19 21 22 23 24 25
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_779) then 11 else
  if p.val = (false, vertices_709) then 14 else
  if p.val = (false, vertices_837) then 15 else
  if p.val = (false, vertices_345) then 17 else
  if p.val = (false, vertices_665) then 18 else
  if p.val = (false, vertices_241) then 20 else
  if p.val = (true, vertices_26) then 0 else
  if p.val = (true, vertices_106) then 12 else
  if p.val = (true, vertices_50) then 1 else
  if p.val = (true, vertices_530) then 2 else
  if p.val = (true, vertices_290) then 3 else
  if p.val = (true, vertices_546) then 4 else
  if p.val = (true, vertices_164) then 5 else
  if p.val = (true, vertices_292) then 6 else
  if p.val = (true, vertices_548) then 7 else
  if p.val = (true, vertices_560) then 8 else
  if p.val = (true, vertices_352) then 9 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_26), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_50), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_530), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_290), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_546), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_164), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_292), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_548), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_560), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_352), by decide +kernel⟩
  | 10 => Sum.inl 0
  | 11 => Sum.inr ⟨(false, vertices_779), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_106), by decide +kernel⟩
  | 13 => Sum.inl 1
  | 14 => Sum.inr ⟨(false, vertices_709), by decide +kernel⟩
  | 15 => Sum.inr ⟨(false, vertices_837), by decide +kernel⟩
  | 16 => Sum.inl 2
  | 17 => Sum.inr ⟨(false, vertices_345), by decide +kernel⟩
  | 18 => Sum.inr ⟨(false, vertices_665), by decide +kernel⟩
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
cert_row_2 0 0 2 4 5 106
cert_row_4 1 0 1 4 7 8 806 290 1
cert_row_4 2 1 3 4 6 8 692 164 1
cert_row_4 3 1 4 5 6 7 484 164 2
cert_rows
cert_pivot_2 2 0 3 1
cert_heightProof 4
cert_coverFacet 0 806
cert_cover_5 0 1 0 1 4 7 290 806 1
cert_coverFacet 1 122
cert_cover_5 1 0 0 2 3 4 26 122 3
cert_coverFacet 2 538
cert_cover_2 2 2 0 3 8 26 538 3
cert_coverFacet 3 362
cert_cover_5 3 0 0 2 4 7 106 362 3
cert_coverFacet 4 562
cert_cover_2 4 3 0 4 8 50 562 3
cert_coverFacet 5 692
cert_cover_5 5 2 1 3 4 6 164 692 1
cert_coverFacet 6 484
cert_cover_5 6 3 1 4 5 6 164 484 2
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m13e11q2_0004

end
end BundlePart20

section BundlePart21
/- Source: ProjectionCertificates/R_m13e11q2_0005.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m13e11q2_0005

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [563, 789, 901, 313, 681, 457, 598, 362, 618, 306, 338, 716, 468, 773, 41, 137, 265, 49, 273, 529, 545, 385, 641, 106, 50, 82, 274, 530, 290, 546, 322, 578, 84, 276, 532, 196, 580, 388, 644, 296, 552, 200, 328, 584, 648, 304, 336, 448]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_563, vertices_789, vertices_901, vertices_313, vertices_681, vertices_457, vertices_598, vertices_362, vertices_618, vertices_306, vertices_338, vertices_716, vertices_468] (by decide +kernel)
  polygons := literalFinset [vertices_773, vertices_41, vertices_137, vertices_265, vertices_49, vertices_273, vertices_529, vertices_545, vertices_385, vertices_641, vertices_106, vertices_50, vertices_82, vertices_274, vertices_530, vertices_290, vertices_546, vertices_322, vertices_578, vertices_84, vertices_276, vertices_532, vertices_196, vertices_580, vertices_388, vertices_644, vertices_296, vertices_552, vertices_200, vertices_328, vertices_584, vertices_648, vertices_304, vertices_336, vertices_448] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_563), (false, vertices_789), (false, vertices_901), (false, vertices_313), (false, vertices_681), (false, vertices_457), (true, vertices_106), (true, vertices_82), (true, vertices_274), (true, vertices_290), (true, vertices_322), (true, vertices_578), (true, vertices_84), (true, vertices_196), (true, vertices_580), (true, vertices_584), (true, vertices_336)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 10 13 16 20 21 22 23 24 25
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_563) then 11 else
  if p.val = (false, vertices_789) then 14 else
  if p.val = (false, vertices_901) then 15 else
  if p.val = (false, vertices_313) then 17 else
  if p.val = (false, vertices_681) then 18 else
  if p.val = (false, vertices_457) then 19 else
  if p.val = (true, vertices_106) then 12 else
  if p.val = (true, vertices_82) then 0 else
  if p.val = (true, vertices_274) then 1 else
  if p.val = (true, vertices_290) then 2 else
  if p.val = (true, vertices_322) then 3 else
  if p.val = (true, vertices_578) then 4 else
  if p.val = (true, vertices_84) then 5 else
  if p.val = (true, vertices_196) then 6 else
  if p.val = (true, vertices_580) then 7 else
  if p.val = (true, vertices_584) then 8 else
  if p.val = (true, vertices_336) then 9 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_82), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_274), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_290), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_322), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_578), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_84), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_196), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_580), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_584), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_336), by decide +kernel⟩
  | 10 => Sum.inl 0
  | 11 => Sum.inr ⟨(false, vertices_563), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_106), by decide +kernel⟩
  | 13 => Sum.inl 1
  | 14 => Sum.inr ⟨(false, vertices_789), by decide +kernel⟩
  | 15 => Sum.inr ⟨(false, vertices_901), by decide +kernel⟩
  | 16 => Sum.inl 2
  | 17 => Sum.inr ⟨(false, vertices_313), by decide +kernel⟩
  | 18 => Sum.inr ⟨(false, vertices_681), by decide +kernel⟩
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
cert_row_2 0 0 2 4 5 106
cert_row_4 1 0 1 3 5 8 598 82 1
cert_row_4 2 1 2 5 6 8 716 196 1
cert_row_4 3 1 3 5 6 7 468 84 3
cert_rows
cert_pivot_2 4 0 2 1
cert_heightProof 4
cert_coverFacet 0 598
cert_cover_5 0 1 0 1 3 5 82 598 1
cert_coverFacet 1 362
cert_cover_5 1 0 0 2 4 7 106 362 3
cert_coverFacet 2 618
cert_cover_5 2 0 0 2 4 8 106 618 3
cert_coverFacet 3 306
cert_cover_2 3 3 0 4 7 50 306 3
cert_coverFacet 4 338
cert_cover_2 4 3 0 5 7 82 338 3
cert_coverFacet 5 716
cert_cover_5 5 2 1 2 5 6 196 716 1
cert_coverFacet 6 468
cert_cover_5 6 3 1 3 5 6 84 468 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m13e11q2_0005

end
end BundlePart21

section BundlePart22
/- Source: ProjectionCertificates/R_m13e11q2_0006.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m13e11q2_0006

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [47, 155, 659, 803, 141, 357, 901, 122, 626, 108, 460, 728, 992, 11, 147, 35, 515, 13, 37, 133, 261, 137, 289, 641, 769, 26, 42, 114, 530, 546, 44, 76, 140, 100, 324, 388, 88, 152, 104, 200, 592, 656, 352, 608, 800, 448, 704, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_47, vertices_155, vertices_659, vertices_803, vertices_141, vertices_357, vertices_901, vertices_122, vertices_626, vertices_108, vertices_460, vertices_728, vertices_992] (by decide +kernel)
  polygons := literalFinset [vertices_11, vertices_147, vertices_35, vertices_515, vertices_13, vertices_37, vertices_133, vertices_261, vertices_137, vertices_289, vertices_641, vertices_769, vertices_26, vertices_42, vertices_114, vertices_530, vertices_546, vertices_44, vertices_76, vertices_140, vertices_100, vertices_324, vertices_388, vertices_88, vertices_152, vertices_104, vertices_200, vertices_592, vertices_656, vertices_352, vertices_608, vertices_800, vertices_448, vertices_704, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_47), (false, vertices_155), (false, vertices_659), (false, vertices_803), (false, vertices_141), (false, vertices_357), (false, vertices_901), (true, vertices_114), (true, vertices_76), (true, vertices_88), (true, vertices_104), (true, vertices_200), (true, vertices_592), (true, vertices_608), (true, vertices_448), (true, vertices_704)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 17 9 13 20 14 21 22 23 24
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_47) then 10 else
  if p.val = (false, vertices_155) then 18 else
  if p.val = (false, vertices_659) then 19 else
  if p.val = (false, vertices_803) then 15 else
  if p.val = (false, vertices_141) then 0 else
  if p.val = (false, vertices_357) then 11 else
  if p.val = (false, vertices_901) then 12 else
  if p.val = (true, vertices_114) then 16 else
  if p.val = (true, vertices_76) then 1 else
  if p.val = (true, vertices_88) then 2 else
  if p.val = (true, vertices_104) then 3 else
  if p.val = (true, vertices_200) then 4 else
  if p.val = (true, vertices_592) then 5 else
  if p.val = (true, vertices_608) then 6 else
  if p.val = (true, vertices_448) then 7 else
  if p.val = (true, vertices_704) then 8 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_141), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_76), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_88), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_104), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_200), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_592), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_608), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_448), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_704), by decide +kernel⟩
  | 9 => Sum.inl 1
  | 10 => Sum.inr ⟨(false, vertices_47), by decide +kernel⟩
  | 11 => Sum.inr ⟨(false, vertices_357), by decide +kernel⟩
  | 12 => Sum.inr ⟨(false, vertices_901), by decide +kernel⟩
  | 13 => Sum.inl 2
  | 14 => Sum.inl 4
  | 15 => Sum.inr ⟨(false, vertices_803), by decide +kernel⟩
  | 16 => Sum.inr ⟨(true, vertices_114), by decide +kernel⟩
  | 17 => Sum.inl 0
  | 18 => Sum.inr ⟨(false, vertices_155), by decide +kernel⟩
  | 19 => Sum.inr ⟨(false, vertices_659), by decide +kernel⟩
  | 20 => Sum.inl 3
  | 21 => Sum.inl 5
  | 22 => Sum.inl 6
  | 23 => Sum.inl 7
  | 24 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 3 4 5 114
cert_row_4 1 1 2 5 6 7 460 76 3
cert_row_4 2 2 3 5 6 8 728 88 3
cert_row_4 3 4 5 6 7 8 992 352 2
cert_rows
cert_pivot_2 0 1 2 4
cert_heightProof 4
cert_coverFacet 0 122
cert_cover_5 0 0 0 2 3 4 26 122 3
cert_coverFacet 1 626
cert_cover_5 1 0 0 3 4 8 114 626 3
cert_coverFacet 2 108
cert_cover_2 2 2 1 4 5 44 108 3
cert_coverFacet 3 460
cert_cover_5 3 1 1 2 5 6 76 460 3
cert_coverFacet 4 728
cert_cover_5 4 2 2 3 5 6 88 728 3
cert_coverFacet 5 992
cert_cover_5 5 3 4 5 6 7 352 992 2
cert_coveringFacets
cert_coveringProof_6
cert_certificate 4 6
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m13e11q2_0006

end
end BundlePart22

section BundlePart23
/- Source: ProjectionCertificates/R_m13e11q2_0007.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m13e11q2_0007

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [55, 535, 781, 421, 689, 961, 110, 526, 842, 114, 722, 364, 496, 23, 37, 261, 517, 49, 529, 161, 385, 641, 769, 14, 38, 518, 74, 522, 50, 82, 530, 98, 578, 108, 268, 524, 292, 328, 776, 112, 176, 208, 656, 352, 416, 448, 704, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_55, vertices_535, vertices_781, vertices_421, vertices_689, vertices_961, vertices_110, vertices_526, vertices_842, vertices_114, vertices_722, vertices_364, vertices_496] (by decide +kernel)
  polygons := literalFinset [vertices_23, vertices_37, vertices_261, vertices_517, vertices_49, vertices_529, vertices_161, vertices_385, vertices_641, vertices_769, vertices_14, vertices_38, vertices_518, vertices_74, vertices_522, vertices_50, vertices_82, vertices_530, vertices_98, vertices_578, vertices_108, vertices_268, vertices_524, vertices_292, vertices_328, vertices_776, vertices_112, vertices_176, vertices_208, vertices_656, vertices_352, vertices_416, vertices_448, vertices_704, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_55), (false, vertices_535), (false, vertices_781), (false, vertices_421), (false, vertices_689), (false, vertices_961), (true, vertices_14), (true, vertices_74), (true, vertices_522), (true, vertices_82), (true, vertices_98), (true, vertices_578), (true, vertices_108), (true, vertices_328), (true, vertices_112), (true, vertices_208), (true, vertices_352)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 10 13 17 18 20 21 23 24 25
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_55) then 11 else
  if p.val = (false, vertices_535) then 12 else
  if p.val = (false, vertices_781) then 14 else
  if p.val = (false, vertices_421) then 15 else
  if p.val = (false, vertices_689) then 19 else
  if p.val = (false, vertices_961) then 22 else
  if p.val = (true, vertices_14) then 0 else
  if p.val = (true, vertices_74) then 1 else
  if p.val = (true, vertices_522) then 2 else
  if p.val = (true, vertices_82) then 3 else
  if p.val = (true, vertices_98) then 4 else
  if p.val = (true, vertices_578) then 5 else
  if p.val = (true, vertices_108) then 16 else
  if p.val = (true, vertices_328) then 6 else
  if p.val = (true, vertices_112) then 7 else
  if p.val = (true, vertices_208) then 8 else
  if p.val = (true, vertices_352) then 9 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_14), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_74), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_522), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_82), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_98), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_578), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_328), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_112), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_208), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_352), by decide +kernel⟩
  | 10 => Sum.inl 0
  | 11 => Sum.inr ⟨(false, vertices_55), by decide +kernel⟩
  | 12 => Sum.inr ⟨(false, vertices_535), by decide +kernel⟩
  | 13 => Sum.inl 1
  | 14 => Sum.inr ⟨(false, vertices_781), by decide +kernel⟩
  | 15 => Sum.inr ⟨(false, vertices_421), by decide +kernel⟩
  | 16 => Sum.inr ⟨(true, vertices_108), by decide +kernel⟩
  | 17 => Sum.inl 2
  | 18 => Sum.inl 3
  | 19 => Sum.inr ⟨(false, vertices_689), by decide +kernel⟩
  | 20 => Sum.inl 4
  | 21 => Sum.inl 5
  | 22 => Sum.inr ⟨(false, vertices_961), by decide +kernel⟩
  | 23 => Sum.inl 6
  | 24 => Sum.inl 7
  | 25 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 1 2 4 5 108
cert_row_4 1 0 2 5 7 8 842 74 3
cert_row_4 2 0 3 5 6 8 722 82 3
cert_row_4 3 3 4 5 6 7 496 112 3
cert_rows
cert_pivot_2 1 2 0 3
cert_heightProof 4
cert_coverFacet 0 110
cert_cover_5 0 0 0 1 2 4 14 110 3
cert_coverFacet 1 526
cert_cover_2 1 1 0 2 8 14 526 3
cert_coverFacet 2 842
cert_cover_5 2 1 0 2 5 7 74 842 3
cert_coverFacet 3 114
cert_cover_2 3 3 0 4 5 50 114 3
cert_coverFacet 4 722
cert_cover_5 4 2 0 3 5 6 82 722 3
cert_coverFacet 5 364
cert_cover_5 5 0 1 2 4 7 108 364 3
cert_coverFacet 6 496
cert_cover_5 6 3 3 4 5 6 112 496 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m13e11q2_0007

end
end BundlePart23

section BundlePart24
/- Source: ProjectionCertificates/R_m13e11q2_0008.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m13e11q2_0008

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [51, 403, 675, 901, 121, 345, 809, 598, 662, 618, 114, 844, 468, 19, 35, 131, 89, 41, 265, 49, 273, 545, 385, 641, 769, 534, 50, 82, 146, 98, 546, 578, 642, 84, 148, 324, 580, 388, 644, 772, 104, 552, 328, 584, 776, 112, 336, 400]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_51, vertices_403, vertices_675, vertices_901, vertices_121, vertices_345, vertices_809, vertices_598, vertices_662, vertices_618, vertices_114, vertices_844, vertices_468] (by decide +kernel)
  polygons := literalFinset [vertices_19, vertices_35, vertices_131, vertices_89, vertices_41, vertices_265, vertices_49, vertices_273, vertices_545, vertices_385, vertices_641, vertices_769, vertices_534, vertices_50, vertices_82, vertices_146, vertices_98, vertices_546, vertices_578, vertices_642, vertices_84, vertices_148, vertices_324, vertices_580, vertices_388, vertices_644, vertices_772, vertices_104, vertices_552, vertices_328, vertices_584, vertices_776, vertices_112, vertices_336, vertices_400] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_51), (false, vertices_403), (false, vertices_675), (false, vertices_901), (false, vertices_121), (false, vertices_345), (false, vertices_809), (true, vertices_534), (true, vertices_82), (true, vertices_98), (true, vertices_578), (true, vertices_84), (true, vertices_148), (true, vertices_324), (true, vertices_580), (true, vertices_584)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 9 13 15 19 20 21 22 23 24
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_51) then 0 else
  if p.val = (false, vertices_403) then 10 else
  if p.val = (false, vertices_675) then 11 else
  if p.val = (false, vertices_901) then 14 else
  if p.val = (false, vertices_121) then 16 else
  if p.val = (false, vertices_345) then 17 else
  if p.val = (false, vertices_809) then 18 else
  if p.val = (true, vertices_534) then 12 else
  if p.val = (true, vertices_82) then 1 else
  if p.val = (true, vertices_98) then 2 else
  if p.val = (true, vertices_578) then 3 else
  if p.val = (true, vertices_84) then 4 else
  if p.val = (true, vertices_148) then 5 else
  if p.val = (true, vertices_324) then 6 else
  if p.val = (true, vertices_580) then 7 else
  if p.val = (true, vertices_584) then 8 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_51), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_82), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_98), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_578), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_84), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_148), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_324), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_580), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_584), by decide +kernel⟩
  | 9 => Sum.inl 0
  | 10 => Sum.inr ⟨(false, vertices_403), by decide +kernel⟩
  | 11 => Sum.inr ⟨(false, vertices_675), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_534), by decide +kernel⟩
  | 13 => Sum.inl 1
  | 14 => Sum.inr ⟨(false, vertices_901), by decide +kernel⟩
  | 15 => Sum.inl 2
  | 16 => Sum.inr ⟨(false, vertices_121), by decide +kernel⟩
  | 17 => Sum.inr ⟨(false, vertices_345), by decide +kernel⟩
  | 18 => Sum.inr ⟨(false, vertices_809), by decide +kernel⟩
  | 19 => Sum.inl 3
  | 20 => Sum.inl 4
  | 21 => Sum.inl 5
  | 22 => Sum.inl 6
  | 23 => Sum.inl 7
  | 24 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 2 4 5 8 618 98 1
cert_row_2 1 0 1 3 8 534
cert_row_4 2 1 2 5 7 8 844 324 1
cert_row_4 3 1 3 5 6 7 468 84 3
cert_rows
cert_pivot_2 4 0 2 1
cert_heightProof 4
cert_coverFacet 0 598
cert_cover_5 0 1 0 1 3 5 534 598 3
cert_coverFacet 1 662
cert_cover_5 1 1 0 1 3 6 534 662 3
cert_coverFacet 2 618
cert_cover_5 2 0 0 2 4 5 98 618 1
cert_coverFacet 3 114
cert_cover_2 3 3 0 4 5 50 114 3
cert_coverFacet 4 844
cert_cover_5 4 2 1 2 5 7 324 844 1
cert_coverFacet 5 468
cert_cover_5 5 3 1 3 5 6 84 468 3
cert_coveringFacets
cert_coveringProof_6
cert_certificate 4 6
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m13e11q2_0008

end
end BundlePart24

section BundlePart25
/- Source: ProjectionCertificates/R_m13e11q2_0010.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m13e11q2_0010

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [55, 151, 557, 589, 453, 361, 433, 550, 710, 562, 914, 824, 968, 23, 525, 37, 69, 133, 41, 73, 49, 145, 289, 321, 385, 38, 134, 518, 50, 146, 530, 546, 642, 548, 196, 580, 296, 552, 328, 584, 776, 304, 560, 400, 784, 448, 704, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_55, vertices_151, vertices_557, vertices_589, vertices_453, vertices_361, vertices_433, vertices_550, vertices_710, vertices_562, vertices_914, vertices_824, vertices_968] (by decide +kernel)
  polygons := literalFinset [vertices_23, vertices_525, vertices_37, vertices_69, vertices_133, vertices_41, vertices_73, vertices_49, vertices_145, vertices_289, vertices_321, vertices_385, vertices_38, vertices_134, vertices_518, vertices_50, vertices_146, vertices_530, vertices_546, vertices_642, vertices_548, vertices_196, vertices_580, vertices_296, vertices_552, vertices_328, vertices_584, vertices_776, vertices_304, vertices_560, vertices_400, vertices_784, vertices_448, vertices_704, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_55), (false, vertices_151), (false, vertices_557), (false, vertices_589), (false, vertices_453), (false, vertices_361), (false, vertices_433), (true, vertices_518), (true, vertices_530), (true, vertices_546), (true, vertices_642), (true, vertices_776), (true, vertices_560), (true, vertices_784), (true, vertices_704), (true, vertices_896)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 9 12 16 18 20 21 22 23 24
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_55) then 10 else
  if p.val = (false, vertices_151) then 11 else
  if p.val = (false, vertices_557) then 13 else
  if p.val = (false, vertices_589) then 14 else
  if p.val = (false, vertices_453) then 15 else
  if p.val = (false, vertices_361) then 17 else
  if p.val = (false, vertices_433) then 19 else
  if p.val = (true, vertices_518) then 0 else
  if p.val = (true, vertices_530) then 1 else
  if p.val = (true, vertices_546) then 2 else
  if p.val = (true, vertices_642) then 3 else
  if p.val = (true, vertices_776) then 4 else
  if p.val = (true, vertices_560) then 5 else
  if p.val = (true, vertices_784) then 6 else
  if p.val = (true, vertices_704) then 7 else
  if p.val = (true, vertices_896) then 8 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_518), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_530), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_546), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_642), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_776), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_560), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_784), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_704), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_896), by decide +kernel⟩
  | 9 => Sum.inl 0
  | 10 => Sum.inr ⟨(false, vertices_55), by decide +kernel⟩
  | 11 => Sum.inr ⟨(false, vertices_151), by decide +kernel⟩
  | 12 => Sum.inl 1
  | 13 => Sum.inr ⟨(false, vertices_557), by decide +kernel⟩
  | 14 => Sum.inr ⟨(false, vertices_589), by decide +kernel⟩
  | 15 => Sum.inr ⟨(false, vertices_453), by decide +kernel⟩
  | 16 => Sum.inl 2
  | 17 => Sum.inr ⟨(false, vertices_361), by decide +kernel⟩
  | 18 => Sum.inl 3
  | 19 => Sum.inr ⟨(false, vertices_433), by decide +kernel⟩
  | 20 => Sum.inl 4
  | 21 => Sum.inl 5
  | 22 => Sum.inl 6
  | 23 => Sum.inl 7
  | 24 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 5 6 8 710 134 2
cert_row_4 1 0 3 6 7 8 914 146 3
cert_row_4 2 2 3 4 7 8 824 296 1
cert_row_4 3 2 5 6 7 8 968 328 2
cert_rows
cert_pivot_2 1 0 3 2
cert_heightProof 4
cert_coverFacet 0 550
cert_cover_2 0 1 0 4 8 38 550 3
cert_coverFacet 1 710
cert_cover_5 1 0 0 1 5 6 134 710 2
cert_coverFacet 2 562
cert_cover_2 2 3 0 4 8 50 562 3
cert_coverFacet 3 914
cert_cover_5 3 1 0 3 6 7 146 914 3
cert_coverFacet 4 824
cert_cover_5 4 2 2 3 4 7 296 824 1
cert_coverFacet 5 968
cert_cover_5 5 3 2 5 6 7 328 968 2
cert_coveringFacets
cert_coveringProof_6
cert_certificate 4 6
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m13e11q2_0010

end
end BundlePart25

section BundlePart26
/- Source: ProjectionCertificates/R_m13e11q2_0011.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m13e11q2_0011

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [583, 263, 675, 291, 453, 713, 433, 310, 566, 796, 844, 696, 472, 7, 35, 259, 515, 69, 261, 161, 289, 193, 577, 385, 641, 54, 262, 518, 290, 546, 780, 276, 532, 324, 580, 152, 280, 536, 200, 328, 584, 648, 176, 304, 560, 400, 672, 448]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_583, vertices_263, vertices_675, vertices_291, vertices_453, vertices_713, vertices_433, vertices_310, vertices_566, vertices_796, vertices_844, vertices_696, vertices_472] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_35, vertices_259, vertices_515, vertices_69, vertices_261, vertices_161, vertices_289, vertices_193, vertices_577, vertices_385, vertices_641, vertices_54, vertices_262, vertices_518, vertices_290, vertices_546, vertices_780, vertices_276, vertices_532, vertices_324, vertices_580, vertices_152, vertices_280, vertices_536, vertices_200, vertices_328, vertices_584, vertices_648, vertices_176, vertices_304, vertices_560, vertices_400, vertices_672, vertices_448] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_583), (false, vertices_263), (false, vertices_675), (false, vertices_291), (false, vertices_453), (false, vertices_713), (false, vertices_433), (true, vertices_54), (true, vertices_780), (true, vertices_276), (true, vertices_532), (true, vertices_152), (true, vertices_280), (true, vertices_536), (true, vertices_328), (true, vertices_560)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 9 13 16 18 20 21 22 23 24
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_583) then 10 else
  if p.val = (false, vertices_263) then 0 else
  if p.val = (false, vertices_675) then 11 else
  if p.val = (false, vertices_291) then 1 else
  if p.val = (false, vertices_453) then 14 else
  if p.val = (false, vertices_713) then 17 else
  if p.val = (false, vertices_433) then 19 else
  if p.val = (true, vertices_54) then 12 else
  if p.val = (true, vertices_780) then 15 else
  if p.val = (true, vertices_276) then 2 else
  if p.val = (true, vertices_532) then 3 else
  if p.val = (true, vertices_152) then 4 else
  if p.val = (true, vertices_280) then 5 else
  if p.val = (true, vertices_536) then 6 else
  if p.val = (true, vertices_328) then 7 else
  if p.val = (true, vertices_560) then 8 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_263), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_291), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_276), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_532), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_152), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_280), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_536), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_328), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_560), by decide +kernel⟩
  | 9 => Sum.inl 0
  | 10 => Sum.inr ⟨(false, vertices_583), by decide +kernel⟩
  | 11 => Sum.inr ⟨(false, vertices_675), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_54), by decide +kernel⟩
  | 13 => Sum.inl 1
  | 14 => Sum.inr ⟨(false, vertices_453), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_780), by decide +kernel⟩
  | 16 => Sum.inl 2
  | 17 => Sum.inr ⟨(false, vertices_713), by decide +kernel⟩
  | 18 => Sum.inl 3
  | 19 => Sum.inr ⟨(false, vertices_433), by decide +kernel⟩
  | 20 => Sum.inl 4
  | 21 => Sum.inl 5
  | 22 => Sum.inl 6
  | 23 => Sum.inl 7
  | 24 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 1 3 4 54
cert_row_2 1 1 2 7 8 780
cert_row_4 2 2 3 4 6 8 696 152 2
cert_row_4 3 2 3 5 6 7 472 152 2
cert_rows
cert_pivot_2 0 1 4 2
cert_heightProof 4
cert_coverFacet 0 310
cert_cover_5 0 0 0 1 3 7 54 310 3
cert_coverFacet 1 566
cert_cover_5 1 0 0 1 3 8 54 566 3
cert_coverFacet 2 796
cert_cover_5 2 1 1 2 3 7 780 796 2
cert_coverFacet 3 844
cert_cover_5 3 1 1 2 5 7 780 844 2
cert_coverFacet 4 696
cert_cover_5 4 2 2 3 4 6 152 696 2
cert_coverFacet 5 472
cert_cover_5 5 3 2 3 5 6 152 472 2
cert_coveringFacets
cert_coveringProof_6
cert_certificate 4 6
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m13e11q2_0011

end
end BundlePart26

section BundlePart27
/- Source: ProjectionCertificates/R_m13e11q2_0012.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m13e11q2_0012

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [151, 171, 299, 787, 533, 229, 805, 218, 346, 724, 612, 488, 880, 43, 19, 131, 259, 21, 37, 133, 517, 529, 161, 289, 769, 90, 138, 266, 146, 274, 148, 532, 100, 548, 196, 580, 168, 296, 200, 328, 208, 336, 592, 784, 224, 352, 608, 800]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_151, vertices_171, vertices_299, vertices_787, vertices_533, vertices_229, vertices_805, vertices_218, vertices_346, vertices_724, vertices_612, vertices_488, vertices_880] (by decide +kernel)
  polygons := literalFinset [vertices_43, vertices_19, vertices_131, vertices_259, vertices_21, vertices_37, vertices_133, vertices_517, vertices_529, vertices_161, vertices_289, vertices_769, vertices_90, vertices_138, vertices_266, vertices_146, vertices_274, vertices_148, vertices_532, vertices_100, vertices_548, vertices_196, vertices_580, vertices_168, vertices_296, vertices_200, vertices_328, vertices_208, vertices_336, vertices_592, vertices_784, vertices_224, vertices_352, vertices_608, vertices_800] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_151), (false, vertices_171), (false, vertices_299), (false, vertices_787), (false, vertices_533), (false, vertices_229), (false, vertices_805), (true, vertices_90), (true, vertices_580), (true, vertices_200), (true, vertices_328), (true, vertices_208), (true, vertices_336), (true, vertices_592), (true, vertices_352), (true, vertices_608)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 16 9 19 13 20 21 22 23 24
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_151) then 10 else
  if p.val = (false, vertices_171) then 17 else
  if p.val = (false, vertices_299) then 18 else
  if p.val = (false, vertices_787) then 14 else
  if p.val = (false, vertices_533) then 0 else
  if p.val = (false, vertices_229) then 11 else
  if p.val = (false, vertices_805) then 12 else
  if p.val = (true, vertices_90) then 15 else
  if p.val = (true, vertices_580) then 1 else
  if p.val = (true, vertices_200) then 2 else
  if p.val = (true, vertices_328) then 3 else
  if p.val = (true, vertices_208) then 4 else
  if p.val = (true, vertices_336) then 5 else
  if p.val = (true, vertices_592) then 6 else
  if p.val = (true, vertices_352) then 7 else
  if p.val = (true, vertices_608) then 8 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_533), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_580), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_200), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_328), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_208), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_336), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_592), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_352), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_608), by decide +kernel⟩
  | 9 => Sum.inl 1
  | 10 => Sum.inr ⟨(false, vertices_151), by decide +kernel⟩
  | 11 => Sum.inr ⟨(false, vertices_229), by decide +kernel⟩
  | 12 => Sum.inr ⟨(false, vertices_805), by decide +kernel⟩
  | 13 => Sum.inl 3
  | 14 => Sum.inr ⟨(false, vertices_787), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_90), by decide +kernel⟩
  | 16 => Sum.inl 0
  | 17 => Sum.inr ⟨(false, vertices_171), by decide +kernel⟩
  | 18 => Sum.inr ⟨(false, vertices_299), by decide +kernel⟩
  | 19 => Sum.inl 2
  | 20 => Sum.inl 4
  | 21 => Sum.inl 5
  | 22 => Sum.inl 6
  | 23 => Sum.inl 7
  | 24 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 2 3 5 90
cert_row_4 1 1 3 5 6 8 724 148 2
cert_row_4 2 2 4 5 6 7 488 168 2
cert_row_4 3 3 4 5 7 8 880 336 1
cert_rows
cert_pivot_2 0 1 2 3
cert_heightProof 4
cert_coverFacet 0 218
cert_cover_5 0 0 0 2 3 6 90 218 3
cert_coverFacet 1 346
cert_cover_5 1 0 0 2 3 7 90 346 3
cert_coverFacet 2 724
cert_cover_5 2 1 1 3 5 6 148 724 2
cert_coverFacet 3 612
cert_cover_2 3 4 1 5 8 100 612 3
cert_coverFacet 4 488
cert_cover_5 4 2 2 4 5 6 168 488 2
cert_coverFacet 5 880
cert_cover_5 5 3 3 4 5 7 336 880 1
cert_coveringFacets
cert_coveringProof_6
cert_certificate 4 6
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m13e11q2_0012

end
end BundlePart27

section BundlePart28
/- Source: ProjectionCertificates/R_m13e11q2_0013.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m13e11q2_0013

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [551, 155, 651, 51, 309, 901, 465, 90, 618, 370, 484, 740, 728, 139, 19, 35, 515, 37, 261, 517, 49, 145, 273, 385, 641, 26, 74, 522, 50, 82, 98, 546, 228, 292, 548, 388, 644, 88, 152, 584, 648, 304, 208, 336, 352, 608, 448, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_551, vertices_155, vertices_651, vertices_51, vertices_309, vertices_901, vertices_465, vertices_90, vertices_618, vertices_370, vertices_484, vertices_740, vertices_728] (by decide +kernel)
  polygons := literalFinset [vertices_139, vertices_19, vertices_35, vertices_515, vertices_37, vertices_261, vertices_517, vertices_49, vertices_145, vertices_273, vertices_385, vertices_641, vertices_26, vertices_74, vertices_522, vertices_50, vertices_82, vertices_98, vertices_546, vertices_228, vertices_292, vertices_548, vertices_388, vertices_644, vertices_88, vertices_152, vertices_584, vertices_648, vertices_304, vertices_208, vertices_336, vertices_352, vertices_608, vertices_448, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_551), (false, vertices_155), (false, vertices_651), (false, vertices_51), (false, vertices_309), (false, vertices_901), (false, vertices_465), (true, vertices_74), (true, vertices_82), (true, vertices_98), (true, vertices_228), (true, vertices_88), (true, vertices_584), (true, vertices_352), (true, vertices_608), (true, vertices_704)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 9 13 17 18 20 21 22 23 24
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_551) then 10 else
  if p.val = (false, vertices_155) then 11 else
  if p.val = (false, vertices_651) then 12 else
  if p.val = (false, vertices_51) then 0 else
  if p.val = (false, vertices_309) then 14 else
  if p.val = (false, vertices_901) then 15 else
  if p.val = (false, vertices_465) then 19 else
  if p.val = (true, vertices_74) then 1 else
  if p.val = (true, vertices_82) then 2 else
  if p.val = (true, vertices_98) then 3 else
  if p.val = (true, vertices_228) then 16 else
  if p.val = (true, vertices_88) then 4 else
  if p.val = (true, vertices_584) then 5 else
  if p.val = (true, vertices_352) then 6 else
  if p.val = (true, vertices_608) then 7 else
  if p.val = (true, vertices_704) then 8 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_51), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_74), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_82), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_98), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_88), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_584), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_352), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_608), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_704), by decide +kernel⟩
  | 9 => Sum.inl 0
  | 10 => Sum.inr ⟨(false, vertices_551), by decide +kernel⟩
  | 11 => Sum.inr ⟨(false, vertices_155), by decide +kernel⟩
  | 12 => Sum.inr ⟨(false, vertices_651), by decide +kernel⟩
  | 13 => Sum.inl 1
  | 14 => Sum.inr ⟨(false, vertices_309), by decide +kernel⟩
  | 15 => Sum.inr ⟨(false, vertices_901), by decide +kernel⟩
  | 16 => Sum.inr ⟨(true, vertices_228), by decide +kernel⟩
  | 17 => Sum.inl 2
  | 18 => Sum.inl 3
  | 19 => Sum.inr ⟨(false, vertices_465), by decide +kernel⟩
  | 20 => Sum.inl 4
  | 21 => Sum.inl 5
  | 22 => Sum.inl 6
  | 23 => Sum.inl 7
  | 24 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 1 4 5 6 228
cert_row_4 1 0 3 4 5 7 370 50 3
cert_row_4 2 0 2 4 5 8 618 74 2
cert_row_4 3 2 3 5 6 8 728 88 3
cert_rows
cert_pivot_2 1 7 0 2
cert_heightProof 4
cert_coverFacet 0 90
cert_cover_2 0 2 0 3 5 26 90 3
cert_coverFacet 1 618
cert_cover_5 1 2 0 2 4 5 74 618 2
cert_coverFacet 2 370
cert_cover_5 2 1 0 3 4 5 50 370 3
cert_coverFacet 3 484
cert_cover_5 3 0 1 4 5 7 228 484 3
cert_coverFacet 4 740
cert_cover_5 4 0 1 4 5 8 228 740 3
cert_coverFacet 5 728
cert_cover_5 5 3 2 3 5 6 88 728 3
cert_coveringFacets
cert_coveringProof_6
cert_certificate 4 6
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m13e11q2_0013

end
end BundlePart28

section BundlePart29
/- Source: ProjectionCertificates/R_m13e11q2_0015.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m13e11q2_0015

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [295, 341, 597, 677, 665, 433, 334, 590, 550, 410, 682, 418, 856, 85, 37, 261, 517, 145, 273, 529, 161, 289, 641, 78, 38, 262, 518, 138, 266, 522, 162, 290, 546, 386, 548, 324, 580, 152, 280, 536, 328, 584, 648, 336, 592, 400, 416, 672]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_295, vertices_341, vertices_597, vertices_677, vertices_665, vertices_433, vertices_334, vertices_590, vertices_550, vertices_410, vertices_682, vertices_418, vertices_856] (by decide +kernel)
  polygons := literalFinset [vertices_85, vertices_37, vertices_261, vertices_517, vertices_145, vertices_273, vertices_529, vertices_161, vertices_289, vertices_641, vertices_78, vertices_38, vertices_262, vertices_518, vertices_138, vertices_266, vertices_522, vertices_162, vertices_290, vertices_546, vertices_386, vertices_548, vertices_324, vertices_580, vertices_152, vertices_280, vertices_536, vertices_328, vertices_584, vertices_648, vertices_336, vertices_592, vertices_400, vertices_416, vertices_672] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_295), (false, vertices_341), (false, vertices_597), (false, vertices_677), (false, vertices_665), (false, vertices_433), (true, vertices_78), (true, vertices_518), (true, vertices_138), (true, vertices_266), (true, vertices_522), (true, vertices_162), (true, vertices_546), (true, vertices_386), (true, vertices_280), (true, vertices_328), (true, vertices_584)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 10 13 17 19 21 22 23 24 25
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_295) then 11 else
  if p.val = (false, vertices_341) then 14 else
  if p.val = (false, vertices_597) then 15 else
  if p.val = (false, vertices_677) then 16 else
  if p.val = (false, vertices_665) then 18 else
  if p.val = (false, vertices_433) then 20 else
  if p.val = (true, vertices_78) then 12 else
  if p.val = (true, vertices_518) then 0 else
  if p.val = (true, vertices_138) then 1 else
  if p.val = (true, vertices_266) then 2 else
  if p.val = (true, vertices_522) then 3 else
  if p.val = (true, vertices_162) then 4 else
  if p.val = (true, vertices_546) then 5 else
  if p.val = (true, vertices_386) then 6 else
  if p.val = (true, vertices_280) then 7 else
  if p.val = (true, vertices_328) then 8 else
  if p.val = (true, vertices_584) then 9 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_518), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_138), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_266), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_522), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_162), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_546), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_386), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_280), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_328), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_584), by decide +kernel⟩
  | 10 => Sum.inl 0
  | 11 => Sum.inr ⟨(false, vertices_295), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_78), by decide +kernel⟩
  | 13 => Sum.inl 1
  | 14 => Sum.inr ⟨(false, vertices_341), by decide +kernel⟩
  | 15 => Sum.inr ⟨(false, vertices_597), by decide +kernel⟩
  | 16 => Sum.inr ⟨(false, vertices_677), by decide +kernel⟩
  | 17 => Sum.inl 2
  | 18 => Sum.inr ⟨(false, vertices_665), by decide +kernel⟩
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
cert_row_2 0 0 1 2 5 78
cert_row_4 1 0 2 4 6 8 682 138 2
cert_row_4 2 0 2 3 6 7 410 138 2
cert_row_4 3 2 3 5 7 8 856 280 2
cert_rows
cert_pivot_2 1 4 0 2
cert_heightProof 4
cert_coverFacet 0 334
cert_cover_5 0 0 0 1 2 7 78 334 3
cert_coverFacet 1 590
cert_cover_5 1 0 0 1 2 8 78 590 3
cert_coverFacet 2 550
cert_cover_2 2 1 0 4 8 38 550 3
cert_coverFacet 3 410
cert_cover_5 3 2 0 2 3 6 138 410 2
cert_coverFacet 4 682
cert_cover_5 4 1 0 2 4 6 138 682 2
cert_coverFacet 5 418
cert_cover_2 5 4 0 6 7 162 418 3
cert_coverFacet 6 856
cert_cover_5 6 3 2 3 5 7 280 856 2
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m13e11q2_0015

end
end BundlePart29
-- Explicit facial frame witnesses.

-- Public target certificates; internal witness data stays private.
namespace Nonrational.TerminalVerification
open Papers.RationalityTen.ChirotopeDensity.FiniteProjection
open Nonrational.TerminalData
set_option maxRecDepth 100000
set_option maxHeartbeats 0

public theorem projection_0150 : Certifies 150 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m13e10q1_0086.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0151 : Certifies 151 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m13e10q1_0101.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0152 : Certifies 152 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m13e10q1_0105.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0153 : Certifies 153 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m13e10q1_0126.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0154 : Certifies 154 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m13e10q1_0141.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0155 : Certifies 155 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m13e10q1_0151.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0156 : Certifies 156 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m13e11q1_0000.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0157 : Certifies 157 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m13e11q1_0001.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0158 : Certifies 158 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m13e11q1_0002.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0159 : Certifies 159 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m13e11q1_0003.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0160 : Certifies 160 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m13e11q1_0004.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0161 : Certifies 161 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m13e11q1_0005.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0162 : Certifies 162 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m13e11q1_0008.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0163 : Certifies 163 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m13e11q1_0009.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0164 : Certifies 164 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m13e11q1_0010.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0165 : Certifies 165 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m13e11q1_0011.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0166 : Certifies 166 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m13e11q1_0013.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0167 : Certifies 167 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m13e11q2_0000.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0168 : Certifies 168 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m13e11q2_0001.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0169 : Certifies 169 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m13e11q2_0003.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0170 : Certifies 170 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m13e11q2_0004.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0171 : Certifies 171 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m13e11q2_0005.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0172 : Certifies 172 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m13e11q2_0006.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0173 : Certifies 173 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m13e11q2_0007.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0174 : Certifies 174 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m13e11q2_0008.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0175 : Certifies 175 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m13e11q2_0010.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0176 : Certifies 176 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m13e11q2_0011.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0177 : Certifies 177 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m13e11q2_0012.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0178 : Certifies 178 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m13e11q2_0013.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0179 : Certifies 179 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m13e11q2_0015.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem certified_B005 (j : Fin 30) :
    Certifies (150 + j.val) := by
  fin_cases j
  · exact projection_0150
  · exact projection_0151
  · exact projection_0152
  · exact projection_0153
  · exact projection_0154
  · exact projection_0155
  · exact projection_0156
  · exact projection_0157
  · exact projection_0158
  · exact projection_0159
  · exact projection_0160
  · exact projection_0161
  · exact projection_0162
  · exact projection_0163
  · exact projection_0164
  · exact projection_0165
  · exact projection_0166
  · exact projection_0167
  · exact projection_0168
  · exact projection_0169
  · exact projection_0170
  · exact projection_0171
  · exact projection_0172
  · exact projection_0173
  · exact projection_0174
  · exact projection_0175
  · exact projection_0176
  · exact projection_0177
  · exact projection_0178
  · exact projection_0179

end Nonrational.TerminalVerification
