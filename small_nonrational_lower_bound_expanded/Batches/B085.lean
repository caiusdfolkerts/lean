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
/- Source: ProjectionCertificates/R_m15e10q0_0003.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q0_0003

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [611, 157, 557, 709, 121, 465, 782, 314, 554, 482, 706, 898, 284, 916, 368, 13, 133, 517, 25, 41, 81, 145, 97, 545, 193, 577, 42, 266, 522, 98, 290, 546, 194, 578, 386, 642, 770, 28, 268, 524, 148, 276, 644, 772, 56, 280, 552, 112, 304, 336, 400, 352, 448, 704, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_611, vertices_157, vertices_557, vertices_709, vertices_121, vertices_465, vertices_782, vertices_314, vertices_554, vertices_482, vertices_706, vertices_898, vertices_284, vertices_916, vertices_368] (by decide +kernel)
  polygons := literalFinset [vertices_13, vertices_133, vertices_517, vertices_25, vertices_41, vertices_81, vertices_145, vertices_97, vertices_545, vertices_193, vertices_577, vertices_42, vertices_266, vertices_522, vertices_98, vertices_290, vertices_546, vertices_194, vertices_578, vertices_386, vertices_642, vertices_770, vertices_28, vertices_268, vertices_524, vertices_148, vertices_276, vertices_644, vertices_772, vertices_56, vertices_280, vertices_552, vertices_112, vertices_304, vertices_336, vertices_400, vertices_352, vertices_448, vertices_704, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_611), (false, vertices_157), (false, vertices_557), (false, vertices_709), (false, vertices_121), (false, vertices_465), (true, vertices_42), (true, vertices_266), (true, vertices_522), (true, vertices_290), (true, vertices_194), (true, vertices_386), (true, vertices_642), (true, vertices_770), (true, vertices_268), (true, vertices_276), (true, vertices_772), (true, vertices_280), (true, vertices_304), (true, vertices_352), (true, vertices_896)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 17 21 23 25 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_611) then 16 else
  if p.val = (false, vertices_157) then 18 else
  if p.val = (false, vertices_557) then 19 else
  if p.val = (false, vertices_709) then 20 else
  if p.val = (false, vertices_121) then 22 else
  if p.val = (false, vertices_465) then 24 else
  if p.val = (true, vertices_42) then 0 else
  if p.val = (true, vertices_266) then 1 else
  if p.val = (true, vertices_522) then 2 else
  if p.val = (true, vertices_290) then 3 else
  if p.val = (true, vertices_194) then 4 else
  if p.val = (true, vertices_386) then 5 else
  if p.val = (true, vertices_642) then 6 else
  if p.val = (true, vertices_770) then 7 else
  if p.val = (true, vertices_268) then 8 else
  if p.val = (true, vertices_276) then 9 else
  if p.val = (true, vertices_772) then 10 else
  if p.val = (true, vertices_280) then 11 else
  if p.val = (true, vertices_304) then 12 else
  if p.val = (true, vertices_352) then 13 else
  if p.val = (true, vertices_896) then 14 else
  0
cert_priority
cert_nodeAtPriority_68 0 42 1 266 522 290 194 386 642 770 268 276 772 280 304 352 896 611 157 557 709 121 465
cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 4 5 6 7 482 98 3
cert_row_4 1 0 2 3 4 7 314 42 2
cert_row_4 2 0 1 2 7 8 782 266 1
cert_row_4 3 1 3 6 7 8 916 148 3
cert_rows
cert_pivot_2 5 4 0 1
cert_heightProof 4
cert_coverFacet 0 782
cert_cover_5 0 2 0 1 2 7 266 782 1
cert_coverFacet 1 314
cert_cover_5 1 1 0 2 3 4 42 314 2
cert_coverFacet 2 554
cert_cover_2 2 2 0 4 8 42 554 3
cert_coverFacet 3 482
cert_cover_5 3 0 0 4 5 6 98 482 3
cert_coverFacet 4 706
cert_cover_2 4 5 0 6 8 194 706 3
cert_coverFacet 5 898
cert_cover_2 5 6 0 7 8 386 898 3
cert_coverFacet 6 284
cert_cover_2 6 2 1 3 7 28 284 3
cert_coverFacet 7 916
cert_cover_5 7 3 1 3 6 7 148 916 3
cert_coverFacet 8 368
cert_cover_2 8 4 3 5 7 112 368 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q0_0003

end
end BundlePart0

section BundlePart1
/- Source: ProjectionCertificates/R_m15e10q0_0004.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q0_0004

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [611, 157, 589, 677, 345, 241, 782, 362, 586, 434, 674, 898, 284, 916, 368, 13, 133, 517, 25, 73, 81, 145, 97, 161, 545, 577, 74, 266, 522, 98, 162, 290, 546, 578, 386, 642, 770, 28, 268, 524, 148, 276, 644, 772, 280, 328, 584, 112, 176, 304, 336, 400, 352, 672, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_611, vertices_157, vertices_589, vertices_677, vertices_345, vertices_241, vertices_782, vertices_362, vertices_586, vertices_434, vertices_674, vertices_898, vertices_284, vertices_916, vertices_368] (by decide +kernel)
  polygons := literalFinset [vertices_13, vertices_133, vertices_517, vertices_25, vertices_73, vertices_81, vertices_145, vertices_97, vertices_161, vertices_545, vertices_577, vertices_74, vertices_266, vertices_522, vertices_98, vertices_162, vertices_290, vertices_546, vertices_578, vertices_386, vertices_642, vertices_770, vertices_28, vertices_268, vertices_524, vertices_148, vertices_276, vertices_644, vertices_772, vertices_280, vertices_328, vertices_584, vertices_112, vertices_176, vertices_304, vertices_336, vertices_400, vertices_352, vertices_672, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_611), (false, vertices_157), (false, vertices_589), (false, vertices_677), (false, vertices_345), (false, vertices_241), (true, vertices_74), (true, vertices_266), (true, vertices_522), (true, vertices_162), (true, vertices_290), (true, vertices_386), (true, vertices_642), (true, vertices_770), (true, vertices_268), (true, vertices_276), (true, vertices_772), (true, vertices_304), (true, vertices_400), (true, vertices_352), (true, vertices_896)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 17 21 23 25 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_611) then 16 else
  if p.val = (false, vertices_157) then 18 else
  if p.val = (false, vertices_589) then 19 else
  if p.val = (false, vertices_677) then 20 else
  if p.val = (false, vertices_345) then 22 else
  if p.val = (false, vertices_241) then 24 else
  if p.val = (true, vertices_74) then 0 else
  if p.val = (true, vertices_266) then 1 else
  if p.val = (true, vertices_522) then 2 else
  if p.val = (true, vertices_162) then 3 else
  if p.val = (true, vertices_290) then 4 else
  if p.val = (true, vertices_386) then 5 else
  if p.val = (true, vertices_642) then 6 else
  if p.val = (true, vertices_770) then 7 else
  if p.val = (true, vertices_268) then 8 else
  if p.val = (true, vertices_276) then 9 else
  if p.val = (true, vertices_772) then 10 else
  if p.val = (true, vertices_304) then 11 else
  if p.val = (true, vertices_400) then 12 else
  if p.val = (true, vertices_352) then 13 else
  if p.val = (true, vertices_896) then 14 else
  0
cert_priority
cert_nodeAtPriority_68 0 74 1 266 522 162 290 386 642 770 268 276 772 304 400 352 896 611 157 589 677 345 241
cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 2 4 5 7 362 74 2
cert_row_4 1 0 1 2 7 8 782 266 1
cert_row_4 2 0 3 4 6 7 434 162 1
cert_row_4 3 1 3 6 7 8 916 148 3
cert_rows
cert_pivot_2 5 2 0 1
cert_heightProof 4
cert_coverFacet 0 782
cert_cover_5 0 1 0 1 2 7 266 782 1
cert_coverFacet 1 362
cert_cover_5 1 0 0 2 4 5 74 362 2
cert_coverFacet 2 586
cert_cover_2 2 2 0 5 8 74 586 3
cert_coverFacet 3 434
cert_cover_5 3 2 0 3 4 6 162 434 1
cert_coverFacet 4 674
cert_cover_2 4 4 0 6 8 162 674 3
cert_coverFacet 5 898
cert_cover_2 5 6 0 7 8 386 898 3
cert_coverFacet 6 284
cert_cover_2 6 2 1 3 7 28 284 3
cert_coverFacet 7 916
cert_cover_5 7 3 1 3 6 7 148 916 3
cert_coverFacet 8 368
cert_cover_2 8 4 3 5 7 112 368 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q0_0004

end
end BundlePart1

section BundlePart2
/- Source: ProjectionCertificates/R_m15e10q0_0005.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q0_0005

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [587, 93, 653, 181, 369, 737, 782, 362, 434, 610, 674, 898, 284, 916, 344, 13, 21, 133, 73, 521, 49, 81, 97, 161, 577, 641, 74, 266, 522, 98, 162, 290, 546, 578, 386, 642, 770, 28, 268, 524, 148, 276, 644, 772, 88, 280, 328, 176, 304, 336, 400, 352, 608, 672, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_587, vertices_93, vertices_653, vertices_181, vertices_369, vertices_737, vertices_782, vertices_362, vertices_434, vertices_610, vertices_674, vertices_898, vertices_284, vertices_916, vertices_344] (by decide +kernel)
  polygons := literalFinset [vertices_13, vertices_21, vertices_133, vertices_73, vertices_521, vertices_49, vertices_81, vertices_97, vertices_161, vertices_577, vertices_641, vertices_74, vertices_266, vertices_522, vertices_98, vertices_162, vertices_290, vertices_546, vertices_578, vertices_386, vertices_642, vertices_770, vertices_28, vertices_268, vertices_524, vertices_148, vertices_276, vertices_644, vertices_772, vertices_88, vertices_280, vertices_328, vertices_176, vertices_304, vertices_336, vertices_400, vertices_352, vertices_608, vertices_672, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_587), (false, vertices_93), (false, vertices_653), (false, vertices_181), (false, vertices_369), (false, vertices_737), (true, vertices_266), (true, vertices_98), (true, vertices_162), (true, vertices_290), (true, vertices_546), (true, vertices_386), (true, vertices_642), (true, vertices_770), (true, vertices_268), (true, vertices_276), (true, vertices_772), (true, vertices_280), (true, vertices_328), (true, vertices_400), (true, vertices_896)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 17 21 22 24 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_587) then 16 else
  if p.val = (false, vertices_93) then 18 else
  if p.val = (false, vertices_653) then 19 else
  if p.val = (false, vertices_181) then 20 else
  if p.val = (false, vertices_369) then 23 else
  if p.val = (false, vertices_737) then 25 else
  if p.val = (true, vertices_266) then 0 else
  if p.val = (true, vertices_98) then 1 else
  if p.val = (true, vertices_162) then 2 else
  if p.val = (true, vertices_290) then 3 else
  if p.val = (true, vertices_546) then 4 else
  if p.val = (true, vertices_386) then 5 else
  if p.val = (true, vertices_642) then 6 else
  if p.val = (true, vertices_770) then 7 else
  if p.val = (true, vertices_268) then 8 else
  if p.val = (true, vertices_276) then 9 else
  if p.val = (true, vertices_772) then 10 else
  if p.val = (true, vertices_280) then 11 else
  if p.val = (true, vertices_328) then 12 else
  if p.val = (true, vertices_400) then 13 else
  if p.val = (true, vertices_896) then 14 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_266), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_98), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_162), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_290), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_546), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_386), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_642), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_770), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_268), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_276), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_772), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_280), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_328), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_400), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_896), by decide +kernel⟩
  | 15 => Sum.inl 0
  | 16 => Sum.inr ⟨(false, vertices_587), by decide +kernel⟩
  | 17 => Sum.inl 1
  | 18 => Sum.inr ⟨(false, vertices_93), by decide +kernel⟩
  | 19 => Sum.inr ⟨(false, vertices_653), by decide +kernel⟩
  | 20 => Sum.inr ⟨(false, vertices_181), by decide +kernel⟩
  | 21 => Sum.inl 2
  | 22 => Sum.inl 3
  | 23 => Sum.inr ⟨(false, vertices_369), by decide +kernel⟩
  | 24 => Sum.inl 4
  | 25 => Sum.inr ⟨(false, vertices_737), by decide +kernel⟩
  | 26 => Sum.inl 5
  | 27 => Sum.inl 6
  | 28 => Sum.inl 7
  | 29 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 2 4 5 7 362 74 2
cert_row_4 1 0 1 2 7 8 782 266 1
cert_row_4 2 0 3 4 6 7 434 162 1
cert_row_4 3 1 3 6 7 8 916 148 3
cert_rows
cert_pivot_2 5 2 0 1
cert_heightProof 4
cert_coverFacet 0 782
cert_cover_5 0 1 0 1 2 7 266 782 1
cert_coverFacet 1 362
cert_cover_5 1 0 0 2 4 5 74 362 2
cert_coverFacet 2 434
cert_cover_5 2 2 0 3 4 6 162 434 1
cert_coverFacet 3 610
cert_cover_2 3 4 0 5 8 98 610 3
cert_coverFacet 4 674
cert_cover_2 4 4 0 6 8 162 674 3
cert_coverFacet 5 898
cert_cover_2 5 6 0 7 8 386 898 3
cert_coverFacet 6 284
cert_cover_2 6 2 1 3 7 28 284 3
cert_coverFacet 7 916
cert_cover_5 7 3 1 3 6 7 148 916 3
cert_coverFacet 8 344
cert_cover_2 8 3 2 5 7 88 344 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q0_0005

end
end BundlePart2

section BundlePart3
/- Source: ProjectionCertificates/R_m15e10q0_0006.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q0_0006

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [55, 539, 395, 291, 653, 597, 421, 842, 306, 786, 244, 708, 488, 712, 880, 11, 19, 35, 259, 21, 37, 133, 517, 137, 521, 529, 289, 385, 266, 522, 50, 274, 530, 290, 770, 52, 84, 164, 196, 580, 644, 200, 328, 584, 392, 648, 112, 304, 592, 784, 224, 352, 416, 704, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_55, vertices_539, vertices_395, vertices_291, vertices_653, vertices_597, vertices_421, vertices_842, vertices_306, vertices_786, vertices_244, vertices_708, vertices_488, vertices_712, vertices_880] (by decide +kernel)
  polygons := literalFinset [vertices_11, vertices_19, vertices_35, vertices_259, vertices_21, vertices_37, vertices_133, vertices_517, vertices_137, vertices_521, vertices_529, vertices_289, vertices_385, vertices_266, vertices_522, vertices_50, vertices_274, vertices_530, vertices_290, vertices_770, vertices_52, vertices_84, vertices_164, vertices_196, vertices_580, vertices_644, vertices_200, vertices_328, vertices_584, vertices_392, vertices_648, vertices_112, vertices_304, vertices_592, vertices_784, vertices_224, vertices_352, vertices_416, vertices_704, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_55), (false, vertices_539), (false, vertices_395), (false, vertices_291), (false, vertices_653), (false, vertices_597), (false, vertices_421), (true, vertices_274), (true, vertices_770), (true, vertices_196), (true, vertices_200), (true, vertices_328), (true, vertices_584), (true, vertices_112), (true, vertices_304), (true, vertices_784), (true, vertices_224), (true, vertices_352), (true, vertices_704), (true, vertices_832)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 14 18 22 23 24 25 26 27 28
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_55) then 15 else
  if p.val = (false, vertices_539) then 16 else
  if p.val = (false, vertices_395) then 17 else
  if p.val = (false, vertices_291) then 0 else
  if p.val = (false, vertices_653) then 19 else
  if p.val = (false, vertices_597) then 20 else
  if p.val = (false, vertices_421) then 21 else
  if p.val = (true, vertices_274) then 1 else
  if p.val = (true, vertices_770) then 2 else
  if p.val = (true, vertices_196) then 3 else
  if p.val = (true, vertices_200) then 4 else
  if p.val = (true, vertices_328) then 5 else
  if p.val = (true, vertices_584) then 6 else
  if p.val = (true, vertices_112) then 7 else
  if p.val = (true, vertices_304) then 8 else
  if p.val = (true, vertices_784) then 9 else
  if p.val = (true, vertices_224) then 10 else
  if p.val = (true, vertices_352) then 11 else
  if p.val = (true, vertices_704) then 12 else
  if p.val = (true, vertices_832) then 13 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_291), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_274), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_770), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_196), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_200), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_328), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_584), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_112), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_304), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_784), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_224), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_352), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_704), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_832), by decide +kernel⟩
  | 14 => Sum.inl 0
  | 15 => Sum.inr ⟨(false, vertices_55), by decide +kernel⟩
  | 16 => Sum.inr ⟨(false, vertices_539), by decide +kernel⟩
  | 17 => Sum.inr ⟨(false, vertices_395), by decide +kernel⟩
  | 18 => Sum.inl 1
  | 19 => Sum.inr ⟨(false, vertices_653), by decide +kernel⟩
  | 20 => Sum.inr ⟨(false, vertices_597), by decide +kernel⟩
  | 21 => Sum.inr ⟨(false, vertices_421), by decide +kernel⟩
  | 22 => Sum.inl 2
  | 23 => Sum.inl 3
  | 24 => Sum.inl 4
  | 25 => Sum.inl 5
  | 26 => Sum.inl 6
  | 27 => Sum.inl 7
  | 28 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 2 5 7 8 842 266 2
cert_row_4 1 1 3 4 5 6 244 52 3
cert_row_4 2 2 4 5 6 7 488 200 1
cert_row_4 3 3 4 5 7 8 880 112 3
cert_rows
cert_pivot_2 0 1 2 3
cert_heightProof 4
cert_coverFacet 0 842
cert_cover_5 0 0 0 2 5 7 266 842 2
cert_coverFacet 1 306
cert_cover_2 1 3 0 4 7 50 306 3
cert_coverFacet 2 786
cert_cover_2 2 3 0 7 8 274 786 3
cert_coverFacet 3 244
cert_cover_5 3 1 1 3 4 5 52 244 3
cert_coverFacet 4 708
cert_cover_2 4 5 1 6 8 196 708 3
cert_coverFacet 5 488
cert_cover_5 5 2 2 4 5 6 200 488 1
cert_coverFacet 6 712
cert_cover_2 6 5 2 6 8 200 712 3
cert_coverFacet 7 880
cert_cover_5 7 3 3 4 5 7 112 880 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q0_0006

end
end BundlePart3

section BundlePart4
/- Source: ProjectionCertificates/R_m15e10q0_0008.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q0_0008

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [583, 283, 555, 451, 541, 213, 401, 362, 610, 692, 484, 612, 920, 808, 928, 11, 67, 259, 515, 21, 69, 517, 25, 521, 145, 273, 193, 385, 42, 266, 98, 546, 322, 578, 148, 532, 100, 164, 548, 196, 580, 280, 536, 296, 552, 776, 400, 656, 352, 608, 416, 672, 800, 448, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_583, vertices_283, vertices_555, vertices_451, vertices_541, vertices_213, vertices_401, vertices_362, vertices_610, vertices_692, vertices_484, vertices_612, vertices_920, vertices_808, vertices_928] (by decide +kernel)
  polygons := literalFinset [vertices_11, vertices_67, vertices_259, vertices_515, vertices_21, vertices_69, vertices_517, vertices_25, vertices_521, vertices_145, vertices_273, vertices_193, vertices_385, vertices_42, vertices_266, vertices_98, vertices_546, vertices_322, vertices_578, vertices_148, vertices_532, vertices_100, vertices_164, vertices_548, vertices_196, vertices_580, vertices_280, vertices_536, vertices_296, vertices_552, vertices_776, vertices_400, vertices_656, vertices_352, vertices_608, vertices_416, vertices_672, vertices_800, vertices_448, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_583), (false, vertices_283), (false, vertices_555), (false, vertices_451), (false, vertices_541), (false, vertices_213), (false, vertices_401), (true, vertices_98), (true, vertices_100), (true, vertices_164), (true, vertices_548), (true, vertices_296), (true, vertices_776), (true, vertices_656), (true, vertices_352), (true, vertices_608), (true, vertices_416), (true, vertices_672), (true, vertices_800), (true, vertices_896)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 18 14 22 23 24 25 26 27 28
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_583) then 15 else
  if p.val = (false, vertices_283) then 19 else
  if p.val = (false, vertices_555) then 20 else
  if p.val = (false, vertices_451) then 21 else
  if p.val = (false, vertices_541) then 16 else
  if p.val = (false, vertices_213) then 17 else
  if p.val = (false, vertices_401) then 0 else
  if p.val = (true, vertices_98) then 1 else
  if p.val = (true, vertices_100) then 2 else
  if p.val = (true, vertices_164) then 3 else
  if p.val = (true, vertices_548) then 4 else
  if p.val = (true, vertices_296) then 5 else
  if p.val = (true, vertices_776) then 6 else
  if p.val = (true, vertices_656) then 7 else
  if p.val = (true, vertices_352) then 8 else
  if p.val = (true, vertices_608) then 9 else
  if p.val = (true, vertices_416) then 10 else
  if p.val = (true, vertices_672) then 11 else
  if p.val = (true, vertices_800) then 12 else
  if p.val = (true, vertices_896) then 13 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_401), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_98), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_100), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_164), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_548), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_296), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_776), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_656), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_352), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_608), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_416), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_672), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_800), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_896), by decide +kernel⟩
  | 14 => Sum.inl 1
  | 15 => Sum.inr ⟨(false, vertices_583), by decide +kernel⟩
  | 16 => Sum.inr ⟨(false, vertices_541), by decide +kernel⟩
  | 17 => Sum.inr ⟨(false, vertices_213), by decide +kernel⟩
  | 18 => Sum.inl 0
  | 19 => Sum.inr ⟨(false, vertices_283), by decide +kernel⟩
  | 20 => Sum.inr ⟨(false, vertices_555), by decide +kernel⟩
  | 21 => Sum.inr ⟨(false, vertices_451), by decide +kernel⟩
  | 22 => Sum.inl 2
  | 23 => Sum.inl 3
  | 24 => Sum.inl 4
  | 25 => Sum.inl 5
  | 26 => Sum.inl 6
  | 27 => Sum.inl 7
  | 28 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 2 4 5 7 362 42 3
cert_row_4 1 1 4 5 6 7 484 100 3
cert_row_4 2 1 3 4 6 8 692 148 2
cert_row_4 3 2 3 6 7 8 920 280 2
cert_rows
cert_pivot_2 0 5 1 2
cert_heightProof 4
cert_coverFacet 0 362
cert_cover_5 0 0 0 2 4 5 42 362 3
cert_coverFacet 1 610
cert_cover_2 1 4 0 5 8 98 610 3
cert_coverFacet 2 692
cert_cover_5 2 2 1 3 4 6 148 692 2
cert_coverFacet 3 484
cert_cover_5 3 1 1 4 5 6 100 484 3
cert_coverFacet 4 612
cert_cover_2 4 4 1 5 8 100 612 3
cert_coverFacet 5 920
cert_cover_5 5 3 2 3 6 7 280 920 2
cert_coverFacet 6 808
cert_cover_2 6 4 2 7 8 296 808 3
cert_coverFacet 7 928
cert_cover_2 7 6 4 7 8 416 928 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q0_0008

end
end BundlePart4

section BundlePart5
/- Source: ProjectionCertificates/R_m15e10q0_0009.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q0_0009

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [707, 61, 653, 213, 617, 369, 782, 314, 554, 482, 610, 898, 284, 916, 464, 13, 21, 133, 41, 521, 49, 81, 97, 193, 577, 641, 42, 266, 522, 98, 290, 546, 194, 578, 386, 642, 770, 28, 268, 524, 148, 276, 644, 772, 56, 280, 552, 304, 208, 336, 400, 352, 608, 448, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_707, vertices_61, vertices_653, vertices_213, vertices_617, vertices_369, vertices_782, vertices_314, vertices_554, vertices_482, vertices_610, vertices_898, vertices_284, vertices_916, vertices_464] (by decide +kernel)
  polygons := literalFinset [vertices_13, vertices_21, vertices_133, vertices_41, vertices_521, vertices_49, vertices_81, vertices_97, vertices_193, vertices_577, vertices_641, vertices_42, vertices_266, vertices_522, vertices_98, vertices_290, vertices_546, vertices_194, vertices_578, vertices_386, vertices_642, vertices_770, vertices_28, vertices_268, vertices_524, vertices_148, vertices_276, vertices_644, vertices_772, vertices_56, vertices_280, vertices_552, vertices_304, vertices_208, vertices_336, vertices_400, vertices_352, vertices_608, vertices_448, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_707), (false, vertices_61), (false, vertices_653), (false, vertices_213), (false, vertices_617), (false, vertices_369), (true, vertices_42), (true, vertices_266), (true, vertices_522), (true, vertices_98), (true, vertices_290), (true, vertices_546), (true, vertices_386), (true, vertices_770), (true, vertices_268), (true, vertices_276), (true, vertices_772), (true, vertices_280), (true, vertices_400), (true, vertices_448), (true, vertices_896)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 17 21 23 25 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_707) then 16 else
  if p.val = (false, vertices_61) then 18 else
  if p.val = (false, vertices_653) then 19 else
  if p.val = (false, vertices_213) then 20 else
  if p.val = (false, vertices_617) then 22 else
  if p.val = (false, vertices_369) then 24 else
  if p.val = (true, vertices_42) then 0 else
  if p.val = (true, vertices_266) then 1 else
  if p.val = (true, vertices_522) then 2 else
  if p.val = (true, vertices_98) then 3 else
  if p.val = (true, vertices_290) then 4 else
  if p.val = (true, vertices_546) then 5 else
  if p.val = (true, vertices_386) then 6 else
  if p.val = (true, vertices_770) then 7 else
  if p.val = (true, vertices_268) then 8 else
  if p.val = (true, vertices_276) then 9 else
  if p.val = (true, vertices_772) then 10 else
  if p.val = (true, vertices_280) then 11 else
  if p.val = (true, vertices_400) then 12 else
  if p.val = (true, vertices_448) then 13 else
  if p.val = (true, vertices_896) then 14 else
  0
cert_priority
cert_nodeAtPriority_68 0 42 1 266 522 98 290 546 386 770 268 276 772 280 400 448 896 707 61 653 213 617 369
cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 4 5 6 7 482 98 3
cert_row_4 1 0 2 3 4 7 314 42 2
cert_row_4 2 0 1 2 7 8 782 266 1
cert_row_4 3 1 3 6 7 8 916 148 3
cert_rows
cert_pivot_2 5 4 0 1
cert_heightProof 4
cert_coverFacet 0 782
cert_cover_5 0 2 0 1 2 7 266 782 1
cert_coverFacet 1 314
cert_cover_5 1 1 0 2 3 4 42 314 2
cert_coverFacet 2 554
cert_cover_2 2 2 0 4 8 42 554 3
cert_coverFacet 3 482
cert_cover_5 3 0 0 4 5 6 98 482 3
cert_coverFacet 4 610
cert_cover_2 4 4 0 5 8 98 610 3
cert_coverFacet 5 898
cert_cover_2 5 6 0 7 8 386 898 3
cert_coverFacet 6 284
cert_cover_2 6 2 1 3 7 28 284 3
cert_coverFacet 7 916
cert_cover_5 7 3 1 3 6 7 148 916 3
cert_coverFacet 8 464
cert_cover_2 8 5 3 6 7 208 464 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q0_0009

end
end BundlePart5

section BundlePart6
/- Source: ProjectionCertificates/R_m15e10q0_0011.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q0_0011

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [551, 587, 227, 541, 301, 457, 417, 690, 962, 348, 436, 564, 600, 848, 912, 35, 67, 515, 13, 37, 517, 73, 265, 521, 161, 289, 193, 385, 162, 546, 194, 578, 642, 28, 268, 52, 276, 532, 292, 548, 88, 536, 328, 584, 176, 560, 336, 592, 400, 656, 784, 416, 448, 832, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_551, vertices_587, vertices_227, vertices_541, vertices_301, vertices_457, vertices_417, vertices_690, vertices_962, vertices_348, vertices_436, vertices_564, vertices_600, vertices_848, vertices_912] (by decide +kernel)
  polygons := literalFinset [vertices_35, vertices_67, vertices_515, vertices_13, vertices_37, vertices_517, vertices_73, vertices_265, vertices_521, vertices_161, vertices_289, vertices_193, vertices_385, vertices_162, vertices_546, vertices_194, vertices_578, vertices_642, vertices_28, vertices_268, vertices_52, vertices_276, vertices_532, vertices_292, vertices_548, vertices_88, vertices_536, vertices_328, vertices_584, vertices_176, vertices_560, vertices_336, vertices_592, vertices_400, vertices_656, vertices_784, vertices_416, vertices_448, vertices_832, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_551), (false, vertices_587), (false, vertices_227), (false, vertices_541), (false, vertices_301), (false, vertices_457), (false, vertices_417), (true, vertices_642), (true, vertices_52), (true, vertices_276), (true, vertices_88), (true, vertices_176), (true, vertices_560), (true, vertices_336), (true, vertices_592), (true, vertices_400), (true, vertices_656), (true, vertices_784), (true, vertices_832), (true, vertices_896)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 14 18 21 23 24 25 26 27 28
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_551) then 15 else
  if p.val = (false, vertices_587) then 16 else
  if p.val = (false, vertices_227) then 17 else
  if p.val = (false, vertices_541) then 19 else
  if p.val = (false, vertices_301) then 20 else
  if p.val = (false, vertices_457) then 22 else
  if p.val = (false, vertices_417) then 0 else
  if p.val = (true, vertices_642) then 1 else
  if p.val = (true, vertices_52) then 2 else
  if p.val = (true, vertices_276) then 3 else
  if p.val = (true, vertices_88) then 4 else
  if p.val = (true, vertices_176) then 5 else
  if p.val = (true, vertices_560) then 6 else
  if p.val = (true, vertices_336) then 7 else
  if p.val = (true, vertices_592) then 8 else
  if p.val = (true, vertices_400) then 9 else
  if p.val = (true, vertices_656) then 10 else
  if p.val = (true, vertices_784) then 11 else
  if p.val = (true, vertices_832) then 12 else
  if p.val = (true, vertices_896) then 13 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_417), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_642), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_52), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_276), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_88), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_176), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_560), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_336), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_592), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_400), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_656), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_784), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_832), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_896), by decide +kernel⟩
  | 14 => Sum.inl 0
  | 15 => Sum.inr ⟨(false, vertices_551), by decide +kernel⟩
  | 16 => Sum.inr ⟨(false, vertices_587), by decide +kernel⟩
  | 17 => Sum.inr ⟨(false, vertices_227), by decide +kernel⟩
  | 18 => Sum.inl 1
  | 19 => Sum.inr ⟨(false, vertices_541), by decide +kernel⟩
  | 20 => Sum.inr ⟨(false, vertices_301), by decide +kernel⟩
  | 21 => Sum.inl 2
  | 22 => Sum.inr ⟨(false, vertices_457), by decide +kernel⟩
  | 23 => Sum.inl 3
  | 24 => Sum.inl 4
  | 25 => Sum.inl 5
  | 26 => Sum.inl 6
  | 27 => Sum.inl 7
  | 28 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 1 2 3 5 7 348 28 3
cert_row_4 1 0 5 6 7 8 962 194 3
cert_row_4 2 0 3 4 6 8 690 162 1
cert_row_4 3 1 3 4 6 7 436 52 3
cert_rows
cert_pivot_2 2 5 0 1
cert_heightProof 4
cert_coverFacet 0 690
cert_cover_5 0 2 0 3 4 6 162 690 1
cert_coverFacet 1 962
cert_cover_5 1 1 0 5 6 7 194 962 3
cert_coverFacet 2 348
cert_cover_5 2 0 1 2 3 5 28 348 3
cert_coverFacet 3 436
cert_cover_5 3 3 1 3 4 6 52 436 3
cert_coverFacet 4 564
cert_cover_2 4 3 1 4 8 52 564 3
cert_coverFacet 5 600
cert_cover_2 5 3 2 5 8 88 600 3
cert_coverFacet 6 848
cert_cover_2 6 5 3 7 8 336 848 3
cert_coverFacet 7 912
cert_cover_2 7 6 3 7 8 400 912 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q0_0011

end
end BundlePart6

section BundlePart7
/- Source: ProjectionCertificates/R_m15e10q0_0013.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q0_0013

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [299, 179, 275, 285, 109, 213, 737, 790, 722, 418, 898, 844, 596, 616, 936, 19, 35, 259, 13, 21, 69, 41, 265, 145, 273, 97, 161, 193, 146, 274, 530, 162, 290, 386, 642, 770, 76, 268, 84, 276, 532, 580, 772, 104, 296, 552, 584, 776, 208, 592, 608, 416, 672, 704, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_299, vertices_179, vertices_275, vertices_285, vertices_109, vertices_213, vertices_737, vertices_790, vertices_722, vertices_418, vertices_898, vertices_844, vertices_596, vertices_616, vertices_936] (by decide +kernel)
  polygons := literalFinset [vertices_19, vertices_35, vertices_259, vertices_13, vertices_21, vertices_69, vertices_41, vertices_265, vertices_145, vertices_273, vertices_97, vertices_161, vertices_193, vertices_146, vertices_274, vertices_530, vertices_162, vertices_290, vertices_386, vertices_642, vertices_770, vertices_76, vertices_268, vertices_84, vertices_276, vertices_532, vertices_580, vertices_772, vertices_104, vertices_296, vertices_552, vertices_584, vertices_776, vertices_208, vertices_592, vertices_608, vertices_416, vertices_672, vertices_704, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_299), (false, vertices_179), (false, vertices_275), (false, vertices_285), (false, vertices_109), (false, vertices_213), (false, vertices_737), (true, vertices_530), (true, vertices_386), (true, vertices_642), (true, vertices_770), (true, vertices_532), (true, vertices_580), (true, vertices_772), (true, vertices_552), (true, vertices_584), (true, vertices_776), (true, vertices_592), (true, vertices_416), (true, vertices_896)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 14 17 21 22 23 25 26 27 28
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_299) then 15 else
  if p.val = (false, vertices_179) then 16 else
  if p.val = (false, vertices_275) then 0 else
  if p.val = (false, vertices_285) then 18 else
  if p.val = (false, vertices_109) then 19 else
  if p.val = (false, vertices_213) then 20 else
  if p.val = (false, vertices_737) then 24 else
  if p.val = (true, vertices_530) then 1 else
  if p.val = (true, vertices_386) then 2 else
  if p.val = (true, vertices_642) then 3 else
  if p.val = (true, vertices_770) then 4 else
  if p.val = (true, vertices_532) then 5 else
  if p.val = (true, vertices_580) then 6 else
  if p.val = (true, vertices_772) then 7 else
  if p.val = (true, vertices_552) then 8 else
  if p.val = (true, vertices_584) then 9 else
  if p.val = (true, vertices_776) then 10 else
  if p.val = (true, vertices_592) then 11 else
  if p.val = (true, vertices_416) then 12 else
  if p.val = (true, vertices_896) then 13 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_275), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_530), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_386), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_642), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_770), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_532), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_580), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_772), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_552), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_584), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_776), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_592), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_416), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_896), by decide +kernel⟩
  | 14 => Sum.inl 0
  | 15 => Sum.inr ⟨(false, vertices_299), by decide +kernel⟩
  | 16 => Sum.inr ⟨(false, vertices_179), by decide +kernel⟩
  | 17 => Sum.inl 1
  | 18 => Sum.inr ⟨(false, vertices_285), by decide +kernel⟩
  | 19 => Sum.inr ⟨(false, vertices_109), by decide +kernel⟩
  | 20 => Sum.inr ⟨(false, vertices_213), by decide +kernel⟩
  | 21 => Sum.inl 2
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
cert_row_4 0 2 4 6 7 8 936 296 2
cert_row_4 1 0 3 5 6 8 722 146 2
cert_row_4 2 0 1 3 7 8 790 274 1
cert_row_4 3 1 2 5 7 8 844 76 3
cert_rows
cert_pivot_2 4 6 0 1
cert_heightProof 4
cert_coverFacet 0 790
cert_cover_5 0 2 0 1 3 7 274 790 1
cert_coverFacet 1 722
cert_cover_5 1 1 0 3 5 6 146 722 2
cert_coverFacet 2 418
cert_cover_2 2 4 0 6 7 162 418 3
cert_coverFacet 3 898
cert_cover_2 3 6 0 7 8 386 898 3
cert_coverFacet 4 844
cert_cover_5 4 3 1 2 5 7 76 844 3
cert_coverFacet 5 596
cert_cover_2 5 3 1 5 8 84 596 3
cert_coverFacet 6 616
cert_cover_2 6 4 2 5 8 104 616 3
cert_coverFacet 7 936
cert_cover_5 7 0 2 4 6 7 296 936 2
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q0_0013

end
end BundlePart7

section BundlePart8
/- Source: ProjectionCertificates/R_m15e10q0_0015.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q0_0015

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [527, 283, 563, 205, 181, 549, 329, 465, 842, 914, 620, 484, 688, 864, 928, 11, 19, 515, 13, 37, 133, 517, 73, 265, 49, 145, 273, 545, 193, 321, 266, 522, 274, 530, 770, 76, 524, 100, 164, 548, 196, 328, 584, 176, 560, 400, 656, 352, 608, 416, 672, 800, 448, 832, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_527, vertices_283, vertices_563, vertices_205, vertices_181, vertices_549, vertices_329, vertices_465, vertices_842, vertices_914, vertices_620, vertices_484, vertices_688, vertices_864, vertices_928] (by decide +kernel)
  polygons := literalFinset [vertices_11, vertices_19, vertices_515, vertices_13, vertices_37, vertices_133, vertices_517, vertices_73, vertices_265, vertices_49, vertices_145, vertices_273, vertices_545, vertices_193, vertices_321, vertices_266, vertices_522, vertices_274, vertices_530, vertices_770, vertices_76, vertices_524, vertices_100, vertices_164, vertices_548, vertices_196, vertices_328, vertices_584, vertices_176, vertices_560, vertices_400, vertices_656, vertices_352, vertices_608, vertices_416, vertices_672, vertices_800, vertices_448, vertices_832, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_527), (false, vertices_283), (false, vertices_563), (false, vertices_205), (false, vertices_181), (false, vertices_549), (false, vertices_329), (false, vertices_465), (true, vertices_770), (true, vertices_100), (true, vertices_584), (true, vertices_656), (true, vertices_352), (true, vertices_608), (true, vertices_416), (true, vertices_672), (true, vertices_800), (true, vertices_832), (true, vertices_896)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 13 17 20 21 23 24 25 26 27
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_527) then 14 else
  if p.val = (false, vertices_283) then 15 else
  if p.val = (false, vertices_563) then 16 else
  if p.val = (false, vertices_205) then 18 else
  if p.val = (false, vertices_181) then 19 else
  if p.val = (false, vertices_549) then 0 else
  if p.val = (false, vertices_329) then 1 else
  if p.val = (false, vertices_465) then 22 else
  if p.val = (true, vertices_770) then 2 else
  if p.val = (true, vertices_100) then 3 else
  if p.val = (true, vertices_584) then 4 else
  if p.val = (true, vertices_656) then 5 else
  if p.val = (true, vertices_352) then 6 else
  if p.val = (true, vertices_608) then 7 else
  if p.val = (true, vertices_416) then 8 else
  if p.val = (true, vertices_672) then 9 else
  if p.val = (true, vertices_800) then 10 else
  if p.val = (true, vertices_832) then 11 else
  if p.val = (true, vertices_896) then 12 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_549), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_329), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_770), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_100), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_584), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_656), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_352), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_608), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_416), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_672), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_800), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_832), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_896), by decide +kernel⟩
  | 13 => Sum.inl 0
  | 14 => Sum.inr ⟨(false, vertices_527), by decide +kernel⟩
  | 15 => Sum.inr ⟨(false, vertices_283), by decide +kernel⟩
  | 16 => Sum.inr ⟨(false, vertices_563), by decide +kernel⟩
  | 17 => Sum.inl 1
  | 18 => Sum.inr ⟨(false, vertices_205), by decide +kernel⟩
  | 19 => Sum.inr ⟨(false, vertices_181), by decide +kernel⟩
  | 20 => Sum.inl 2
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
cert_row_4 0 0 3 6 7 8 914 274 2
cert_row_4 1 0 2 5 7 8 842 266 2
cert_row_4 2 1 2 4 5 8 620 76 2
cert_row_4 3 1 4 5 6 7 484 100 3
cert_rows
cert_pivot_2 3 0 2 1
cert_heightProof 4
cert_coverFacet 0 842
cert_cover_5 0 1 0 2 5 7 266 842 2
cert_coverFacet 1 914
cert_cover_5 1 0 0 3 6 7 274 914 2
cert_coverFacet 2 620
cert_cover_5 2 2 1 2 4 5 76 620 2
cert_coverFacet 3 484
cert_cover_5 3 3 1 4 5 6 100 484 3
cert_coverFacet 4 688
cert_cover_2 4 4 3 6 8 176 688 3
cert_coverFacet 5 864
cert_cover_2 5 5 4 7 8 352 864 3
cert_coverFacet 6 928
cert_cover_2 6 6 4 7 8 416 928 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q0_0015

end
end BundlePart8

section BundlePart9
/- Source: ProjectionCertificates/R_m15e10q0_0016.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q0_0016

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [167, 651, 307, 595, 589, 141, 341, 293, 690, 204, 484, 856, 936, 456, 816, 19, 35, 131, 515, 13, 37, 69, 133, 261, 137, 521, 81, 273, 289, 577, 50, 530, 162, 642, 76, 140, 164, 292, 196, 324, 200, 328, 584, 392, 648, 776, 304, 560, 336, 592, 784, 416, 672, 800, 448]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_167, vertices_651, vertices_307, vertices_595, vertices_589, vertices_141, vertices_341, vertices_293, vertices_690, vertices_204, vertices_484, vertices_856, vertices_936, vertices_456, vertices_816] (by decide +kernel)
  polygons := literalFinset [vertices_19, vertices_35, vertices_131, vertices_515, vertices_13, vertices_37, vertices_69, vertices_133, vertices_261, vertices_137, vertices_521, vertices_81, vertices_273, vertices_289, vertices_577, vertices_50, vertices_530, vertices_162, vertices_642, vertices_76, vertices_140, vertices_164, vertices_292, vertices_196, vertices_324, vertices_200, vertices_328, vertices_584, vertices_392, vertices_648, vertices_776, vertices_304, vertices_560, vertices_336, vertices_592, vertices_784, vertices_416, vertices_672, vertices_800, vertices_448] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_167), (false, vertices_651), (false, vertices_307), (false, vertices_595), (false, vertices_589), (false, vertices_141), (false, vertices_341), (false, vertices_293), (true, vertices_196), (true, vertices_200), (true, vertices_328), (true, vertices_392), (true, vertices_776), (true, vertices_560), (true, vertices_784), (true, vertices_416), (true, vertices_672), (true, vertices_800), (true, vertices_448)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 17 13 21 22 23 24 25 26 27
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_167) then 14 else
  if p.val = (false, vertices_651) then 18 else
  if p.val = (false, vertices_307) then 19 else
  if p.val = (false, vertices_595) then 20 else
  if p.val = (false, vertices_589) then 15 else
  if p.val = (false, vertices_141) then 0 else
  if p.val = (false, vertices_341) then 16 else
  if p.val = (false, vertices_293) then 1 else
  if p.val = (true, vertices_196) then 2 else
  if p.val = (true, vertices_200) then 3 else
  if p.val = (true, vertices_328) then 4 else
  if p.val = (true, vertices_392) then 5 else
  if p.val = (true, vertices_776) then 6 else
  if p.val = (true, vertices_560) then 7 else
  if p.val = (true, vertices_784) then 8 else
  if p.val = (true, vertices_416) then 9 else
  if p.val = (true, vertices_672) then 10 else
  if p.val = (true, vertices_800) then 11 else
  if p.val = (true, vertices_448) then 12 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_141), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_293), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_196), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_200), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_328), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_392), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_776), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_560), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_784), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_416), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_672), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_800), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_448), by decide +kernel⟩
  | 13 => Sum.inl 1
  | 14 => Sum.inr ⟨(false, vertices_167), by decide +kernel⟩
  | 15 => Sum.inr ⟨(false, vertices_589), by decide +kernel⟩
  | 16 => Sum.inr ⟨(false, vertices_341), by decide +kernel⟩
  | 17 => Sum.inl 0
  | 18 => Sum.inr ⟨(false, vertices_651), by decide +kernel⟩
  | 19 => Sum.inr ⟨(false, vertices_307), by decide +kernel⟩
  | 20 => Sum.inr ⟨(false, vertices_595), by decide +kernel⟩
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
cert_row_4 0 0 3 4 6 8 690 50 3
cert_row_4 1 1 4 5 6 7 484 164 2
cert_row_4 2 2 3 5 7 8 856 328 1
cert_row_4 3 2 4 6 7 8 936 392 1
cert_rows
cert_pivot_2 0 1 3 2
cert_heightProof 4
cert_coverFacet 0 690
cert_cover_5 0 0 0 3 4 6 50 690 3
cert_coverFacet 1 204
cert_cover_2 1 2 1 5 6 76 204 3
cert_coverFacet 2 484
cert_cover_5 2 1 1 4 5 6 164 484 2
cert_coverFacet 3 856
cert_cover_5 3 2 2 3 5 7 328 856 1
cert_coverFacet 4 936
cert_cover_5 4 3 2 4 6 7 392 936 1
cert_coverFacet 5 456
cert_cover_2 5 5 2 6 7 200 456 3
cert_coverFacet 6 816
cert_cover_2 6 4 3 7 8 304 816 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q0_0016

end
end BundlePart9

section BundlePart10
/- Source: ProjectionCertificates/R_m15e10q0_0017.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q0_0017

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [299, 179, 275, 285, 589, 213, 233, 790, 722, 418, 898, 812, 596, 616, 992, 19, 35, 259, 13, 21, 69, 41, 73, 265, 145, 273, 161, 193, 146, 274, 530, 162, 290, 386, 642, 770, 268, 524, 84, 276, 532, 580, 772, 104, 296, 552, 584, 208, 592, 224, 608, 416, 800, 704, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_299, vertices_179, vertices_275, vertices_285, vertices_589, vertices_213, vertices_233, vertices_790, vertices_722, vertices_418, vertices_898, vertices_812, vertices_596, vertices_616, vertices_992] (by decide +kernel)
  polygons := literalFinset [vertices_19, vertices_35, vertices_259, vertices_13, vertices_21, vertices_69, vertices_41, vertices_73, vertices_265, vertices_145, vertices_273, vertices_161, vertices_193, vertices_146, vertices_274, vertices_530, vertices_162, vertices_290, vertices_386, vertices_642, vertices_770, vertices_268, vertices_524, vertices_84, vertices_276, vertices_532, vertices_580, vertices_772, vertices_104, vertices_296, vertices_552, vertices_584, vertices_208, vertices_592, vertices_224, vertices_608, vertices_416, vertices_800, vertices_704, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_299), (false, vertices_179), (false, vertices_275), (false, vertices_285), (false, vertices_589), (false, vertices_213), (false, vertices_233), (true, vertices_530), (true, vertices_386), (true, vertices_642), (true, vertices_770), (true, vertices_532), (true, vertices_772), (true, vertices_552), (true, vertices_592), (true, vertices_608), (true, vertices_416), (true, vertices_800), (true, vertices_704), (true, vertices_896)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 14 17 21 23 24 25 26 27 28
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_299) then 15 else
  if p.val = (false, vertices_179) then 16 else
  if p.val = (false, vertices_275) then 0 else
  if p.val = (false, vertices_285) then 18 else
  if p.val = (false, vertices_589) then 19 else
  if p.val = (false, vertices_213) then 20 else
  if p.val = (false, vertices_233) then 22 else
  if p.val = (true, vertices_530) then 1 else
  if p.val = (true, vertices_386) then 2 else
  if p.val = (true, vertices_642) then 3 else
  if p.val = (true, vertices_770) then 4 else
  if p.val = (true, vertices_532) then 5 else
  if p.val = (true, vertices_772) then 6 else
  if p.val = (true, vertices_552) then 7 else
  if p.val = (true, vertices_592) then 8 else
  if p.val = (true, vertices_608) then 9 else
  if p.val = (true, vertices_416) then 10 else
  if p.val = (true, vertices_800) then 11 else
  if p.val = (true, vertices_704) then 12 else
  if p.val = (true, vertices_896) then 13 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_275), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_530), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_386), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_642), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_770), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_532), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_772), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_552), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_592), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_608), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_416), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_800), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_704), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_896), by decide +kernel⟩
  | 14 => Sum.inl 0
  | 15 => Sum.inr ⟨(false, vertices_299), by decide +kernel⟩
  | 16 => Sum.inr ⟨(false, vertices_179), by decide +kernel⟩
  | 17 => Sum.inl 1
  | 18 => Sum.inr ⟨(false, vertices_285), by decide +kernel⟩
  | 19 => Sum.inr ⟨(false, vertices_589), by decide +kernel⟩
  | 20 => Sum.inr ⟨(false, vertices_213), by decide +kernel⟩
  | 21 => Sum.inl 2
  | 22 => Sum.inr ⟨(false, vertices_233), by decide +kernel⟩
  | 23 => Sum.inl 3
  | 24 => Sum.inl 4
  | 25 => Sum.inl 5
  | 26 => Sum.inl 6
  | 27 => Sum.inl 7
  | 28 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 1 2 4 7 8 812 268 2
cert_row_4 1 0 1 3 7 8 790 274 1
cert_row_4 2 0 3 5 6 8 722 146 2
cert_row_4 3 4 5 6 7 8 992 224 3
cert_rows
cert_pivot_2 2 1 0 4
cert_heightProof 4
cert_coverFacet 0 790
cert_cover_5 0 1 0 1 3 7 274 790 1
cert_coverFacet 1 722
cert_cover_5 1 2 0 3 5 6 146 722 2
cert_coverFacet 2 418
cert_cover_2 2 4 0 6 7 162 418 3
cert_coverFacet 3 898
cert_cover_2 3 6 0 7 8 386 898 3
cert_coverFacet 4 812
cert_cover_5 4 0 1 2 4 7 268 812 2
cert_coverFacet 5 596
cert_cover_2 5 3 1 5 8 84 596 3
cert_coverFacet 6 616
cert_cover_2 6 4 2 5 8 104 616 3
cert_coverFacet 7 992
cert_cover_5 7 3 4 5 6 7 224 992 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q0_0017

end
end BundlePart10

section BundlePart11
/- Source: ProjectionCertificates/R_m15e10q0_0018.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q0_0018

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [271, 539, 115, 291, 653, 597, 357, 778, 690, 802, 460, 708, 936, 496, 720, 11, 19, 35, 259, 13, 69, 261, 517, 521, 81, 529, 97, 289, 266, 522, 50, 530, 290, 546, 770, 140, 268, 196, 324, 580, 644, 392, 648, 776, 112, 176, 208, 592, 656, 352, 416, 672, 800, 448, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_271, vertices_539, vertices_115, vertices_291, vertices_653, vertices_597, vertices_357, vertices_778, vertices_690, vertices_802, vertices_460, vertices_708, vertices_936, vertices_496, vertices_720] (by decide +kernel)
  polygons := literalFinset [vertices_11, vertices_19, vertices_35, vertices_259, vertices_13, vertices_69, vertices_261, vertices_517, vertices_521, vertices_81, vertices_529, vertices_97, vertices_289, vertices_266, vertices_522, vertices_50, vertices_530, vertices_290, vertices_546, vertices_770, vertices_140, vertices_268, vertices_196, vertices_324, vertices_580, vertices_644, vertices_392, vertices_648, vertices_776, vertices_112, vertices_176, vertices_208, vertices_592, vertices_656, vertices_352, vertices_416, vertices_672, vertices_800, vertices_448, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_271), (false, vertices_539), (false, vertices_115), (false, vertices_291), (false, vertices_653), (false, vertices_597), (false, vertices_357), (true, vertices_546), (true, vertices_770), (true, vertices_196), (true, vertices_392), (true, vertices_776), (true, vertices_176), (true, vertices_208), (true, vertices_656), (true, vertices_416), (true, vertices_672), (true, vertices_800), (true, vertices_448), (true, vertices_704)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 14 18 22 23 24 25 26 27 28
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_271) then 15 else
  if p.val = (false, vertices_539) then 16 else
  if p.val = (false, vertices_115) then 17 else
  if p.val = (false, vertices_291) then 0 else
  if p.val = (false, vertices_653) then 19 else
  if p.val = (false, vertices_597) then 20 else
  if p.val = (false, vertices_357) then 21 else
  if p.val = (true, vertices_546) then 1 else
  if p.val = (true, vertices_770) then 2 else
  if p.val = (true, vertices_196) then 3 else
  if p.val = (true, vertices_392) then 4 else
  if p.val = (true, vertices_776) then 5 else
  if p.val = (true, vertices_176) then 6 else
  if p.val = (true, vertices_208) then 7 else
  if p.val = (true, vertices_656) then 8 else
  if p.val = (true, vertices_416) then 9 else
  if p.val = (true, vertices_672) then 10 else
  if p.val = (true, vertices_800) then 11 else
  if p.val = (true, vertices_448) then 12 else
  if p.val = (true, vertices_704) then 13 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_291), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_546), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_770), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_196), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_392), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_776), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_176), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_208), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_656), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_416), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_672), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_800), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_448), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_704), by decide +kernel⟩
  | 14 => Sum.inl 0
  | 15 => Sum.inr ⟨(false, vertices_271), by decide +kernel⟩
  | 16 => Sum.inr ⟨(false, vertices_539), by decide +kernel⟩
  | 17 => Sum.inr ⟨(false, vertices_115), by decide +kernel⟩
  | 18 => Sum.inl 1
  | 19 => Sum.inr ⟨(false, vertices_653), by decide +kernel⟩
  | 20 => Sum.inr ⟨(false, vertices_597), by decide +kernel⟩
  | 21 => Sum.inr ⟨(false, vertices_357), by decide +kernel⟩
  | 22 => Sum.inl 2
  | 23 => Sum.inl 3
  | 24 => Sum.inl 4
  | 25 => Sum.inl 5
  | 26 => Sum.inl 6
  | 27 => Sum.inl 7
  | 28 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 3 4 6 8 690 50 3
cert_row_4 1 1 2 5 6 7 460 140 2
cert_row_4 2 2 4 6 7 8 936 392 1
cert_row_4 3 3 4 5 6 7 496 112 3
cert_rows
cert_pivot_2 0 1 2 3
cert_heightProof 4
cert_coverFacet 0 778
cert_cover_2 0 2 0 7 8 266 778 3
cert_coverFacet 1 690
cert_cover_5 1 0 0 3 4 6 50 690 3
cert_coverFacet 2 802
cert_cover_2 2 4 0 7 8 290 802 3
cert_coverFacet 3 460
cert_cover_5 3 1 1 2 5 6 140 460 2
cert_coverFacet 4 708
cert_cover_2 4 5 1 6 8 196 708 3
cert_coverFacet 5 936
cert_cover_5 5 2 2 4 6 7 392 936 1
cert_coverFacet 6 496
cert_cover_5 6 3 3 4 5 6 112 496 3
cert_coverFacet 7 720
cert_cover_2 7 5 3 6 8 208 720 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q0_0018

end
end BundlePart11

section BundlePart12
/- Source: ProjectionCertificates/R_m15e10q0_0019.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q0_0019

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [103, 395, 307, 707, 301, 653, 581, 242, 402, 796, 868, 728, 408, 624, 816, 35, 67, 131, 259, 13, 37, 69, 517, 137, 265, 289, 577, 641, 50, 146, 274, 98, 194, 386, 268, 524, 100, 292, 580, 772, 152, 280, 536, 392, 648, 112, 304, 560, 208, 592, 400, 784, 608, 800, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_103, vertices_395, vertices_307, vertices_707, vertices_301, vertices_653, vertices_581, vertices_242, vertices_402, vertices_796, vertices_868, vertices_728, vertices_408, vertices_624, vertices_816] (by decide +kernel)
  polygons := literalFinset [vertices_35, vertices_67, vertices_131, vertices_259, vertices_13, vertices_37, vertices_69, vertices_517, vertices_137, vertices_265, vertices_289, vertices_577, vertices_641, vertices_50, vertices_146, vertices_274, vertices_98, vertices_194, vertices_386, vertices_268, vertices_524, vertices_100, vertices_292, vertices_580, vertices_772, vertices_152, vertices_280, vertices_536, vertices_392, vertices_648, vertices_112, vertices_304, vertices_560, vertices_208, vertices_592, vertices_400, vertices_784, vertices_608, vertices_800, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_103), (false, vertices_395), (false, vertices_307), (false, vertices_707), (false, vertices_301), (false, vertices_653), (false, vertices_581), (true, vertices_146), (true, vertices_772), (true, vertices_152), (true, vertices_280), (true, vertices_536), (true, vertices_112), (true, vertices_560), (true, vertices_208), (true, vertices_592), (true, vertices_400), (true, vertices_784), (true, vertices_608), (true, vertices_800)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 18 14 22 23 24 25 26 27 28
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_103) then 15 else
  if p.val = (false, vertices_395) then 19 else
  if p.val = (false, vertices_307) then 20 else
  if p.val = (false, vertices_707) then 21 else
  if p.val = (false, vertices_301) then 16 else
  if p.val = (false, vertices_653) then 17 else
  if p.val = (false, vertices_581) then 0 else
  if p.val = (true, vertices_146) then 1 else
  if p.val = (true, vertices_772) then 2 else
  if p.val = (true, vertices_152) then 3 else
  if p.val = (true, vertices_280) then 4 else
  if p.val = (true, vertices_536) then 5 else
  if p.val = (true, vertices_112) then 6 else
  if p.val = (true, vertices_560) then 7 else
  if p.val = (true, vertices_208) then 8 else
  if p.val = (true, vertices_592) then 9 else
  if p.val = (true, vertices_400) then 10 else
  if p.val = (true, vertices_784) then 11 else
  if p.val = (true, vertices_608) then 12 else
  if p.val = (true, vertices_800) then 13 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_581), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_146), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_772), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_152), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_280), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_536), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_112), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_560), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_208), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_592), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_400), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_784), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_608), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_800), by decide +kernel⟩
  | 14 => Sum.inl 1
  | 15 => Sum.inr ⟨(false, vertices_103), by decide +kernel⟩
  | 16 => Sum.inr ⟨(false, vertices_301), by decide +kernel⟩
  | 17 => Sum.inr ⟨(false, vertices_653), by decide +kernel⟩
  | 18 => Sum.inl 0
  | 19 => Sum.inr ⟨(false, vertices_395), by decide +kernel⟩
  | 20 => Sum.inr ⟨(false, vertices_307), by decide +kernel⟩
  | 21 => Sum.inr ⟨(false, vertices_707), by decide +kernel⟩
  | 22 => Sum.inl 2
  | 23 => Sum.inl 3
  | 24 => Sum.inl 4
  | 25 => Sum.inl 5
  | 26 => Sum.inl 6
  | 27 => Sum.inl 7
  | 28 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 3 4 5 6 242 50 3
cert_row_4 1 1 4 5 7 8 868 100 3
cert_row_4 2 1 2 3 7 8 796 268 2
cert_row_4 3 2 3 5 6 8 728 152 2
cert_rows
cert_pivot_2 0 4 1 2
cert_heightProof 4
cert_coverFacet 0 242
cert_cover_5 0 0 0 3 4 5 50 242 3
cert_coverFacet 1 402
cert_cover_2 1 3 0 6 7 146 402 3
cert_coverFacet 2 796
cert_cover_5 2 2 1 2 3 7 268 796 2
cert_coverFacet 3 868
cert_cover_5 3 1 1 4 5 7 100 868 3
cert_coverFacet 4 728
cert_cover_5 4 3 2 3 5 6 152 728 2
cert_coverFacet 5 408
cert_cover_2 5 3 2 6 7 152 408 3
cert_coverFacet 6 624
cert_cover_2 6 4 3 5 8 112 624 3
cert_coverFacet 7 816
cert_cover_2 7 4 3 7 8 304 816 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q0_0019

end
end BundlePart12

section BundlePart13
/- Source: ProjectionCertificates/R_m15e10q0_0020.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q0_0020

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [307, 589, 565, 341, 809, 457, 182, 410, 714, 778, 674, 802, 212, 740, 464, 21, 69, 517, 73, 265, 521, 49, 273, 289, 545, 321, 138, 266, 522, 50, 146, 274, 162, 290, 546, 642, 770, 52, 84, 148, 164, 548, 196, 580, 200, 584, 392, 776, 208, 336, 400, 672, 800, 448, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_307, vertices_589, vertices_565, vertices_341, vertices_809, vertices_457, vertices_182, vertices_410, vertices_714, vertices_778, vertices_674, vertices_802, vertices_212, vertices_740, vertices_464] (by decide +kernel)
  polygons := literalFinset [vertices_21, vertices_69, vertices_517, vertices_73, vertices_265, vertices_521, vertices_49, vertices_273, vertices_289, vertices_545, vertices_321, vertices_138, vertices_266, vertices_522, vertices_50, vertices_146, vertices_274, vertices_162, vertices_290, vertices_546, vertices_642, vertices_770, vertices_52, vertices_84, vertices_148, vertices_164, vertices_548, vertices_196, vertices_580, vertices_200, vertices_584, vertices_392, vertices_776, vertices_208, vertices_336, vertices_400, vertices_672, vertices_800, vertices_448, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_307), (false, vertices_589), (false, vertices_565), (false, vertices_341), (false, vertices_809), (false, vertices_457), (true, vertices_138), (true, vertices_266), (true, vertices_522), (true, vertices_146), (true, vertices_162), (true, vertices_546), (true, vertices_642), (true, vertices_770), (true, vertices_148), (true, vertices_164), (true, vertices_196), (true, vertices_208), (true, vertices_400), (true, vertices_672), (true, vertices_704)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 17 21 24 25 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_307) then 16 else
  if p.val = (false, vertices_589) then 18 else
  if p.val = (false, vertices_565) then 19 else
  if p.val = (false, vertices_341) then 20 else
  if p.val = (false, vertices_809) then 22 else
  if p.val = (false, vertices_457) then 23 else
  if p.val = (true, vertices_138) then 0 else
  if p.val = (true, vertices_266) then 1 else
  if p.val = (true, vertices_522) then 2 else
  if p.val = (true, vertices_146) then 3 else
  if p.val = (true, vertices_162) then 4 else
  if p.val = (true, vertices_546) then 5 else
  if p.val = (true, vertices_642) then 6 else
  if p.val = (true, vertices_770) then 7 else
  if p.val = (true, vertices_148) then 8 else
  if p.val = (true, vertices_164) then 9 else
  if p.val = (true, vertices_196) then 10 else
  if p.val = (true, vertices_208) then 11 else
  if p.val = (true, vertices_400) then 12 else
  if p.val = (true, vertices_672) then 13 else
  if p.val = (true, vertices_704) then 14 else
  0
cert_priority
cert_nodeAtPriority_36 0 138 1 266 2 522 146 162 546 642 770 148 164 196 208 400 672 704 307 589 565 341 809 457
cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 2 3 6 7 410 138 2
cert_row_4 1 0 1 3 4 6 182 50 1
cert_row_4 2 0 2 5 6 8 714 138 2
cert_row_4 3 1 4 5 6 8 740 164 2
cert_rows
cert_pivot_2 7 3 0 1
cert_heightProof 4
cert_coverFacet 0 182
cert_cover_5 0 1 0 1 3 4 50 182 1
cert_coverFacet 1 410
cert_cover_5 1 0 0 2 3 6 138 410 2
cert_coverFacet 2 714
cert_cover_5 2 2 0 2 5 6 138 714 2
cert_coverFacet 3 778
cert_cover_2 3 2 0 7 8 266 778 3
cert_coverFacet 4 674
cert_cover_2 4 4 0 6 8 162 674 3
cert_coverFacet 5 802
cert_cover_2 5 4 0 7 8 290 802 3
cert_coverFacet 6 212
cert_cover_2 6 3 1 5 6 84 212 3
cert_coverFacet 7 740
cert_cover_5 7 3 1 4 5 6 164 740 2
cert_coverFacet 8 464
cert_cover_2 8 5 3 6 7 208 464 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q0_0020

end
end BundlePart13

section BundlePart14
/- Source: ProjectionCertificates/R_m15e10q0_0022.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q0_0022

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [611, 285, 597, 357, 665, 809, 422, 410, 714, 778, 226, 802, 244, 404, 720, 21, 69, 261, 25, 265, 521, 529, 97, 289, 545, 577, 138, 266, 522, 98, 162, 290, 546, 194, 578, 386, 770, 84, 148, 276, 100, 164, 292, 388, 152, 280, 648, 776, 208, 592, 400, 656, 224, 800, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_611, vertices_285, vertices_597, vertices_357, vertices_665, vertices_809, vertices_422, vertices_410, vertices_714, vertices_778, vertices_226, vertices_802, vertices_244, vertices_404, vertices_720] (by decide +kernel)
  polygons := literalFinset [vertices_21, vertices_69, vertices_261, vertices_25, vertices_265, vertices_521, vertices_529, vertices_97, vertices_289, vertices_545, vertices_577, vertices_138, vertices_266, vertices_522, vertices_98, vertices_162, vertices_290, vertices_546, vertices_194, vertices_578, vertices_386, vertices_770, vertices_84, vertices_148, vertices_276, vertices_100, vertices_164, vertices_292, vertices_388, vertices_152, vertices_280, vertices_648, vertices_776, vertices_208, vertices_592, vertices_400, vertices_656, vertices_224, vertices_800, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_611), (false, vertices_285), (false, vertices_597), (false, vertices_357), (false, vertices_665), (false, vertices_809), (true, vertices_138), (true, vertices_266), (true, vertices_522), (true, vertices_162), (true, vertices_290), (true, vertices_194), (true, vertices_386), (true, vertices_770), (true, vertices_148), (true, vertices_164), (true, vertices_388), (true, vertices_208), (true, vertices_400), (true, vertices_224), (true, vertices_704)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 17 21 24 25 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_611) then 16 else
  if p.val = (false, vertices_285) then 18 else
  if p.val = (false, vertices_597) then 19 else
  if p.val = (false, vertices_357) then 20 else
  if p.val = (false, vertices_665) then 22 else
  if p.val = (false, vertices_809) then 23 else
  if p.val = (true, vertices_138) then 0 else
  if p.val = (true, vertices_266) then 1 else
  if p.val = (true, vertices_522) then 2 else
  if p.val = (true, vertices_162) then 3 else
  if p.val = (true, vertices_290) then 4 else
  if p.val = (true, vertices_194) then 5 else
  if p.val = (true, vertices_386) then 6 else
  if p.val = (true, vertices_770) then 7 else
  if p.val = (true, vertices_148) then 8 else
  if p.val = (true, vertices_164) then 9 else
  if p.val = (true, vertices_388) then 10 else
  if p.val = (true, vertices_208) then 11 else
  if p.val = (true, vertices_400) then 12 else
  if p.val = (true, vertices_224) then 13 else
  if p.val = (true, vertices_704) then 14 else
  0
cert_priority
cert_nodeAtPriority_36 0 138 1 266 2 522 162 290 194 386 770 148 164 388 208 400 224 704 611 285 597 357 665 809
cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 2 5 6 8 714 138 2
cert_row_4 1 0 2 3 6 7 410 138 2
cert_row_4 2 0 1 4 6 7 422 162 1
cert_row_4 3 1 3 4 5 6 244 84 2
cert_rows
cert_pivot_2 8 2 0 1
cert_heightProof 4
cert_coverFacet 0 422
cert_cover_5 0 2 0 1 4 6 162 422 1
cert_coverFacet 1 410
cert_cover_5 1 1 0 2 3 6 138 410 2
cert_coverFacet 2 714
cert_cover_5 2 0 0 2 5 6 138 714 2
cert_coverFacet 3 778
cert_cover_2 3 2 0 7 8 266 778 3
cert_coverFacet 4 226
cert_cover_2 4 4 0 5 6 98 226 3
cert_coverFacet 5 802
cert_cover_2 5 4 0 7 8 290 802 3
cert_coverFacet 6 244
cert_cover_5 6 3 1 3 4 5 84 244 2
cert_coverFacet 7 404
cert_cover_2 7 3 1 6 7 148 404 3
cert_coverFacet 8 720
cert_cover_2 8 5 3 6 8 208 720 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q0_0022

end
end BundlePart14

section BundlePart15
/- Source: ProjectionCertificates/R_m15e10q0_0024.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q0_0024

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [563, 333, 653, 597, 809, 369, 398, 666, 778, 242, 418, 802, 484, 708, 720, 13, 69, 517, 265, 521, 49, 81, 529, 289, 545, 321, 138, 266, 522, 50, 146, 530, 162, 290, 546, 386, 770, 140, 268, 196, 324, 580, 388, 644, 648, 776, 112, 208, 592, 656, 224, 352, 416, 800, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_563, vertices_333, vertices_653, vertices_597, vertices_809, vertices_369, vertices_398, vertices_666, vertices_778, vertices_242, vertices_418, vertices_802, vertices_484, vertices_708, vertices_720] (by decide +kernel)
  polygons := literalFinset [vertices_13, vertices_69, vertices_517, vertices_265, vertices_521, vertices_49, vertices_81, vertices_529, vertices_289, vertices_545, vertices_321, vertices_138, vertices_266, vertices_522, vertices_50, vertices_146, vertices_530, vertices_162, vertices_290, vertices_546, vertices_386, vertices_770, vertices_140, vertices_268, vertices_196, vertices_324, vertices_580, vertices_388, vertices_644, vertices_648, vertices_776, vertices_112, vertices_208, vertices_592, vertices_656, vertices_224, vertices_352, vertices_416, vertices_800, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_563), (false, vertices_333), (false, vertices_653), (false, vertices_597), (false, vertices_809), (false, vertices_369), (true, vertices_138), (true, vertices_266), (true, vertices_522), (true, vertices_146), (true, vertices_162), (true, vertices_290), (true, vertices_386), (true, vertices_770), (true, vertices_196), (true, vertices_388), (true, vertices_208), (true, vertices_656), (true, vertices_224), (true, vertices_416), (true, vertices_704)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 17 21 23 25 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_563) then 16 else
  if p.val = (false, vertices_333) then 18 else
  if p.val = (false, vertices_653) then 19 else
  if p.val = (false, vertices_597) then 20 else
  if p.val = (false, vertices_809) then 22 else
  if p.val = (false, vertices_369) then 24 else
  if p.val = (true, vertices_138) then 0 else
  if p.val = (true, vertices_266) then 1 else
  if p.val = (true, vertices_522) then 2 else
  if p.val = (true, vertices_146) then 3 else
  if p.val = (true, vertices_162) then 4 else
  if p.val = (true, vertices_290) then 5 else
  if p.val = (true, vertices_386) then 6 else
  if p.val = (true, vertices_770) then 7 else
  if p.val = (true, vertices_196) then 8 else
  if p.val = (true, vertices_388) then 9 else
  if p.val = (true, vertices_208) then 10 else
  if p.val = (true, vertices_656) then 11 else
  if p.val = (true, vertices_224) then 12 else
  if p.val = (true, vertices_416) then 13 else
  if p.val = (true, vertices_704) then 14 else
  0
cert_priority
cert_nodeAtPriority_68 0 138 1 266 522 146 162 290 386 770 196 388 208 656 224 416 704 563 333 653 597 809 369
cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 2 3 6 8 666 138 2
cert_row_4 1 0 1 2 6 7 398 138 1
cert_row_4 2 0 3 4 5 6 242 50 3
cert_row_4 3 1 4 5 6 7 484 196 1
cert_rows
cert_pivot_2 8 2 0 1
cert_heightProof 4
cert_coverFacet 0 398
cert_cover_5 0 1 0 1 2 6 138 398 1
cert_coverFacet 1 666
cert_cover_5 1 0 0 2 3 6 138 666 2
cert_coverFacet 2 778
cert_cover_2 2 2 0 7 8 266 778 3
cert_coverFacet 3 242
cert_cover_5 3 2 0 3 4 5 50 242 3
cert_coverFacet 4 418
cert_cover_2 4 4 0 6 7 162 418 3
cert_coverFacet 5 802
cert_cover_2 5 4 0 7 8 290 802 3
cert_coverFacet 6 484
cert_cover_5 6 3 1 4 5 6 196 484 1
cert_coverFacet 7 708
cert_cover_2 7 5 1 6 8 196 708 3
cert_coverFacet 8 720
cert_cover_2 8 5 3 6 8 208 720 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q0_0024

end
end BundlePart15

section BundlePart16
/- Source: ProjectionCertificates/R_m15e10q0_0025.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q0_0025

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [55, 283, 587, 547, 341, 613, 457, 778, 434, 802, 716, 692, 212, 936, 464, 11, 19, 35, 515, 21, 37, 69, 73, 265, 273, 545, 321, 577, 266, 522, 50, 274, 290, 546, 770, 52, 84, 148, 548, 196, 580, 644, 200, 584, 392, 648, 776, 176, 208, 336, 400, 416, 672, 800, 448]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_55, vertices_283, vertices_587, vertices_547, vertices_341, vertices_613, vertices_457, vertices_778, vertices_434, vertices_802, vertices_716, vertices_692, vertices_212, vertices_936, vertices_464] (by decide +kernel)
  polygons := literalFinset [vertices_11, vertices_19, vertices_35, vertices_515, vertices_21, vertices_37, vertices_69, vertices_73, vertices_265, vertices_273, vertices_545, vertices_321, vertices_577, vertices_266, vertices_522, vertices_50, vertices_274, vertices_290, vertices_546, vertices_770, vertices_52, vertices_84, vertices_148, vertices_548, vertices_196, vertices_580, vertices_644, vertices_200, vertices_584, vertices_392, vertices_648, vertices_776, vertices_176, vertices_208, vertices_336, vertices_400, vertices_416, vertices_672, vertices_800, vertices_448] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_55), (false, vertices_283), (false, vertices_587), (false, vertices_547), (false, vertices_341), (false, vertices_613), (false, vertices_457), (true, vertices_290), (true, vertices_770), (true, vertices_148), (true, vertices_196), (true, vertices_644), (true, vertices_648), (true, vertices_776), (true, vertices_176), (true, vertices_208), (true, vertices_400), (true, vertices_416), (true, vertices_672), (true, vertices_800)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 14 18 21 23 24 25 26 27 28
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_55) then 15 else
  if p.val = (false, vertices_283) then 16 else
  if p.val = (false, vertices_587) then 17 else
  if p.val = (false, vertices_547) then 0 else
  if p.val = (false, vertices_341) then 19 else
  if p.val = (false, vertices_613) then 20 else
  if p.val = (false, vertices_457) then 22 else
  if p.val = (true, vertices_290) then 1 else
  if p.val = (true, vertices_770) then 2 else
  if p.val = (true, vertices_148) then 3 else
  if p.val = (true, vertices_196) then 4 else
  if p.val = (true, vertices_644) then 5 else
  if p.val = (true, vertices_648) then 6 else
  if p.val = (true, vertices_776) then 7 else
  if p.val = (true, vertices_176) then 8 else
  if p.val = (true, vertices_208) then 9 else
  if p.val = (true, vertices_400) then 10 else
  if p.val = (true, vertices_416) then 11 else
  if p.val = (true, vertices_672) then 12 else
  if p.val = (true, vertices_800) then 13 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_547), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_290), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_770), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_148), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_196), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_644), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_648), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_776), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_176), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_208), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_400), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_416), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_672), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_800), by decide +kernel⟩
  | 14 => Sum.inl 0
  | 15 => Sum.inr ⟨(false, vertices_55), by decide +kernel⟩
  | 16 => Sum.inr ⟨(false, vertices_283), by decide +kernel⟩
  | 17 => Sum.inr ⟨(false, vertices_587), by decide +kernel⟩
  | 18 => Sum.inl 1
  | 19 => Sum.inr ⟨(false, vertices_341), by decide +kernel⟩
  | 20 => Sum.inr ⟨(false, vertices_613), by decide +kernel⟩
  | 21 => Sum.inl 2
  | 22 => Sum.inr ⟨(false, vertices_457), by decide +kernel⟩
  | 23 => Sum.inl 3
  | 24 => Sum.inl 4
  | 25 => Sum.inl 5
  | 26 => Sum.inl 6
  | 27 => Sum.inl 7
  | 28 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 3 4 6 7 434 50 3
cert_row_4 1 1 2 5 6 8 716 196 1
cert_row_4 2 1 3 4 6 8 692 52 3
cert_row_4 3 2 4 6 7 8 936 392 1
cert_rows
cert_pivot_2 0 5 1 2
cert_heightProof 4
cert_coverFacet 0 778
cert_cover_2 0 2 0 7 8 266 778 3
cert_coverFacet 1 434
cert_cover_5 1 0 0 3 4 6 50 434 3
cert_coverFacet 2 802
cert_cover_2 2 4 0 7 8 290 802 3
cert_coverFacet 3 716
cert_cover_5 3 1 1 2 5 6 196 716 1
cert_coverFacet 4 692
cert_cover_5 4 2 1 3 4 6 52 692 3
cert_coverFacet 5 212
cert_cover_2 5 3 1 5 6 84 212 3
cert_coverFacet 6 936
cert_cover_5 6 3 2 4 6 7 392 936 1
cert_coverFacet 7 464
cert_cover_2 7 5 3 6 7 208 464 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q0_0025

end
end BundlePart16

section BundlePart17
/- Source: ProjectionCertificates/R_m15e10q0_0027.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q0_0027

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [535, 403, 227, 579, 309, 613, 425, 794, 962, 60, 604, 236, 312, 712, 904, 19, 67, 131, 515, 21, 37, 517, 273, 97, 161, 289, 577, 385, 274, 530, 194, 578, 386, 770, 28, 44, 76, 52, 532, 100, 580, 56, 280, 536, 168, 296, 200, 584, 392, 648, 776, 304, 224, 704, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_535, vertices_403, vertices_227, vertices_579, vertices_309, vertices_613, vertices_425, vertices_794, vertices_962, vertices_60, vertices_604, vertices_236, vertices_312, vertices_712, vertices_904] (by decide +kernel)
  polygons := literalFinset [vertices_19, vertices_67, vertices_131, vertices_515, vertices_21, vertices_37, vertices_517, vertices_273, vertices_97, vertices_161, vertices_289, vertices_577, vertices_385, vertices_274, vertices_530, vertices_194, vertices_578, vertices_386, vertices_770, vertices_28, vertices_44, vertices_76, vertices_52, vertices_532, vertices_100, vertices_580, vertices_56, vertices_280, vertices_536, vertices_168, vertices_296, vertices_200, vertices_584, vertices_392, vertices_648, vertices_776, vertices_304, vertices_224, vertices_704, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_535), (false, vertices_403), (false, vertices_227), (false, vertices_579), (false, vertices_309), (false, vertices_613), (false, vertices_425), (true, vertices_770), (true, vertices_28), (true, vertices_44), (true, vertices_76), (true, vertices_56), (true, vertices_280), (true, vertices_536), (true, vertices_200), (true, vertices_584), (true, vertices_648), (true, vertices_776), (true, vertices_704), (true, vertices_896)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 14 18 21 23 24 25 26 27 28
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_535) then 15 else
  if p.val = (false, vertices_403) then 16 else
  if p.val = (false, vertices_227) then 17 else
  if p.val = (false, vertices_579) then 0 else
  if p.val = (false, vertices_309) then 19 else
  if p.val = (false, vertices_613) then 20 else
  if p.val = (false, vertices_425) then 22 else
  if p.val = (true, vertices_770) then 1 else
  if p.val = (true, vertices_28) then 2 else
  if p.val = (true, vertices_44) then 3 else
  if p.val = (true, vertices_76) then 4 else
  if p.val = (true, vertices_56) then 5 else
  if p.val = (true, vertices_280) then 6 else
  if p.val = (true, vertices_536) then 7 else
  if p.val = (true, vertices_200) then 8 else
  if p.val = (true, vertices_584) then 9 else
  if p.val = (true, vertices_648) then 10 else
  if p.val = (true, vertices_776) then 11 else
  if p.val = (true, vertices_704) then 12 else
  if p.val = (true, vertices_896) then 13 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_579), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_770), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_28), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_44), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_76), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_56), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_280), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_536), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_200), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_584), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_648), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_776), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_704), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_896), by decide +kernel⟩
  | 14 => Sum.inl 0
  | 15 => Sum.inr ⟨(false, vertices_535), by decide +kernel⟩
  | 16 => Sum.inr ⟨(false, vertices_403), by decide +kernel⟩
  | 17 => Sum.inr ⟨(false, vertices_227), by decide +kernel⟩
  | 18 => Sum.inl 1
  | 19 => Sum.inr ⟨(false, vertices_309), by decide +kernel⟩
  | 20 => Sum.inr ⟨(false, vertices_613), by decide +kernel⟩
  | 21 => Sum.inl 2
  | 22 => Sum.inr ⟨(false, vertices_425), by decide +kernel⟩
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
cert_row_4 1 0 5 6 7 8 962 194 3
cert_row_4 2 0 2 3 7 8 794 274 1
cert_row_4 3 1 2 3 5 8 604 28 3
cert_rows
cert_pivot_2 4 6 0 1
cert_heightProof 4
cert_coverFacet 0 794
cert_cover_5 0 2 0 2 3 7 274 794 1
cert_coverFacet 1 962
cert_cover_5 1 1 0 5 6 7 194 962 3
cert_coverFacet 2 60
cert_cover_2 2 2 1 3 4 28 60 3
cert_coverFacet 3 604
cert_cover_5 3 3 1 2 3 5 28 604 3
cert_coverFacet 4 236
cert_cover_5 4 0 1 2 4 5 44 236 3
cert_coverFacet 5 312
cert_cover_2 5 3 2 4 7 56 312 3
cert_coverFacet 6 712
cert_cover_2 6 5 2 6 8 200 712 3
cert_coverFacet 7 904
cert_cover_2 7 6 2 7 8 392 904 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q0_0027

end
end BundlePart17

section BundlePart18
/- Source: ProjectionCertificates/R_m15e10q0_0029.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q0_0029

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [31, 267, 211, 419, 301, 597, 229, 538, 906, 658, 572, 612, 872, 976, 480, 11, 19, 131, 259, 13, 21, 37, 69, 265, 81, 161, 289, 193, 26, 266, 522, 146, 530, 386, 642, 28, 44, 532, 100, 548, 580, 536, 296, 552, 776, 208, 592, 656, 224, 352, 608, 416, 448, 832, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_31, vertices_267, vertices_211, vertices_419, vertices_301, vertices_597, vertices_229, vertices_538, vertices_906, vertices_658, vertices_572, vertices_612, vertices_872, vertices_976, vertices_480] (by decide +kernel)
  polygons := literalFinset [vertices_11, vertices_19, vertices_131, vertices_259, vertices_13, vertices_21, vertices_37, vertices_69, vertices_265, vertices_81, vertices_161, vertices_289, vertices_193, vertices_26, vertices_266, vertices_522, vertices_146, vertices_530, vertices_386, vertices_642, vertices_28, vertices_44, vertices_532, vertices_100, vertices_548, vertices_580, vertices_536, vertices_296, vertices_552, vertices_776, vertices_208, vertices_592, vertices_656, vertices_224, vertices_352, vertices_608, vertices_416, vertices_448, vertices_832, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_31), (false, vertices_267), (false, vertices_211), (false, vertices_419), (false, vertices_301), (false, vertices_597), (false, vertices_229), (true, vertices_522), (true, vertices_530), (true, vertices_642), (true, vertices_548), (true, vertices_536), (true, vertices_552), (true, vertices_776), (true, vertices_656), (true, vertices_352), (true, vertices_608), (true, vertices_448), (true, vertices_832), (true, vertices_896)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 14 18 22 23 24 25 26 27 28
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_31) then 15 else
  if p.val = (false, vertices_267) then 0 else
  if p.val = (false, vertices_211) then 16 else
  if p.val = (false, vertices_419) then 17 else
  if p.val = (false, vertices_301) then 19 else
  if p.val = (false, vertices_597) then 20 else
  if p.val = (false, vertices_229) then 21 else
  if p.val = (true, vertices_522) then 1 else
  if p.val = (true, vertices_530) then 2 else
  if p.val = (true, vertices_642) then 3 else
  if p.val = (true, vertices_548) then 4 else
  if p.val = (true, vertices_536) then 5 else
  if p.val = (true, vertices_552) then 6 else
  if p.val = (true, vertices_776) then 7 else
  if p.val = (true, vertices_656) then 8 else
  if p.val = (true, vertices_352) then 9 else
  if p.val = (true, vertices_608) then 10 else
  if p.val = (true, vertices_448) then 11 else
  if p.val = (true, vertices_832) then 12 else
  if p.val = (true, vertices_896) then 13 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_267), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_522), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_530), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_642), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_548), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_536), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_552), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_776), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_656), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_352), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_608), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_448), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_832), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_896), by decide +kernel⟩
  | 14 => Sum.inl 0
  | 15 => Sum.inr ⟨(false, vertices_31), by decide +kernel⟩
  | 16 => Sum.inr ⟨(false, vertices_211), by decide +kernel⟩
  | 17 => Sum.inr ⟨(false, vertices_419), by decide +kernel⟩
  | 18 => Sum.inl 1
  | 19 => Sum.inr ⟨(false, vertices_301), by decide +kernel⟩
  | 20 => Sum.inr ⟨(false, vertices_597), by decide +kernel⟩
  | 21 => Sum.inr ⟨(false, vertices_229), by decide +kernel⟩
  | 22 => Sum.inl 2
  | 23 => Sum.inl 3
  | 24 => Sum.inl 4
  | 25 => Sum.inl 5
  | 26 => Sum.inl 6
  | 27 => Sum.inl 7
  | 28 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 2 6 7 8 906 266 2
cert_row_4 1 1 2 3 4 8 572 28 3
cert_row_4 2 2 4 5 7 8 872 296 2
cert_row_4 3 3 5 6 7 8 976 208 3
cert_rows
cert_pivot_2 0 1 2 3
cert_heightProof 4
cert_coverFacet 0 538
cert_cover_2 0 2 0 3 8 26 538 3
cert_coverFacet 1 906
cert_cover_5 1 0 0 2 6 7 266 906 2
cert_coverFacet 2 658
cert_cover_2 2 3 0 6 8 146 658 3
cert_coverFacet 3 572
cert_cover_5 3 1 1 2 3 4 28 572 3
cert_coverFacet 4 612
cert_cover_2 4 4 1 5 8 100 612 3
cert_coverFacet 5 872
cert_cover_5 5 2 2 4 5 7 296 872 2
cert_coverFacet 6 976
cert_cover_5 6 3 3 5 6 7 208 976 3
cert_coverFacet 7 480
cert_cover_2 7 5 4 6 7 224 480 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q0_0029

end
end BundlePart18

section BundlePart19
/- Source: ProjectionCertificates/R_m15e10q0_0030.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q0_0030

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [283, 651, 595, 709, 425, 241, 305, 782, 818, 460, 652, 628, 356, 804, 480, 11, 19, 515, 137, 265, 49, 81, 273, 161, 289, 193, 577, 641, 266, 522, 274, 530, 770, 140, 268, 524, 100, 292, 548, 196, 324, 580, 644, 772, 392, 648, 112, 304, 560, 592, 224, 352, 416, 800, 448]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_283, vertices_651, vertices_595, vertices_709, vertices_425, vertices_241, vertices_305, vertices_782, vertices_818, vertices_460, vertices_652, vertices_628, vertices_356, vertices_804, vertices_480] (by decide +kernel)
  polygons := literalFinset [vertices_11, vertices_19, vertices_515, vertices_137, vertices_265, vertices_49, vertices_81, vertices_273, vertices_161, vertices_289, vertices_193, vertices_577, vertices_641, vertices_266, vertices_522, vertices_274, vertices_530, vertices_770, vertices_140, vertices_268, vertices_524, vertices_100, vertices_292, vertices_548, vertices_196, vertices_324, vertices_580, vertices_644, vertices_772, vertices_392, vertices_648, vertices_112, vertices_304, vertices_560, vertices_592, vertices_224, vertices_352, vertices_416, vertices_800, vertices_448] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_283), (false, vertices_651), (false, vertices_595), (false, vertices_709), (false, vertices_425), (false, vertices_241), (false, vertices_305), (true, vertices_770), (true, vertices_140), (true, vertices_268), (true, vertices_524), (true, vertices_100), (true, vertices_292), (true, vertices_548), (true, vertices_324), (true, vertices_772), (true, vertices_560), (true, vertices_352), (true, vertices_800), (true, vertices_448)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 14 18 20 22 24 25 26 27 28
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_283) then 15 else
  if p.val = (false, vertices_651) then 16 else
  if p.val = (false, vertices_595) then 17 else
  if p.val = (false, vertices_709) then 19 else
  if p.val = (false, vertices_425) then 21 else
  if p.val = (false, vertices_241) then 23 else
  if p.val = (false, vertices_305) then 0 else
  if p.val = (true, vertices_770) then 1 else
  if p.val = (true, vertices_140) then 2 else
  if p.val = (true, vertices_268) then 3 else
  if p.val = (true, vertices_524) then 4 else
  if p.val = (true, vertices_100) then 5 else
  if p.val = (true, vertices_292) then 6 else
  if p.val = (true, vertices_548) then 7 else
  if p.val = (true, vertices_324) then 8 else
  if p.val = (true, vertices_772) then 9 else
  if p.val = (true, vertices_560) then 10 else
  if p.val = (true, vertices_352) then 11 else
  if p.val = (true, vertices_800) then 12 else
  if p.val = (true, vertices_448) then 13 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_305), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_770), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_140), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_268), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_524), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_100), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_292), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_548), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_324), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_772), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_560), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_352), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_800), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_448), by decide +kernel⟩
  | 14 => Sum.inl 0
  | 15 => Sum.inr ⟨(false, vertices_283), by decide +kernel⟩
  | 16 => Sum.inr ⟨(false, vertices_651), by decide +kernel⟩
  | 17 => Sum.inr ⟨(false, vertices_595), by decide +kernel⟩
  | 18 => Sum.inl 1
  | 19 => Sum.inr ⟨(false, vertices_709), by decide +kernel⟩
  | 20 => Sum.inl 2
  | 21 => Sum.inr ⟨(false, vertices_425), by decide +kernel⟩
  | 22 => Sum.inl 3
  | 23 => Sum.inr ⟨(false, vertices_241), by decide +kernel⟩
  | 24 => Sum.inl 4
  | 25 => Sum.inl 5
  | 26 => Sum.inl 6
  | 27 => Sum.inl 7
  | 28 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 1 2 5 6 7 460 140 2
cert_row_4 1 0 1 2 7 8 782 266 1
cert_row_4 2 0 3 4 7 8 818 274 2
cert_row_4 3 1 3 4 5 8 628 100 1
cert_rows
cert_pivot_2 6 2 0 1
cert_heightProof 4
cert_coverFacet 0 782
cert_cover_5 0 1 0 1 2 7 266 782 1
cert_coverFacet 1 818
cert_cover_5 1 2 0 3 4 7 274 818 2
cert_coverFacet 2 460
cert_cover_5 2 0 1 2 5 6 140 460 2
cert_coverFacet 3 652
cert_cover_2 3 2 1 6 8 140 652 3
cert_coverFacet 4 628
cert_cover_5 4 3 1 3 4 5 100 628 1
cert_coverFacet 5 356
cert_cover_2 5 4 1 5 7 100 356 3
cert_coverFacet 6 804
cert_cover_2 6 4 1 7 8 292 804 3
cert_coverFacet 7 480
cert_cover_2 7 5 4 6 7 224 480 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q0_0030

end
end BundlePart19

section BundlePart20
/- Source: ProjectionCertificates/R_m15e10q0_0031.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q0_0031

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [203, 355, 675, 301, 653, 565, 329, 310, 178, 466, 844, 788, 728, 688, 848, 35, 67, 131, 13, 37, 517, 73, 137, 265, 289, 545, 321, 641, 50, 146, 274, 162, 290, 194, 322, 268, 524, 52, 276, 532, 292, 772, 200, 328, 584, 648, 176, 560, 208, 336, 592, 656, 784, 672, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_203, vertices_355, vertices_675, vertices_301, vertices_653, vertices_565, vertices_329, vertices_310, vertices_178, vertices_466, vertices_844, vertices_788, vertices_728, vertices_688, vertices_848] (by decide +kernel)
  polygons := literalFinset [vertices_35, vertices_67, vertices_131, vertices_13, vertices_37, vertices_517, vertices_73, vertices_137, vertices_265, vertices_289, vertices_545, vertices_321, vertices_641, vertices_50, vertices_146, vertices_274, vertices_162, vertices_290, vertices_194, vertices_322, vertices_268, vertices_524, vertices_52, vertices_276, vertices_532, vertices_292, vertices_772, vertices_200, vertices_328, vertices_584, vertices_648, vertices_176, vertices_560, vertices_208, vertices_336, vertices_592, vertices_656, vertices_784, vertices_672, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_203), (false, vertices_355), (false, vertices_675), (false, vertices_301), (false, vertices_653), (false, vertices_565), (false, vertices_329), (true, vertices_50), (true, vertices_146), (true, vertices_274), (true, vertices_276), (true, vertices_772), (true, vertices_584), (true, vertices_176), (true, vertices_208), (true, vertices_336), (true, vertices_592), (true, vertices_656), (true, vertices_784), (true, vertices_832)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 14 18 22 23 24 25 26 27 28
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_203) then 15 else
  if p.val = (false, vertices_355) then 16 else
  if p.val = (false, vertices_675) then 17 else
  if p.val = (false, vertices_301) then 19 else
  if p.val = (false, vertices_653) then 20 else
  if p.val = (false, vertices_565) then 21 else
  if p.val = (false, vertices_329) then 0 else
  if p.val = (true, vertices_50) then 1 else
  if p.val = (true, vertices_146) then 2 else
  if p.val = (true, vertices_274) then 3 else
  if p.val = (true, vertices_276) then 4 else
  if p.val = (true, vertices_772) then 5 else
  if p.val = (true, vertices_584) then 6 else
  if p.val = (true, vertices_176) then 7 else
  if p.val = (true, vertices_208) then 8 else
  if p.val = (true, vertices_336) then 9 else
  if p.val = (true, vertices_592) then 10 else
  if p.val = (true, vertices_656) then 11 else
  if p.val = (true, vertices_784) then 12 else
  if p.val = (true, vertices_832) then 13 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_329), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_50), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_146), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_274), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_276), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_772), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_584), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_176), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_208), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_336), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_592), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_656), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_784), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_832), by decide +kernel⟩
  | 14 => Sum.inl 0
  | 15 => Sum.inr ⟨(false, vertices_203), by decide +kernel⟩
  | 16 => Sum.inr ⟨(false, vertices_355), by decide +kernel⟩
  | 17 => Sum.inr ⟨(false, vertices_675), by decide +kernel⟩
  | 18 => Sum.inl 1
  | 19 => Sum.inr ⟨(false, vertices_301), by decide +kernel⟩
  | 20 => Sum.inr ⟨(false, vertices_653), by decide +kernel⟩
  | 21 => Sum.inr ⟨(false, vertices_565), by decide +kernel⟩
  | 22 => Sum.inl 2
  | 23 => Sum.inl 3
  | 24 => Sum.inl 4
  | 25 => Sum.inl 5
  | 26 => Sum.inl 6
  | 27 => Sum.inl 7
  | 28 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 3 4 7 310 50 1
cert_row_4 1 0 3 5 6 7 466 146 2
cert_row_4 2 1 2 5 7 8 844 268 2
cert_row_4 3 2 3 5 6 8 728 200 1
cert_rows
cert_pivot_2 4 0 1 2
cert_heightProof 4
cert_coverFacet 0 310
cert_cover_5 0 0 0 1 3 4 50 310 1
cert_coverFacet 1 178
cert_cover_2 1 3 0 4 6 50 178 3
cert_coverFacet 2 466
cert_cover_5 2 1 0 3 5 6 146 466 2
cert_coverFacet 3 844
cert_cover_5 3 2 1 2 5 7 268 844 2
cert_coverFacet 4 788
cert_cover_2 4 3 1 7 8 276 788 3
cert_coverFacet 5 728
cert_cover_5 5 3 2 3 5 6 200 728 1
cert_coverFacet 6 688
cert_cover_2 6 4 3 6 8 176 688 3
cert_coverFacet 7 848
cert_cover_2 7 5 3 7 8 336 848 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q0_0031

end
end BundlePart20

section BundlePart21
/- Source: ProjectionCertificates/R_m15e10q0_0033.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q0_0033

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [527, 203, 419, 771, 109, 805, 241, 602, 706, 898, 60, 796, 436, 120, 976, 11, 131, 259, 515, 13, 37, 517, 73, 97, 161, 289, 193, 769, 74, 522, 194, 578, 386, 642, 770, 28, 44, 524, 52, 276, 292, 772, 56, 88, 536, 104, 112, 176, 208, 592, 400, 784, 416, 704, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_527, vertices_203, vertices_419, vertices_771, vertices_109, vertices_805, vertices_241, vertices_602, vertices_706, vertices_898, vertices_60, vertices_796, vertices_436, vertices_120, vertices_976] (by decide +kernel)
  polygons := literalFinset [vertices_11, vertices_131, vertices_259, vertices_515, vertices_13, vertices_37, vertices_517, vertices_73, vertices_97, vertices_161, vertices_289, vertices_193, vertices_769, vertices_74, vertices_522, vertices_194, vertices_578, vertices_386, vertices_642, vertices_770, vertices_28, vertices_44, vertices_524, vertices_52, vertices_276, vertices_292, vertices_772, vertices_56, vertices_88, vertices_536, vertices_104, vertices_112, vertices_176, vertices_208, vertices_592, vertices_400, vertices_784, vertices_416, vertices_704, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_527), (false, vertices_203), (false, vertices_419), (false, vertices_771), (false, vertices_109), (false, vertices_805), (false, vertices_241), (true, vertices_578), (true, vertices_642), (true, vertices_28), (true, vertices_52), (true, vertices_276), (true, vertices_56), (true, vertices_88), (true, vertices_536), (true, vertices_592), (true, vertices_400), (true, vertices_784), (true, vertices_704), (true, vertices_896)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 14 18 21 22 24 25 26 27 28
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_527) then 15 else
  if p.val = (false, vertices_203) then 16 else
  if p.val = (false, vertices_419) then 17 else
  if p.val = (false, vertices_771) then 0 else
  if p.val = (false, vertices_109) then 19 else
  if p.val = (false, vertices_805) then 20 else
  if p.val = (false, vertices_241) then 23 else
  if p.val = (true, vertices_578) then 1 else
  if p.val = (true, vertices_642) then 2 else
  if p.val = (true, vertices_28) then 3 else
  if p.val = (true, vertices_52) then 4 else
  if p.val = (true, vertices_276) then 5 else
  if p.val = (true, vertices_56) then 6 else
  if p.val = (true, vertices_88) then 7 else
  if p.val = (true, vertices_536) then 8 else
  if p.val = (true, vertices_592) then 9 else
  if p.val = (true, vertices_400) then 10 else
  if p.val = (true, vertices_784) then 11 else
  if p.val = (true, vertices_704) then 12 else
  if p.val = (true, vertices_896) then 13 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_771), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_578), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_642), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_28), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_52), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_276), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_56), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_88), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_536), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_592), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_400), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_784), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_704), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_896), by decide +kernel⟩
  | 14 => Sum.inl 0
  | 15 => Sum.inr ⟨(false, vertices_527), by decide +kernel⟩
  | 16 => Sum.inr ⟨(false, vertices_203), by decide +kernel⟩
  | 17 => Sum.inr ⟨(false, vertices_419), by decide +kernel⟩
  | 18 => Sum.inl 1
  | 19 => Sum.inr ⟨(false, vertices_109), by decide +kernel⟩
  | 20 => Sum.inr ⟨(false, vertices_805), by decide +kernel⟩
  | 21 => Sum.inl 2
  | 22 => Sum.inl 3
  | 23 => Sum.inr ⟨(false, vertices_241), by decide +kernel⟩
  | 24 => Sum.inl 4
  | 25 => Sum.inl 5
  | 26 => Sum.inl 6
  | 27 => Sum.inl 7
  | 28 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 2 3 5 8 602 74 2
cert_row_4 1 1 2 3 7 8 796 28 3
cert_row_4 2 1 3 4 6 7 436 52 3
cert_row_4 3 3 5 6 7 8 976 208 3
cert_rows
cert_pivot_2 0 2 1 3
cert_heightProof 4
cert_coverFacet 0 602
cert_cover_5 0 0 0 2 3 5 74 602 2
cert_coverFacet 1 706
cert_cover_2 1 5 0 6 8 194 706 3
cert_coverFacet 2 898
cert_cover_2 2 6 0 7 8 386 898 3
cert_coverFacet 3 60
cert_cover_2 3 2 1 3 4 28 60 3
cert_coverFacet 4 796
cert_cover_5 4 1 1 2 3 7 28 796 3
cert_coverFacet 5 436
cert_cover_5 5 2 1 3 4 6 52 436 3
cert_coverFacet 6 120
cert_cover_2 6 3 2 4 5 56 120 3
cert_coverFacet 7 976
cert_cover_5 7 3 3 5 6 7 208 976 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q0_0033

end
end BundlePart21

section BundlePart22
/- Source: ProjectionCertificates/R_m15e10q0_0034.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q0_0034

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [779, 589, 117, 661, 361, 817, 182, 666, 458, 306, 786, 418, 484, 708, 712, 21, 69, 517, 73, 265, 521, 49, 529, 97, 289, 769, 138, 266, 522, 50, 146, 274, 530, 162, 290, 386, 770, 52, 148, 100, 164, 196, 580, 644, 200, 328, 584, 648, 304, 656, 784, 352, 416, 448, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_779, vertices_589, vertices_117, vertices_661, vertices_361, vertices_817, vertices_182, vertices_666, vertices_458, vertices_306, vertices_786, vertices_418, vertices_484, vertices_708, vertices_712] (by decide +kernel)
  polygons := literalFinset [vertices_21, vertices_69, vertices_517, vertices_73, vertices_265, vertices_521, vertices_49, vertices_529, vertices_97, vertices_289, vertices_769, vertices_138, vertices_266, vertices_522, vertices_50, vertices_146, vertices_274, vertices_530, vertices_162, vertices_290, vertices_386, vertices_770, vertices_52, vertices_148, vertices_100, vertices_164, vertices_196, vertices_580, vertices_644, vertices_200, vertices_328, vertices_584, vertices_648, vertices_304, vertices_656, vertices_784, vertices_352, vertices_416, vertices_448, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_779), (false, vertices_589), (false, vertices_117), (false, vertices_661), (false, vertices_361), (false, vertices_817), (true, vertices_138), (true, vertices_50), (true, vertices_146), (true, vertices_274), (true, vertices_530), (true, vertices_162), (true, vertices_290), (true, vertices_386), (true, vertices_164), (true, vertices_196), (true, vertices_200), (true, vertices_648), (true, vertices_416), (true, vertices_448), (true, vertices_704)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 17 21 23 25 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_779) then 16 else
  if p.val = (false, vertices_589) then 18 else
  if p.val = (false, vertices_117) then 19 else
  if p.val = (false, vertices_661) then 20 else
  if p.val = (false, vertices_361) then 22 else
  if p.val = (false, vertices_817) then 24 else
  if p.val = (true, vertices_138) then 0 else
  if p.val = (true, vertices_50) then 1 else
  if p.val = (true, vertices_146) then 2 else
  if p.val = (true, vertices_274) then 3 else
  if p.val = (true, vertices_530) then 4 else
  if p.val = (true, vertices_162) then 5 else
  if p.val = (true, vertices_290) then 6 else
  if p.val = (true, vertices_386) then 7 else
  if p.val = (true, vertices_164) then 8 else
  if p.val = (true, vertices_196) then 9 else
  if p.val = (true, vertices_200) then 10 else
  if p.val = (true, vertices_648) then 11 else
  if p.val = (true, vertices_416) then 12 else
  if p.val = (true, vertices_448) then 13 else
  if p.val = (true, vertices_704) then 14 else
  0
cert_priority
cert_nodeAtPriority_68 0 138 1 50 146 274 530 162 290 386 164 196 200 648 416 448 704 779 589 117 661 361 817
cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 2 3 6 8 666 138 2
cert_row_4 1 0 1 3 4 6 182 50 1
cert_row_4 2 0 2 5 6 7 458 138 2
cert_row_4 3 1 4 5 6 7 484 100 3
cert_rows
cert_pivot_2 8 3 0 1
cert_heightProof 4
cert_coverFacet 0 182
cert_cover_5 0 1 0 1 3 4 50 182 1
cert_coverFacet 1 666
cert_cover_5 1 0 0 2 3 6 138 666 2
cert_coverFacet 2 458
cert_cover_5 2 2 0 2 5 6 138 458 2
cert_coverFacet 3 306
cert_cover_2 3 3 0 4 7 50 306 3
cert_coverFacet 4 786
cert_cover_2 4 3 0 7 8 274 786 3
cert_coverFacet 5 418
cert_cover_2 5 4 0 6 7 162 418 3
cert_coverFacet 6 484
cert_cover_5 6 3 1 4 5 6 100 484 3
cert_coverFacet 7 708
cert_cover_2 7 5 1 6 8 196 708 3
cert_coverFacet 8 712
cert_cover_2 8 5 2 6 8 200 712 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q0_0034

end
end BundlePart22

section BundlePart23
/- Source: ProjectionCertificates/R_m15e10q0_0035.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q0_0035

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [279, 299, 179, 333, 213, 105, 737, 722, 786, 418, 898, 796, 620, 596, 936, 19, 35, 259, 21, 69, 261, 41, 73, 265, 145, 97, 161, 193, 146, 274, 530, 162, 290, 386, 642, 770, 76, 268, 524, 84, 276, 532, 580, 104, 296, 552, 776, 208, 592, 784, 608, 416, 672, 704, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_279, vertices_299, vertices_179, vertices_333, vertices_213, vertices_105, vertices_737, vertices_722, vertices_786, vertices_418, vertices_898, vertices_796, vertices_620, vertices_596, vertices_936] (by decide +kernel)
  polygons := literalFinset [vertices_19, vertices_35, vertices_259, vertices_21, vertices_69, vertices_261, vertices_41, vertices_73, vertices_265, vertices_145, vertices_97, vertices_161, vertices_193, vertices_146, vertices_274, vertices_530, vertices_162, vertices_290, vertices_386, vertices_642, vertices_770, vertices_76, vertices_268, vertices_524, vertices_84, vertices_276, vertices_532, vertices_580, vertices_104, vertices_296, vertices_552, vertices_776, vertices_208, vertices_592, vertices_784, vertices_608, vertices_416, vertices_672, vertices_704, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_279), (false, vertices_299), (false, vertices_179), (false, vertices_333), (false, vertices_213), (false, vertices_105), (false, vertices_737), (true, vertices_530), (true, vertices_386), (true, vertices_642), (true, vertices_770), (true, vertices_524), (true, vertices_532), (true, vertices_580), (true, vertices_552), (true, vertices_776), (true, vertices_592), (true, vertices_784), (true, vertices_416), (true, vertices_896)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 14 18 21 22 23 25 26 27 28
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_279) then 15 else
  if p.val = (false, vertices_299) then 16 else
  if p.val = (false, vertices_179) then 17 else
  if p.val = (false, vertices_333) then 19 else
  if p.val = (false, vertices_213) then 20 else
  if p.val = (false, vertices_105) then 0 else
  if p.val = (false, vertices_737) then 24 else
  if p.val = (true, vertices_530) then 1 else
  if p.val = (true, vertices_386) then 2 else
  if p.val = (true, vertices_642) then 3 else
  if p.val = (true, vertices_770) then 4 else
  if p.val = (true, vertices_524) then 5 else
  if p.val = (true, vertices_532) then 6 else
  if p.val = (true, vertices_580) then 7 else
  if p.val = (true, vertices_552) then 8 else
  if p.val = (true, vertices_776) then 9 else
  if p.val = (true, vertices_592) then 10 else
  if p.val = (true, vertices_784) then 11 else
  if p.val = (true, vertices_416) then 12 else
  if p.val = (true, vertices_896) then 13 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_105), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_530), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_386), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_642), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_770), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_524), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_532), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_580), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_552), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_776), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_592), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_784), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_416), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_896), by decide +kernel⟩
  | 14 => Sum.inl 0
  | 15 => Sum.inr ⟨(false, vertices_279), by decide +kernel⟩
  | 16 => Sum.inr ⟨(false, vertices_299), by decide +kernel⟩
  | 17 => Sum.inr ⟨(false, vertices_179), by decide +kernel⟩
  | 18 => Sum.inl 1
  | 19 => Sum.inr ⟨(false, vertices_333), by decide +kernel⟩
  | 20 => Sum.inr ⟨(false, vertices_213), by decide +kernel⟩
  | 21 => Sum.inl 2
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
cert_row_4 0 0 3 5 6 8 722 146 2
cert_row_4 1 1 2 3 7 8 796 268 2
cert_row_4 2 1 2 4 5 8 620 76 2
cert_row_4 3 2 4 6 7 8 936 296 2
cert_rows
cert_pivot_2 0 3 1 2
cert_heightProof 4
cert_coverFacet 0 722
cert_cover_5 0 0 0 3 5 6 146 722 2
cert_coverFacet 1 786
cert_cover_2 1 3 0 7 8 274 786 3
cert_coverFacet 2 418
cert_cover_2 2 4 0 6 7 162 418 3
cert_coverFacet 3 898
cert_cover_2 3 6 0 7 8 386 898 3
cert_coverFacet 4 796
cert_cover_5 4 1 1 2 3 7 268 796 2
cert_coverFacet 5 620
cert_cover_5 5 2 1 2 4 5 76 620 2
cert_coverFacet 6 596
cert_cover_2 6 3 1 5 8 84 596 3
cert_coverFacet 7 936
cert_cover_5 7 3 2 4 6 7 296 936 2
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q0_0035

end
end BundlePart23

section BundlePart24
/- Source: ProjectionCertificates/R_m15e10q0_0036.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q0_0036

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [651, 115, 787, 195, 781, 313, 233, 710, 594, 684, 300, 852, 420, 452, 496, 19, 67, 131, 515, 41, 137, 265, 521, 49, 273, 97, 193, 769, 82, 530, 194, 578, 642, 44, 268, 524, 164, 292, 196, 324, 580, 388, 644, 772, 168, 296, 648, 112, 304, 336, 592, 784, 224, 416, 448]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_651, vertices_115, vertices_787, vertices_195, vertices_781, vertices_313, vertices_233, vertices_710, vertices_594, vertices_684, vertices_300, vertices_852, vertices_420, vertices_452, vertices_496] (by decide +kernel)
  polygons := literalFinset [vertices_19, vertices_67, vertices_131, vertices_515, vertices_41, vertices_137, vertices_265, vertices_521, vertices_49, vertices_273, vertices_97, vertices_193, vertices_769, vertices_82, vertices_530, vertices_194, vertices_578, vertices_642, vertices_44, vertices_268, vertices_524, vertices_164, vertices_292, vertices_196, vertices_324, vertices_580, vertices_388, vertices_644, vertices_772, vertices_168, vertices_296, vertices_648, vertices_112, vertices_304, vertices_336, vertices_592, vertices_784, vertices_224, vertices_416, vertices_448] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_651), (false, vertices_115), (false, vertices_787), (false, vertices_195), (false, vertices_781), (false, vertices_313), (false, vertices_233), (true, vertices_578), (true, vertices_44), (true, vertices_164), (true, vertices_292), (true, vertices_196), (true, vertices_324), (true, vertices_580), (true, vertices_388), (true, vertices_644), (true, vertices_336), (true, vertices_592), (true, vertices_416), (true, vertices_448)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 14 18 20 23 24 25 26 27 28
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_651) then 15 else
  if p.val = (false, vertices_115) then 16 else
  if p.val = (false, vertices_787) then 17 else
  if p.val = (false, vertices_195) then 0 else
  if p.val = (false, vertices_781) then 19 else
  if p.val = (false, vertices_313) then 21 else
  if p.val = (false, vertices_233) then 22 else
  if p.val = (true, vertices_578) then 1 else
  if p.val = (true, vertices_44) then 2 else
  if p.val = (true, vertices_164) then 3 else
  if p.val = (true, vertices_292) then 4 else
  if p.val = (true, vertices_196) then 5 else
  if p.val = (true, vertices_324) then 6 else
  if p.val = (true, vertices_580) then 7 else
  if p.val = (true, vertices_388) then 8 else
  if p.val = (true, vertices_644) then 9 else
  if p.val = (true, vertices_336) then 10 else
  if p.val = (true, vertices_592) then 11 else
  if p.val = (true, vertices_416) then 12 else
  if p.val = (true, vertices_448) then 13 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_195), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_578), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_44), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_164), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_292), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_196), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_324), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_580), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_388), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_644), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_336), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_592), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_416), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_448), by decide +kernel⟩
  | 14 => Sum.inl 0
  | 15 => Sum.inr ⟨(false, vertices_651), by decide +kernel⟩
  | 16 => Sum.inr ⟨(false, vertices_115), by decide +kernel⟩
  | 17 => Sum.inr ⟨(false, vertices_787), by decide +kernel⟩
  | 18 => Sum.inl 1
  | 19 => Sum.inr ⟨(false, vertices_781), by decide +kernel⟩
  | 20 => Sum.inl 2
  | 21 => Sum.inr ⟨(false, vertices_313), by decide +kernel⟩
  | 22 => Sum.inr ⟨(false, vertices_233), by decide +kernel⟩
  | 23 => Sum.inl 3
  | 24 => Sum.inl 4
  | 25 => Sum.inl 5
  | 26 => Sum.inl 6
  | 27 => Sum.inl 7
  | 28 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 5 6 8 710 194 1
cert_row_4 1 1 2 4 6 8 684 44 3
cert_row_4 2 1 3 5 7 8 852 324 1
cert_row_4 3 3 4 5 6 7 496 112 3
cert_rows
cert_pivot_2 0 2 1 3
cert_heightProof 4
cert_coverFacet 0 710
cert_cover_5 0 0 0 1 5 6 194 710 1
cert_coverFacet 1 594
cert_cover_2 1 3 0 5 8 82 594 3
cert_coverFacet 2 684
cert_cover_5 2 1 1 2 4 6 44 684 3
cert_coverFacet 3 300
cert_cover_2 3 2 1 4 7 44 300 3
cert_coverFacet 4 852
cert_cover_5 4 2 1 3 5 7 324 852 1
cert_coverFacet 5 420
cert_cover_2 5 4 1 6 7 164 420 3
cert_coverFacet 6 452
cert_cover_2 6 5 1 6 7 196 452 3
cert_coverFacet 7 496
cert_cover_5 7 3 3 4 5 6 112 496 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q0_0036

end
end BundlePart24

section BundlePart25
/- Source: ProjectionCertificates/R_m15e10q0_0038.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q0_0038

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [535, 307, 675, 341, 901, 425, 282, 538, 618, 298, 604, 740, 452, 472, 232, 19, 35, 515, 21, 261, 517, 273, 161, 289, 385, 641, 26, 42, 266, 522, 274, 530, 290, 546, 84, 532, 196, 324, 580, 388, 644, 88, 280, 536, 104, 168, 296, 200, 584, 392, 336, 224, 608, 672, 448]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_535, vertices_307, vertices_675, vertices_341, vertices_901, vertices_425, vertices_282, vertices_538, vertices_618, vertices_298, vertices_604, vertices_740, vertices_452, vertices_472, vertices_232] (by decide +kernel)
  polygons := literalFinset [vertices_19, vertices_35, vertices_515, vertices_21, vertices_261, vertices_517, vertices_273, vertices_161, vertices_289, vertices_385, vertices_641, vertices_26, vertices_42, vertices_266, vertices_522, vertices_274, vertices_530, vertices_290, vertices_546, vertices_84, vertices_532, vertices_196, vertices_324, vertices_580, vertices_388, vertices_644, vertices_88, vertices_280, vertices_536, vertices_104, vertices_168, vertices_296, vertices_200, vertices_584, vertices_392, vertices_336, vertices_224, vertices_608, vertices_672, vertices_448] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_535), (false, vertices_307), (false, vertices_675), (false, vertices_341), (false, vertices_901), (false, vertices_425), (true, vertices_26), (true, vertices_42), (true, vertices_266), (true, vertices_522), (true, vertices_196), (true, vertices_580), (true, vertices_88), (true, vertices_280), (true, vertices_536), (true, vertices_104), (true, vertices_200), (true, vertices_584), (true, vertices_224), (true, vertices_608), (true, vertices_448)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 19 22 24 25 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_535) then 16 else
  if p.val = (false, vertices_307) then 17 else
  if p.val = (false, vertices_675) then 18 else
  if p.val = (false, vertices_341) then 20 else
  if p.val = (false, vertices_901) then 21 else
  if p.val = (false, vertices_425) then 23 else
  if p.val = (true, vertices_26) then 0 else
  if p.val = (true, vertices_42) then 1 else
  if p.val = (true, vertices_266) then 2 else
  if p.val = (true, vertices_522) then 3 else
  if p.val = (true, vertices_196) then 4 else
  if p.val = (true, vertices_580) then 5 else
  if p.val = (true, vertices_88) then 6 else
  if p.val = (true, vertices_280) then 7 else
  if p.val = (true, vertices_536) then 8 else
  if p.val = (true, vertices_104) then 9 else
  if p.val = (true, vertices_200) then 10 else
  if p.val = (true, vertices_584) then 11 else
  if p.val = (true, vertices_224) then 12 else
  if p.val = (true, vertices_608) then 13 else
  if p.val = (true, vertices_448) then 14 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_26), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_42), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_266), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_522), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_196), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_580), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_88), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_280), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_536), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_104), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_200), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_584), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_224), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_608), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_448), by decide +kernel⟩
  | 15 => Sum.inl 0
  | 16 => Sum.inr ⟨(false, vertices_535), by decide +kernel⟩
  | 17 => Sum.inr ⟨(false, vertices_307), by decide +kernel⟩
  | 18 => Sum.inr ⟨(false, vertices_675), by decide +kernel⟩
  | 19 => Sum.inl 1
  | 20 => Sum.inr ⟨(false, vertices_341), by decide +kernel⟩
  | 21 => Sum.inr ⟨(false, vertices_901), by decide +kernel⟩
  | 22 => Sum.inl 2
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
cert_row_4 0 0 2 4 5 8 618 42 3
cert_row_4 1 1 4 5 6 8 740 196 1
cert_row_4 2 1 2 3 5 8 604 84 1
cert_row_4 3 2 3 5 6 7 472 88 3
cert_rows
cert_pivot_2 0 4 1 2
cert_heightProof 4
cert_coverFacet 0 282
cert_cover_2 0 2 0 3 7 26 282 3
cert_coverFacet 1 538
cert_cover_2 1 2 0 3 8 26 538 3
cert_coverFacet 2 618
cert_cover_5 2 0 0 2 4 5 42 618 3
cert_coverFacet 3 298
cert_cover_2 3 2 0 4 7 42 298 3
cert_coverFacet 4 604
cert_cover_5 4 2 1 2 3 5 84 604 1
cert_coverFacet 5 740
cert_cover_5 5 1 1 4 5 6 196 740 1
cert_coverFacet 6 452
cert_cover_2 6 5 1 6 7 196 452 3
cert_coverFacet 7 472
cert_cover_5 7 3 2 3 5 6 88 472 3
cert_coverFacet 8 232
cert_cover_2 8 4 2 5 6 104 232 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q0_0038

end
end BundlePart25

section BundlePart26
/- Source: ProjectionCertificates/R_m15e10q0_0039.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q0_0039

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [271, 587, 675, 387, 93, 613, 421, 778, 914, 316, 116, 728, 792, 496, 736, 11, 131, 259, 515, 13, 37, 69, 261, 73, 161, 545, 577, 385, 266, 522, 386, 642, 770, 28, 268, 52, 84, 100, 292, 88, 280, 536, 584, 776, 112, 304, 208, 400, 656, 784, 224, 608, 416, 672, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_271, vertices_587, vertices_675, vertices_387, vertices_93, vertices_613, vertices_421, vertices_778, vertices_914, vertices_316, vertices_116, vertices_728, vertices_792, vertices_496, vertices_736] (by decide +kernel)
  polygons := literalFinset [vertices_11, vertices_131, vertices_259, vertices_515, vertices_13, vertices_37, vertices_69, vertices_261, vertices_73, vertices_161, vertices_545, vertices_577, vertices_385, vertices_266, vertices_522, vertices_386, vertices_642, vertices_770, vertices_28, vertices_268, vertices_52, vertices_84, vertices_100, vertices_292, vertices_88, vertices_280, vertices_536, vertices_584, vertices_776, vertices_112, vertices_304, vertices_208, vertices_400, vertices_656, vertices_784, vertices_224, vertices_608, vertices_416, vertices_672, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_271), (false, vertices_587), (false, vertices_675), (false, vertices_387), (false, vertices_93), (false, vertices_613), (false, vertices_421), (true, vertices_770), (true, vertices_52), (true, vertices_280), (true, vertices_536), (true, vertices_776), (true, vertices_112), (true, vertices_304), (true, vertices_208), (true, vertices_400), (true, vertices_656), (true, vertices_784), (true, vertices_224), (true, vertices_704)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 14 18 22 23 24 25 26 27 28
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_271) then 15 else
  if p.val = (false, vertices_587) then 16 else
  if p.val = (false, vertices_675) then 17 else
  if p.val = (false, vertices_387) then 0 else
  if p.val = (false, vertices_93) then 19 else
  if p.val = (false, vertices_613) then 20 else
  if p.val = (false, vertices_421) then 21 else
  if p.val = (true, vertices_770) then 1 else
  if p.val = (true, vertices_52) then 2 else
  if p.val = (true, vertices_280) then 3 else
  if p.val = (true, vertices_536) then 4 else
  if p.val = (true, vertices_776) then 5 else
  if p.val = (true, vertices_112) then 6 else
  if p.val = (true, vertices_304) then 7 else
  if p.val = (true, vertices_208) then 8 else
  if p.val = (true, vertices_400) then 9 else
  if p.val = (true, vertices_656) then 10 else
  if p.val = (true, vertices_784) then 11 else
  if p.val = (true, vertices_224) then 12 else
  if p.val = (true, vertices_704) then 13 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_387), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_770), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_52), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_280), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_536), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_776), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_112), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_304), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_208), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_400), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_656), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_784), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_224), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_704), by decide +kernel⟩
  | 14 => Sum.inl 0
  | 15 => Sum.inr ⟨(false, vertices_271), by decide +kernel⟩
  | 16 => Sum.inr ⟨(false, vertices_587), by decide +kernel⟩
  | 17 => Sum.inr ⟨(false, vertices_675), by decide +kernel⟩
  | 18 => Sum.inl 1
  | 19 => Sum.inr ⟨(false, vertices_93), by decide +kernel⟩
  | 20 => Sum.inr ⟨(false, vertices_613), by decide +kernel⟩
  | 21 => Sum.inr ⟨(false, vertices_421), by decide +kernel⟩
  | 22 => Sum.inl 2
  | 23 => Sum.inl 3
  | 24 => Sum.inl 4
  | 25 => Sum.inl 5
  | 26 => Sum.inl 6
  | 27 => Sum.inl 7
  | 28 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 3 6 7 8 914 386 1
cert_row_4 1 1 2 3 4 7 316 28 3
cert_row_4 2 2 3 5 6 8 728 88 3
cert_row_4 3 3 4 5 6 7 496 112 3
cert_rows
cert_pivot_2 0 1 2 3
cert_heightProof 4
cert_coverFacet 0 778
cert_cover_2 0 2 0 7 8 266 778 3
cert_coverFacet 1 914
cert_cover_5 1 0 0 3 6 7 386 914 1
cert_coverFacet 2 316
cert_cover_5 2 1 1 2 3 4 28 316 3
cert_coverFacet 3 116
cert_cover_2 3 3 1 4 5 52 116 3
cert_coverFacet 4 728
cert_cover_5 4 2 2 3 5 6 88 728 3
cert_coverFacet 5 792
cert_cover_2 5 3 2 7 8 280 792 3
cert_coverFacet 6 496
cert_cover_5 6 3 3 4 5 6 112 496 3
cert_coverFacet 7 736
cert_cover_2 7 5 4 6 8 224 736 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q0_0039

end
end BundlePart26

section BundlePart27
/- Source: ProjectionCertificates/R_m15e10q0_0042.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q0_0042

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [299, 659, 275, 227, 285, 109, 213, 790, 418, 898, 844, 596, 616, 936, 752, 19, 35, 131, 259, 13, 21, 69, 41, 265, 145, 273, 97, 193, 274, 530, 162, 290, 386, 642, 770, 76, 268, 84, 276, 532, 580, 772, 104, 296, 552, 584, 776, 208, 592, 656, 224, 608, 416, 672, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_299, vertices_659, vertices_275, vertices_227, vertices_285, vertices_109, vertices_213, vertices_790, vertices_418, vertices_898, vertices_844, vertices_596, vertices_616, vertices_936, vertices_752] (by decide +kernel)
  polygons := literalFinset [vertices_19, vertices_35, vertices_131, vertices_259, vertices_13, vertices_21, vertices_69, vertices_41, vertices_265, vertices_145, vertices_273, vertices_97, vertices_193, vertices_274, vertices_530, vertices_162, vertices_290, vertices_386, vertices_642, vertices_770, vertices_76, vertices_268, vertices_84, vertices_276, vertices_532, vertices_580, vertices_772, vertices_104, vertices_296, vertices_552, vertices_584, vertices_776, vertices_208, vertices_592, vertices_656, vertices_224, vertices_608, vertices_416, vertices_672, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_299), (false, vertices_659), (false, vertices_275), (false, vertices_227), (false, vertices_285), (false, vertices_109), (false, vertices_213), (true, vertices_386), (true, vertices_770), (true, vertices_532), (true, vertices_580), (true, vertices_772), (true, vertices_552), (true, vertices_584), (true, vertices_776), (true, vertices_592), (true, vertices_608), (true, vertices_416), (true, vertices_672), (true, vertices_896)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 14 18 22 23 24 25 26 27 28
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_299) then 15 else
  if p.val = (false, vertices_659) then 16 else
  if p.val = (false, vertices_275) then 0 else
  if p.val = (false, vertices_227) then 17 else
  if p.val = (false, vertices_285) then 19 else
  if p.val = (false, vertices_109) then 20 else
  if p.val = (false, vertices_213) then 21 else
  if p.val = (true, vertices_386) then 1 else
  if p.val = (true, vertices_770) then 2 else
  if p.val = (true, vertices_532) then 3 else
  if p.val = (true, vertices_580) then 4 else
  if p.val = (true, vertices_772) then 5 else
  if p.val = (true, vertices_552) then 6 else
  if p.val = (true, vertices_584) then 7 else
  if p.val = (true, vertices_776) then 8 else
  if p.val = (true, vertices_592) then 9 else
  if p.val = (true, vertices_608) then 10 else
  if p.val = (true, vertices_416) then 11 else
  if p.val = (true, vertices_672) then 12 else
  if p.val = (true, vertices_896) then 13 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_275), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_386), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_770), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_532), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_580), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_772), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_552), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_584), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_776), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_592), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_608), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_416), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_672), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_896), by decide +kernel⟩
  | 14 => Sum.inl 0
  | 15 => Sum.inr ⟨(false, vertices_299), by decide +kernel⟩
  | 16 => Sum.inr ⟨(false, vertices_659), by decide +kernel⟩
  | 17 => Sum.inr ⟨(false, vertices_227), by decide +kernel⟩
  | 18 => Sum.inl 1
  | 19 => Sum.inr ⟨(false, vertices_285), by decide +kernel⟩
  | 20 => Sum.inr ⟨(false, vertices_109), by decide +kernel⟩
  | 21 => Sum.inr ⟨(false, vertices_213), by decide +kernel⟩
  | 22 => Sum.inl 2
  | 23 => Sum.inl 3
  | 24 => Sum.inl 4
  | 25 => Sum.inl 5
  | 26 => Sum.inl 6
  | 27 => Sum.inl 7
  | 28 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 3 7 8 790 274 1
cert_row_4 1 1 2 5 7 8 844 76 3
cert_row_4 2 2 4 6 7 8 936 296 2
cert_row_4 3 3 4 5 6 8 752 208 1
cert_rows
cert_pivot_2 0 1 2 3
cert_heightProof 4
cert_coverFacet 0 790
cert_cover_5 0 0 0 1 3 7 274 790 1
cert_coverFacet 1 418
cert_cover_2 1 4 0 6 7 162 418 3
cert_coverFacet 2 898
cert_cover_2 2 6 0 7 8 386 898 3
cert_coverFacet 3 844
cert_cover_5 3 1 1 2 5 7 76 844 3
cert_coverFacet 4 596
cert_cover_2 4 3 1 5 8 84 596 3
cert_coverFacet 5 616
cert_cover_2 5 4 2 5 8 104 616 3
cert_coverFacet 6 936
cert_cover_5 6 2 2 4 6 7 296 936 2
cert_coverFacet 7 752
cert_cover_5 7 3 3 4 5 6 208 752 1
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q0_0042

end
end BundlePart27

section BundlePart28
/- Source: ProjectionCertificates/R_m15e10q0_0043.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q0_0043

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [535, 107, 651, 307, 205, 277, 357, 645, 570, 468, 660, 616, 968, 944, 864, 11, 19, 35, 515, 21, 69, 133, 261, 517, 73, 137, 273, 97, 289, 641, 42, 522, 50, 530, 148, 276, 532, 196, 324, 644, 104, 552, 200, 584, 648, 304, 560, 400, 656, 352, 608, 800, 448, 832, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_535, vertices_107, vertices_651, vertices_307, vertices_205, vertices_277, vertices_357, vertices_645, vertices_570, vertices_468, vertices_660, vertices_616, vertices_968, vertices_944, vertices_864] (by decide +kernel)
  polygons := literalFinset [vertices_11, vertices_19, vertices_35, vertices_515, vertices_21, vertices_69, vertices_133, vertices_261, vertices_517, vertices_73, vertices_137, vertices_273, vertices_97, vertices_289, vertices_641, vertices_42, vertices_522, vertices_50, vertices_530, vertices_148, vertices_276, vertices_532, vertices_196, vertices_324, vertices_644, vertices_104, vertices_552, vertices_200, vertices_584, vertices_648, vertices_304, vertices_560, vertices_400, vertices_656, vertices_352, vertices_608, vertices_800, vertices_448, vertices_832, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_535), (false, vertices_107), (false, vertices_651), (false, vertices_307), (false, vertices_205), (false, vertices_277), (false, vertices_357), (false, vertices_645), (true, vertices_148), (true, vertices_552), (true, vertices_584), (true, vertices_560), (true, vertices_400), (true, vertices_656), (true, vertices_608), (true, vertices_800), (true, vertices_448), (true, vertices_832), (true, vertices_896)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 17 13 21 22 23 24 25 26 27
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_535) then 14 else
  if p.val = (false, vertices_107) then 18 else
  if p.val = (false, vertices_651) then 19 else
  if p.val = (false, vertices_307) then 20 else
  if p.val = (false, vertices_205) then 15 else
  if p.val = (false, vertices_277) then 0 else
  if p.val = (false, vertices_357) then 16 else
  if p.val = (false, vertices_645) then 1 else
  if p.val = (true, vertices_148) then 2 else
  if p.val = (true, vertices_552) then 3 else
  if p.val = (true, vertices_584) then 4 else
  if p.val = (true, vertices_560) then 5 else
  if p.val = (true, vertices_400) then 6 else
  if p.val = (true, vertices_656) then 7 else
  if p.val = (true, vertices_608) then 8 else
  if p.val = (true, vertices_800) then 9 else
  if p.val = (true, vertices_448) then 10 else
  if p.val = (true, vertices_832) then 11 else
  if p.val = (true, vertices_896) then 12 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_277), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_645), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_148), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_552), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_584), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_560), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_400), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_656), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_608), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_800), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_448), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_832), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_896), by decide +kernel⟩
  | 13 => Sum.inl 1
  | 14 => Sum.inr ⟨(false, vertices_535), by decide +kernel⟩
  | 15 => Sum.inr ⟨(false, vertices_205), by decide +kernel⟩
  | 16 => Sum.inr ⟨(false, vertices_357), by decide +kernel⟩
  | 17 => Sum.inl 0
  | 18 => Sum.inr ⟨(false, vertices_107), by decide +kernel⟩
  | 19 => Sum.inr ⟨(false, vertices_651), by decide +kernel⟩
  | 20 => Sum.inr ⟨(false, vertices_307), by decide +kernel⟩
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
cert_row_4 0 0 2 3 4 8 570 42 2
cert_row_4 1 1 3 5 6 7 468 148 2
cert_row_4 2 2 5 6 7 8 968 200 3
cert_row_4 3 3 4 6 7 8 944 304 2
cert_rows
cert_pivot_2 0 1 2 3
cert_heightProof 4
cert_coverFacet 0 570
cert_cover_5 0 0 0 2 3 4 42 570 2
cert_coverFacet 1 468
cert_cover_5 1 1 1 3 5 6 148 468 2
cert_coverFacet 2 660
cert_cover_2 2 3 1 6 8 148 660 3
cert_coverFacet 3 616
cert_cover_2 3 4 2 5 8 104 616 3
cert_coverFacet 4 968
cert_cover_5 4 2 2 5 6 7 200 968 3
cert_coverFacet 5 944
cert_cover_5 5 3 3 4 6 7 304 944 2
cert_coverFacet 6 864
cert_cover_2 6 5 4 7 8 352 864 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q0_0043

end
end BundlePart28

section BundlePart29
/- Source: ProjectionCertificates/R_m15e10q0_0044.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q0_0044

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [587, 227, 803, 781, 457, 433, 678, 722, 316, 604, 180, 660, 804, 344, 464, 35, 67, 515, 73, 265, 521, 161, 289, 193, 385, 769, 162, 546, 194, 578, 642, 28, 268, 524, 52, 148, 532, 164, 292, 548, 644, 772, 88, 280, 328, 584, 176, 304, 208, 336, 592, 400, 656, 800, 448]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_587, vertices_227, vertices_803, vertices_781, vertices_457, vertices_433, vertices_678, vertices_722, vertices_316, vertices_604, vertices_180, vertices_660, vertices_804, vertices_344, vertices_464] (by decide +kernel)
  polygons := literalFinset [vertices_35, vertices_67, vertices_515, vertices_73, vertices_265, vertices_521, vertices_161, vertices_289, vertices_193, vertices_385, vertices_769, vertices_162, vertices_546, vertices_194, vertices_578, vertices_642, vertices_28, vertices_268, vertices_524, vertices_52, vertices_148, vertices_532, vertices_164, vertices_292, vertices_548, vertices_644, vertices_772, vertices_88, vertices_280, vertices_328, vertices_584, vertices_176, vertices_304, vertices_208, vertices_336, vertices_592, vertices_400, vertices_656, vertices_800, vertices_448] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_587), (false, vertices_227), (false, vertices_803), (false, vertices_781), (false, vertices_457), (false, vertices_433), (true, vertices_642), (true, vertices_28), (true, vertices_52), (true, vertices_148), (true, vertices_532), (true, vertices_164), (true, vertices_292), (true, vertices_548), (true, vertices_644), (true, vertices_88), (true, vertices_280), (true, vertices_208), (true, vertices_336), (true, vertices_592), (true, vertices_656)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 19 21 23 25 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_587) then 16 else
  if p.val = (false, vertices_227) then 17 else
  if p.val = (false, vertices_803) then 18 else
  if p.val = (false, vertices_781) then 20 else
  if p.val = (false, vertices_457) then 22 else
  if p.val = (false, vertices_433) then 24 else
  if p.val = (true, vertices_642) then 0 else
  if p.val = (true, vertices_28) then 1 else
  if p.val = (true, vertices_52) then 2 else
  if p.val = (true, vertices_148) then 3 else
  if p.val = (true, vertices_532) then 4 else
  if p.val = (true, vertices_164) then 5 else
  if p.val = (true, vertices_292) then 6 else
  if p.val = (true, vertices_548) then 7 else
  if p.val = (true, vertices_644) then 8 else
  if p.val = (true, vertices_88) then 9 else
  if p.val = (true, vertices_280) then 10 else
  if p.val = (true, vertices_208) then 11 else
  if p.val = (true, vertices_336) then 12 else
  if p.val = (true, vertices_592) then 13 else
  if p.val = (true, vertices_656) then 14 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_642), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_28), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_52), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_148), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_532), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_164), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_292), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_548), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_644), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_88), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_280), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_208), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_336), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_592), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_656), by decide +kernel⟩
  | 15 => Sum.inl 0
  | 16 => Sum.inr ⟨(false, vertices_587), by decide +kernel⟩
  | 17 => Sum.inr ⟨(false, vertices_227), by decide +kernel⟩
  | 18 => Sum.inr ⟨(false, vertices_803), by decide +kernel⟩
  | 19 => Sum.inl 1
  | 20 => Sum.inr ⟨(false, vertices_781), by decide +kernel⟩
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
cert_row_4 0 1 2 3 4 7 316 28 3
cert_row_4 1 0 1 4 6 8 678 162 1
cert_row_4 2 0 3 5 6 8 722 194 1
cert_row_4 3 1 2 3 5 8 604 28 3
cert_rows
cert_pivot_2 7 4 0 1
cert_heightProof 4
cert_coverFacet 0 678
cert_cover_5 0 1 0 1 4 6 162 678 1
cert_coverFacet 1 722
cert_cover_5 1 2 0 3 5 6 194 722 1
cert_coverFacet 2 316
cert_cover_5 2 0 1 2 3 4 28 316 3
cert_coverFacet 3 604
cert_cover_5 3 3 1 2 3 5 28 604 3
cert_coverFacet 4 180
cert_cover_2 4 3 1 4 6 52 180 3
cert_coverFacet 5 660
cert_cover_2 5 3 1 6 8 148 660 3
cert_coverFacet 6 804
cert_cover_2 6 4 1 7 8 292 804 3
cert_coverFacet 7 344
cert_cover_2 7 3 2 5 7 88 344 3
cert_coverFacet 8 464
cert_cover_2 8 5 3 6 7 208 464 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q0_0044

end
end BundlePart29

-- Public target certificates; internal witness data stays private.
namespace Nonrational.TerminalVerification
open Papers.RationalityTen.ChirotopeDensity.FiniteProjection
open Nonrational.TerminalData
set_option maxRecDepth 100000
set_option maxHeartbeats 0

public theorem projection_2583 : Certifies 2583 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q0_0003.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2584 : Certifies 2584 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q0_0004.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2585 : Certifies 2585 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q0_0005.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2586 : Certifies 2586 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q0_0006.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2587 : Certifies 2587 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q0_0008.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2588 : Certifies 2588 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q0_0009.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2589 : Certifies 2589 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q0_0011.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2590 : Certifies 2590 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q0_0013.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2591 : Certifies 2591 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q0_0015.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2592 : Certifies 2592 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q0_0016.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2593 : Certifies 2593 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q0_0017.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2594 : Certifies 2594 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q0_0018.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2595 : Certifies 2595 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q0_0019.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2596 : Certifies 2596 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q0_0020.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2597 : Certifies 2597 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q0_0022.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2598 : Certifies 2598 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q0_0024.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2599 : Certifies 2599 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q0_0025.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2600 : Certifies 2600 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q0_0027.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2601 : Certifies 2601 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q0_0029.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2602 : Certifies 2602 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q0_0030.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2603 : Certifies 2603 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q0_0031.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2604 : Certifies 2604 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q0_0033.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2605 : Certifies 2605 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q0_0034.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2606 : Certifies 2606 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q0_0035.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2607 : Certifies 2607 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q0_0036.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2608 : Certifies 2608 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q0_0038.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2609 : Certifies 2609 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q0_0039.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2610 : Certifies 2610 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q0_0042.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2611 : Certifies 2611 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q0_0043.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2612 : Certifies 2612 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q0_0044.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem certified_B085 (j : Fin 30) :
    Certifies (2583 + j.val) := by
  fin_cases j
  · exact projection_2583
  · exact projection_2584
  · exact projection_2585
  · exact projection_2586
  · exact projection_2587
  · exact projection_2588
  · exact projection_2589
  · exact projection_2590
  · exact projection_2591
  · exact projection_2592
  · exact projection_2593
  · exact projection_2594
  · exact projection_2595
  · exact projection_2596
  · exact projection_2597
  · exact projection_2598
  · exact projection_2599
  · exact projection_2600
  · exact projection_2601
  · exact projection_2602
  · exact projection_2603
  · exact projection_2604
  · exact projection_2605
  · exact projection_2606
  · exact projection_2607
  · exact projection_2608
  · exact projection_2609
  · exact projection_2610
  · exact projection_2611
  · exact projection_2612

end Nonrational.TerminalVerification
-- Explicit facial frame witnesses, with lexical vector tracking.
