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
/- Source: ProjectionCertificates/R_m16e10q1_0375.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0375

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [647, 263, 395, 333, 117, 565, 713, 609, 342, 534, 690, 402, 376, 616, 936, 432, 7, 131, 259, 53, 69, 261, 517, 73, 137, 265, 97, 545, 577, 641, 22, 262, 518, 146, 274, 530, 386, 642, 84, 532, 324, 104, 296, 552, 328, 584, 392, 648, 112, 176, 304, 560, 336, 400, 608, 416, 672]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_647, vertices_263, vertices_395, vertices_333, vertices_117, vertices_565, vertices_713, vertices_609, vertices_342, vertices_534, vertices_690, vertices_402, vertices_376, vertices_616, vertices_936, vertices_432] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_131, vertices_259, vertices_53, vertices_69, vertices_261, vertices_517, vertices_73, vertices_137, vertices_265, vertices_97, vertices_545, vertices_577, vertices_641, vertices_22, vertices_262, vertices_518, vertices_146, vertices_274, vertices_530, vertices_386, vertices_642, vertices_84, vertices_532, vertices_324, vertices_104, vertices_296, vertices_552, vertices_328, vertices_584, vertices_392, vertices_648, vertices_112, vertices_176, vertices_304, vertices_560, vertices_336, vertices_400, vertices_608, vertices_416, vertices_672] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_647), (false, vertices_263), (false, vertices_395), (false, vertices_333), (false, vertices_117), (false, vertices_565), (false, vertices_713), (false, vertices_609), (true, vertices_22), (true, vertices_146), (true, vertices_274), (true, vertices_530), (true, vertices_104), (true, vertices_296), (true, vertices_552), (true, vertices_176), (true, vertices_304), (true, vertices_336), (true, vertices_400), (true, vertices_416), (true, vertices_672)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 18 22 24 25 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_647) then 16 else
  if p.val = (false, vertices_263) then 0 else
  if p.val = (false, vertices_395) then 17 else
  if p.val = (false, vertices_333) then 19 else
  if p.val = (false, vertices_117) then 20 else
  if p.val = (false, vertices_565) then 21 else
  if p.val = (false, vertices_713) then 23 else
  if p.val = (false, vertices_609) then 1 else
  if p.val = (true, vertices_22) then 2 else
  if p.val = (true, vertices_146) then 3 else
  if p.val = (true, vertices_274) then 4 else
  if p.val = (true, vertices_530) then 5 else
  if p.val = (true, vertices_104) then 6 else
  if p.val = (true, vertices_296) then 7 else
  if p.val = (true, vertices_552) then 8 else
  if p.val = (true, vertices_176) then 9 else
  if p.val = (true, vertices_304) then 10 else
  if p.val = (true, vertices_336) then 11 else
  if p.val = (true, vertices_400) then 12 else
  if p.val = (true, vertices_416) then 13 else
  if p.val = (true, vertices_672) then 14 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_263), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_609), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_22), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_146), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_274), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_530), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_104), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_296), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_552), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_176), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_304), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_336), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_400), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_416), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_672), by decide +kernel⟩
  | 15 => Sum.inl 0
  | 16 => Sum.inr ⟨(false, vertices_647), by decide +kernel⟩
  | 17 => Sum.inr ⟨(false, vertices_395), by decide +kernel⟩
  | 18 => Sum.inl 1
  | 19 => Sum.inr ⟨(false, vertices_333), by decide +kernel⟩
  | 20 => Sum.inr ⟨(false, vertices_117), by decide +kernel⟩
  | 21 => Sum.inr ⟨(false, vertices_565), by decide +kernel⟩
  | 22 => Sum.inl 2
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
cert_row_4 0 0 1 3 5 7 342 22 3
cert_row_4 1 0 3 4 6 8 690 146 2
cert_row_4 2 2 3 4 5 7 376 104 1
cert_row_4 3 2 4 6 7 8 936 296 2
cert_rows
cert_pivot_2 1 0 3 2
cert_heightProof 4
cert_coverFacet 0 342
cert_cover_5 0 0 0 1 3 5 22 342 3
cert_coverFacet 1 534
cert_cover_2 1 1 0 3 8 22 534 3
cert_coverFacet 2 690
cert_cover_5 2 1 0 3 4 6 146 690 2
cert_coverFacet 3 402
cert_cover_2 3 3 0 6 7 146 402 3
cert_coverFacet 4 376
cert_cover_5 4 2 2 3 4 5 104 376 1
cert_coverFacet 5 616
cert_cover_2 5 4 2 5 8 104 616 3
cert_coverFacet 6 936
cert_cover_5 6 3 2 4 6 7 296 936 2
cert_coverFacet 7 432
cert_cover_2 7 4 3 6 7 176 432 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0375

end
end BundlePart0

section BundlePart1
/- Source: ProjectionCertificates/R_m16e10q1_0376.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0376

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [595, 275, 803, 309, 185, 217, 617, 902, 714, 338, 450, 172, 812, 652, 180, 468, 19, 259, 515, 153, 41, 73, 49, 81, 273, 289, 545, 577, 82, 274, 194, 322, 578, 386, 642, 770, 44, 140, 524, 52, 148, 276, 164, 292, 388, 644, 772, 168, 552, 200, 584, 648, 176, 208, 336, 800, 448]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_595, vertices_275, vertices_803, vertices_309, vertices_185, vertices_217, vertices_617, vertices_902, vertices_714, vertices_338, vertices_450, vertices_172, vertices_812, vertices_652, vertices_180, vertices_468] (by decide +kernel)
  polygons := literalFinset [vertices_19, vertices_259, vertices_515, vertices_153, vertices_41, vertices_73, vertices_49, vertices_81, vertices_273, vertices_289, vertices_545, vertices_577, vertices_82, vertices_274, vertices_194, vertices_322, vertices_578, vertices_386, vertices_642, vertices_770, vertices_44, vertices_140, vertices_524, vertices_52, vertices_148, vertices_276, vertices_164, vertices_292, vertices_388, vertices_644, vertices_772, vertices_168, vertices_552, vertices_200, vertices_584, vertices_648, vertices_176, vertices_208, vertices_336, vertices_800, vertices_448] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_595), (false, vertices_275), (false, vertices_803), (false, vertices_309), (false, vertices_185), (false, vertices_217), (false, vertices_617), (true, vertices_194), (true, vertices_322), (true, vertices_386), (true, vertices_642), (true, vertices_44), (true, vertices_140), (true, vertices_524), (true, vertices_148), (true, vertices_164), (true, vertices_388), (true, vertices_644), (true, vertices_772), (true, vertices_648), (true, vertices_336), (true, vertices_448)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 16 19 21 25 26 27 28 29 30
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_595) then 17 else
  if p.val = (false, vertices_275) then 0 else
  if p.val = (false, vertices_803) then 18 else
  if p.val = (false, vertices_309) then 20 else
  if p.val = (false, vertices_185) then 22 else
  if p.val = (false, vertices_217) then 23 else
  if p.val = (false, vertices_617) then 24 else
  if p.val = (true, vertices_194) then 1 else
  if p.val = (true, vertices_322) then 2 else
  if p.val = (true, vertices_386) then 3 else
  if p.val = (true, vertices_642) then 4 else
  if p.val = (true, vertices_44) then 5 else
  if p.val = (true, vertices_140) then 6 else
  if p.val = (true, vertices_524) then 7 else
  if p.val = (true, vertices_148) then 8 else
  if p.val = (true, vertices_164) then 9 else
  if p.val = (true, vertices_388) then 10 else
  if p.val = (true, vertices_644) then 11 else
  if p.val = (true, vertices_772) then 12 else
  if p.val = (true, vertices_648) then 13 else
  if p.val = (true, vertices_336) then 14 else
  if p.val = (true, vertices_448) then 15 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_275), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_194), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_322), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_386), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_642), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_44), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_140), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_524), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_148), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_164), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_388), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_644), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_772), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_648), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_336), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_448), by decide +kernel⟩
  | 16 => Sum.inl 0
  | 17 => Sum.inr ⟨(false, vertices_595), by decide +kernel⟩
  | 18 => Sum.inr ⟨(false, vertices_803), by decide +kernel⟩
  | 19 => Sum.inl 1
  | 20 => Sum.inr ⟨(false, vertices_309), by decide +kernel⟩
  | 21 => Sum.inl 2
  | 22 => Sum.inr ⟨(false, vertices_185), by decide +kernel⟩
  | 23 => Sum.inr ⟨(false, vertices_217), by decide +kernel⟩
  | 24 => Sum.inr ⟨(false, vertices_617), by decide +kernel⟩
  | 25 => Sum.inl 3
  | 26 => Sum.inl 4
  | 27 => Sum.inl 5
  | 28 => Sum.inl 6
  | 29 => Sum.inl 7
  | 30 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 1 2 4 7 8 812 44 3
cert_row_4 1 0 2 5 6 8 714 194 1
cert_row_4 2 0 1 6 7 8 902 386 1
cert_row_4 3 1 3 5 6 7 468 148 2
cert_rows
cert_pivot_2 4 2 0 1
cert_heightProof 4
cert_coverFacet 0 902
cert_cover_5 0 2 0 1 6 7 386 902 1
cert_coverFacet 1 714
cert_cover_5 1 1 0 2 5 6 194 714 1
cert_coverFacet 2 338
cert_cover_2 2 3 0 5 7 82 338 3
cert_coverFacet 3 450
cert_cover_2 3 5 0 6 7 194 450 3
cert_coverFacet 4 172
cert_cover_2 4 2 1 4 6 44 172 3
cert_coverFacet 5 812
cert_cover_5 5 0 1 2 4 7 44 812 3
cert_coverFacet 6 652
cert_cover_2 6 2 1 6 8 140 652 3
cert_coverFacet 7 180
cert_cover_2 7 3 1 4 6 52 180 3
cert_coverFacet 8 468
cert_cover_5 8 3 1 3 5 6 148 468 2
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0376

end
end BundlePart1

section BundlePart2
/- Source: ProjectionCertificates/R_m16e10q1_0377.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0377

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [775, 99, 419, 579, 397, 677, 625, 458, 850, 226, 348, 540, 652, 788, 248, 696, 35, 67, 259, 515, 133, 261, 517, 97, 161, 545, 577, 385, 98, 162, 194, 322, 578, 386, 770, 28, 140, 268, 524, 276, 532, 644, 772, 184, 88, 536, 200, 328, 392, 648, 112, 560, 336, 592, 784, 224, 672]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_775, vertices_99, vertices_419, vertices_579, vertices_397, vertices_677, vertices_625, vertices_458, vertices_850, vertices_226, vertices_348, vertices_540, vertices_652, vertices_788, vertices_248, vertices_696] (by decide +kernel)
  polygons := literalFinset [vertices_35, vertices_67, vertices_259, vertices_515, vertices_133, vertices_261, vertices_517, vertices_97, vertices_161, vertices_545, vertices_577, vertices_385, vertices_98, vertices_162, vertices_194, vertices_322, vertices_578, vertices_386, vertices_770, vertices_28, vertices_140, vertices_268, vertices_524, vertices_276, vertices_532, vertices_644, vertices_772, vertices_184, vertices_88, vertices_536, vertices_200, vertices_328, vertices_392, vertices_648, vertices_112, vertices_560, vertices_336, vertices_592, vertices_784, vertices_224, vertices_672] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_775), (false, vertices_99), (false, vertices_419), (false, vertices_579), (false, vertices_397), (false, vertices_677), (false, vertices_625), (true, vertices_194), (true, vertices_322), (true, vertices_28), (true, vertices_524), (true, vertices_276), (true, vertices_532), (true, vertices_184), (true, vertices_88), (true, vertices_536), (true, vertices_200), (true, vertices_328), (true, vertices_648), (true, vertices_336), (true, vertices_784), (true, vertices_224)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 16 19 22 24 26 27 28 29 30
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_775) then 17 else
  if p.val = (false, vertices_99) then 0 else
  if p.val = (false, vertices_419) then 18 else
  if p.val = (false, vertices_579) then 1 else
  if p.val = (false, vertices_397) then 20 else
  if p.val = (false, vertices_677) then 21 else
  if p.val = (false, vertices_625) then 25 else
  if p.val = (true, vertices_194) then 2 else
  if p.val = (true, vertices_322) then 3 else
  if p.val = (true, vertices_28) then 4 else
  if p.val = (true, vertices_524) then 5 else
  if p.val = (true, vertices_276) then 6 else
  if p.val = (true, vertices_532) then 7 else
  if p.val = (true, vertices_184) then 23 else
  if p.val = (true, vertices_88) then 8 else
  if p.val = (true, vertices_536) then 9 else
  if p.val = (true, vertices_200) then 10 else
  if p.val = (true, vertices_328) then 11 else
  if p.val = (true, vertices_648) then 12 else
  if p.val = (true, vertices_336) then 13 else
  if p.val = (true, vertices_784) then 14 else
  if p.val = (true, vertices_224) then 15 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_99), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_579), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_194), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_322), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_28), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_524), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_276), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_532), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_88), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_536), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_200), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_328), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_648), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_336), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_784), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_224), by decide +kernel⟩
  | 16 => Sum.inl 0
  | 17 => Sum.inr ⟨(false, vertices_775), by decide +kernel⟩
  | 18 => Sum.inr ⟨(false, vertices_419), by decide +kernel⟩
  | 19 => Sum.inl 1
  | 20 => Sum.inr ⟨(false, vertices_397), by decide +kernel⟩
  | 21 => Sum.inr ⟨(false, vertices_677), by decide +kernel⟩
  | 22 => Sum.inl 2
  | 23 => Sum.inr ⟨(true, vertices_184), by decide +kernel⟩
  | 24 => Sum.inl 3
  | 25 => Sum.inr ⟨(false, vertices_625), by decide +kernel⟩
  | 26 => Sum.inl 4
  | 27 => Sum.inl 5
  | 28 => Sum.inl 6
  | 29 => Sum.inl 7
  | 30 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 2 3 4 6 184
cert_row_4 1 0 2 5 6 7 458 194 1
cert_row_4 2 0 3 5 7 8 850 322 1
cert_row_4 3 1 2 3 5 7 348 28 3
cert_rows
cert_pivot_2 4 6 0 1
cert_heightProof 4
cert_coverFacet 0 458
cert_cover_5 0 1 0 2 5 6 194 458 1
cert_coverFacet 1 850
cert_cover_5 1 2 0 3 5 7 322 850 1
cert_coverFacet 2 226
cert_cover_2 2 4 0 5 6 98 226 3
cert_coverFacet 3 348
cert_cover_5 3 3 1 2 3 5 28 348 3
cert_coverFacet 4 540
cert_cover_2 4 2 1 3 8 28 540 3
cert_coverFacet 5 652
cert_cover_2 5 2 1 6 8 140 652 3
cert_coverFacet 6 788
cert_cover_2 6 3 1 7 8 276 788 3
cert_coverFacet 7 248
cert_cover_5 7 0 2 3 4 5 184 248 3
cert_coverFacet 8 696
cert_cover_5 8 0 2 3 4 8 184 696 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0377

end
end BundlePart2

section BundlePart3
/- Source: ProjectionCertificates/R_m16e10q1_0379.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0379

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [587, 789, 421, 709, 89, 537, 465, 302, 678, 774, 794, 106, 738, 248, 312, 432, 133, 261, 517, 25, 73, 521, 81, 273, 529, 193, 577, 385, 38, 262, 518, 42, 74, 266, 522, 98, 674, 578, 770, 164, 292, 644, 772, 56, 88, 280, 536, 104, 296, 176, 304, 208, 400, 784, 224, 416, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_587, vertices_789, vertices_421, vertices_709, vertices_89, vertices_537, vertices_465, vertices_302, vertices_678, vertices_774, vertices_794, vertices_106, vertices_738, vertices_248, vertices_312, vertices_432] (by decide +kernel)
  polygons := literalFinset [vertices_133, vertices_261, vertices_517, vertices_25, vertices_73, vertices_521, vertices_81, vertices_273, vertices_529, vertices_193, vertices_577, vertices_385, vertices_38, vertices_262, vertices_518, vertices_42, vertices_74, vertices_266, vertices_522, vertices_98, vertices_674, vertices_578, vertices_770, vertices_164, vertices_292, vertices_644, vertices_772, vertices_56, vertices_88, vertices_280, vertices_536, vertices_104, vertices_296, vertices_176, vertices_304, vertices_208, vertices_400, vertices_784, vertices_224, vertices_416, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_587), (false, vertices_789), (false, vertices_421), (false, vertices_709), (false, vertices_89), (false, vertices_537), (false, vertices_465), (true, vertices_38), (true, vertices_262), (true, vertices_518), (true, vertices_42), (true, vertices_266), (true, vertices_98), (true, vertices_674), (true, vertices_770), (true, vertices_56), (true, vertices_280), (true, vertices_104), (true, vertices_296), (true, vertices_176), (true, vertices_304), (true, vertices_224)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 16 19 23 24 26 27 28 29 30
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_587) then 17 else
  if p.val = (false, vertices_789) then 20 else
  if p.val = (false, vertices_421) then 21 else
  if p.val = (false, vertices_709) then 22 else
  if p.val = (false, vertices_89) then 0 else
  if p.val = (false, vertices_537) then 1 else
  if p.val = (false, vertices_465) then 25 else
  if p.val = (true, vertices_38) then 2 else
  if p.val = (true, vertices_262) then 3 else
  if p.val = (true, vertices_518) then 4 else
  if p.val = (true, vertices_42) then 5 else
  if p.val = (true, vertices_266) then 6 else
  if p.val = (true, vertices_98) then 7 else
  if p.val = (true, vertices_674) then 18 else
  if p.val = (true, vertices_770) then 8 else
  if p.val = (true, vertices_56) then 9 else
  if p.val = (true, vertices_280) then 10 else
  if p.val = (true, vertices_104) then 11 else
  if p.val = (true, vertices_296) then 12 else
  if p.val = (true, vertices_176) then 13 else
  if p.val = (true, vertices_304) then 14 else
  if p.val = (true, vertices_224) then 15 else
  0
cert_priority
cert_nodeAtPriority_21 0 89 1 537 38 262 518 42 266 98 770 56 280 104 296 176 304 224 587 674 789 421 709 465
cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 2 4 7 302 38 2
cert_row_4 1 0 2 3 7 8 794 266 2
cert_row_2 2 0 4 6 8 674
cert_row_4 3 2 3 4 5 6 248 56 3
cert_rows
cert_pivot_2 1 7 0 2
cert_heightProof 4
cert_coverFacet 0 302
cert_cover_5 0 0 0 1 2 4 38 302 2
cert_coverFacet 1 678
cert_cover_5 1 2 0 1 4 6 38 678 3
cert_coverFacet 2 774
cert_cover_2 2 1 0 7 8 262 774 3
cert_coverFacet 3 794
cert_cover_5 3 1 0 2 3 7 266 794 2
cert_coverFacet 4 106
cert_cover_2 4 2 0 4 5 42 106 3
cert_coverFacet 5 738
cert_cover_5 5 2 0 4 5 6 98 738 3
cert_coverFacet 6 248
cert_cover_5 6 3 2 3 4 5 56 248 3
cert_coverFacet 7 312
cert_cover_2 7 3 2 4 7 56 312 3
cert_coverFacet 8 432
cert_cover_2 8 4 3 6 7 176 432 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0379

end
end BundlePart3

section BundlePart4
/- Source: ProjectionCertificates/R_m16e10q1_0380.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0380

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [403, 675, 835, 613, 361, 417, 662, 794, 92, 540, 844, 244, 676, 248, 408, 424, 131, 259, 515, 97, 161, 289, 545, 321, 577, 385, 146, 274, 530, 642, 770, 28, 76, 524, 84, 148, 532, 100, 164, 548, 580, 644, 88, 152, 280, 536, 104, 168, 296, 328, 392, 776, 240, 400, 416, 672, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_403, vertices_675, vertices_835, vertices_613, vertices_361, vertices_417, vertices_662, vertices_794, vertices_92, vertices_540, vertices_844, vertices_244, vertices_676, vertices_248, vertices_408, vertices_424] (by decide +kernel)
  polygons := literalFinset [vertices_131, vertices_259, vertices_515, vertices_97, vertices_161, vertices_289, vertices_545, vertices_321, vertices_577, vertices_385, vertices_146, vertices_274, vertices_530, vertices_642, vertices_770, vertices_28, vertices_76, vertices_524, vertices_84, vertices_148, vertices_532, vertices_100, vertices_164, vertices_548, vertices_580, vertices_644, vertices_88, vertices_152, vertices_280, vertices_536, vertices_104, vertices_168, vertices_296, vertices_328, vertices_392, vertices_776, vertices_240, vertices_400, vertices_416, vertices_672, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_403), (false, vertices_675), (false, vertices_835), (false, vertices_613), (false, vertices_361), (false, vertices_417), (true, vertices_530), (true, vertices_28), (true, vertices_76), (true, vertices_524), (true, vertices_84), (true, vertices_148), (true, vertices_532), (true, vertices_164), (true, vertices_644), (true, vertices_88), (true, vertices_152), (true, vertices_280), (true, vertices_536), (true, vertices_168), (true, vertices_392), (true, vertices_776), (true, vertices_240)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 17 21 23 25 27 28 29 30 31
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_403) then 18 else
  if p.val = (false, vertices_675) then 19 else
  if p.val = (false, vertices_835) then 20 else
  if p.val = (false, vertices_613) then 22 else
  if p.val = (false, vertices_361) then 24 else
  if p.val = (false, vertices_417) then 0 else
  if p.val = (true, vertices_530) then 1 else
  if p.val = (true, vertices_28) then 2 else
  if p.val = (true, vertices_76) then 3 else
  if p.val = (true, vertices_524) then 4 else
  if p.val = (true, vertices_84) then 5 else
  if p.val = (true, vertices_148) then 6 else
  if p.val = (true, vertices_532) then 7 else
  if p.val = (true, vertices_164) then 8 else
  if p.val = (true, vertices_644) then 9 else
  if p.val = (true, vertices_88) then 10 else
  if p.val = (true, vertices_152) then 11 else
  if p.val = (true, vertices_280) then 12 else
  if p.val = (true, vertices_536) then 13 else
  if p.val = (true, vertices_168) then 14 else
  if p.val = (true, vertices_392) then 15 else
  if p.val = (true, vertices_776) then 16 else
  if p.val = (true, vertices_240) then 26 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_417), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_530), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_28), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_76), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_524), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_84), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_148), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_532), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_164), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_644), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_88), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_152), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_280), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_536), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_168), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_392), by decide +kernel⟩
  | 16 => Sum.inr ⟨(true, vertices_776), by decide +kernel⟩
  | 17 => Sum.inl 0
  | 18 => Sum.inr ⟨(false, vertices_403), by decide +kernel⟩
  | 19 => Sum.inr ⟨(false, vertices_675), by decide +kernel⟩
  | 20 => Sum.inr ⟨(false, vertices_835), by decide +kernel⟩
  | 21 => Sum.inl 1
  | 22 => Sum.inr ⟨(false, vertices_613), by decide +kernel⟩
  | 23 => Sum.inl 2
  | 24 => Sum.inr ⟨(false, vertices_361), by decide +kernel⟩
  | 25 => Sum.inl 3
  | 26 => Sum.inr ⟨(true, vertices_240), by decide +kernel⟩
  | 27 => Sum.inl 4
  | 28 => Sum.inl 5
  | 29 => Sum.inl 6
  | 30 => Sum.inl 7
  | 31 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 3 4 5 6 240
cert_row_4 1 0 1 3 6 8 662 146 1
cert_row_4 2 0 2 3 7 8 794 274 1
cert_row_4 3 1 2 5 7 8 844 76 3
cert_rows
cert_pivot_2 4 6 0 1
cert_heightProof 4
cert_coverFacet 0 662
cert_cover_5 0 1 0 1 3 6 146 662 1
cert_coverFacet 1 794
cert_cover_5 1 2 0 2 3 7 274 794 1
cert_coverFacet 2 92
cert_cover_2 2 2 1 3 5 28 92 3
cert_coverFacet 3 540
cert_cover_2 3 2 1 3 8 28 540 3
cert_coverFacet 4 844
cert_cover_5 4 3 1 2 5 7 76 844 3
cert_coverFacet 5 244
cert_cover_5 5 0 1 3 4 5 84 244 2
cert_coverFacet 6 676
cert_cover_2 6 4 1 6 8 164 676 3
cert_coverFacet 7 248
cert_cover_5 7 0 2 3 4 5 88 248 2
cert_coverFacet 8 408
cert_cover_2 8 3 2 6 7 152 408 3
cert_coverFacet 9 424
cert_cover_2 9 4 2 6 7 168 424 3
cert_coveringFacets_5
cert_coveringProof
cert_certificate 4 10
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0380

end
end BundlePart4

section BundlePart5
/- Source: ProjectionCertificates/R_m16e10q1_0381.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0381

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [779, 805, 361, 713, 625, 286, 566, 774, 154, 650, 722, 412, 180, 484, 456, 240, 73, 265, 521, 97, 289, 545, 577, 769, 22, 262, 518, 26, 138, 266, 522, 146, 530, 642, 770, 284, 52, 148, 164, 292, 548, 388, 772, 152, 200, 328, 392, 648, 112, 176, 560, 208, 592, 224, 352, 448, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_779, vertices_805, vertices_361, vertices_713, vertices_625, vertices_286, vertices_566, vertices_774, vertices_154, vertices_650, vertices_722, vertices_412, vertices_180, vertices_484, vertices_456, vertices_240] (by decide +kernel)
  polygons := literalFinset [vertices_73, vertices_265, vertices_521, vertices_97, vertices_289, vertices_545, vertices_577, vertices_769, vertices_22, vertices_262, vertices_518, vertices_26, vertices_138, vertices_266, vertices_522, vertices_146, vertices_530, vertices_642, vertices_770, vertices_284, vertices_52, vertices_148, vertices_164, vertices_292, vertices_548, vertices_388, vertices_772, vertices_152, vertices_200, vertices_328, vertices_392, vertices_648, vertices_112, vertices_176, vertices_560, vertices_208, vertices_592, vertices_224, vertices_352, vertices_448, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_779), (false, vertices_805), (false, vertices_361), (false, vertices_713), (false, vertices_625), (true, vertices_22), (true, vertices_262), (true, vertices_518), (true, vertices_26), (true, vertices_138), (true, vertices_146), (true, vertices_530), (true, vertices_642), (true, vertices_284), (true, vertices_52), (true, vertices_148), (true, vertices_164), (true, vertices_388), (true, vertices_152), (true, vertices_392), (true, vertices_176), (true, vertices_208), (true, vertices_224), (true, vertices_448)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 18 20 23 26 28 29 30 31 32
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_779) then 19 else
  if p.val = (false, vertices_805) then 21 else
  if p.val = (false, vertices_361) then 24 else
  if p.val = (false, vertices_713) then 25 else
  if p.val = (false, vertices_625) then 27 else
  if p.val = (true, vertices_22) then 0 else
  if p.val = (true, vertices_262) then 1 else
  if p.val = (true, vertices_518) then 2 else
  if p.val = (true, vertices_26) then 3 else
  if p.val = (true, vertices_138) then 4 else
  if p.val = (true, vertices_146) then 5 else
  if p.val = (true, vertices_530) then 6 else
  if p.val = (true, vertices_642) then 7 else
  if p.val = (true, vertices_284) then 22 else
  if p.val = (true, vertices_52) then 8 else
  if p.val = (true, vertices_148) then 9 else
  if p.val = (true, vertices_164) then 10 else
  if p.val = (true, vertices_388) then 11 else
  if p.val = (true, vertices_152) then 12 else
  if p.val = (true, vertices_392) then 13 else
  if p.val = (true, vertices_176) then 14 else
  if p.val = (true, vertices_208) then 15 else
  if p.val = (true, vertices_224) then 16 else
  if p.val = (true, vertices_448) then 17 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_22), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_262), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_518), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_26), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_138), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_146), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_530), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_642), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_52), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_148), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_164), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_388), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_152), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_392), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_176), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_208), by decide +kernel⟩
  | 16 => Sum.inr ⟨(true, vertices_224), by decide +kernel⟩
  | 17 => Sum.inr ⟨(true, vertices_448), by decide +kernel⟩
  | 18 => Sum.inl 0
  | 19 => Sum.inr ⟨(false, vertices_779), by decide +kernel⟩
  | 20 => Sum.inl 1
  | 21 => Sum.inr ⟨(false, vertices_805), by decide +kernel⟩
  | 22 => Sum.inr ⟨(true, vertices_284), by decide +kernel⟩
  | 23 => Sum.inl 2
  | 24 => Sum.inr ⟨(false, vertices_361), by decide +kernel⟩
  | 25 => Sum.inr ⟨(false, vertices_713), by decide +kernel⟩
  | 26 => Sum.inl 3
  | 27 => Sum.inr ⟨(false, vertices_625), by decide +kernel⟩
  | 28 => Sum.inl 4
  | 29 => Sum.inl 5
  | 30 => Sum.inl 6
  | 31 => Sum.inl 7
  | 32 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 1 2 3 7 284
cert_row_4 1 1 4 5 6 7 484 164 2
cert_row_4 2 0 1 3 4 8 566 22 3
cert_row_4 3 0 3 5 6 8 722 146 2
cert_rows
cert_pivot_2 2 7 1 0
cert_heightProof 4
cert_coverFacet 0 286
cert_cover_5 0 0 0 1 2 3 22 286 2
cert_coverFacet 1 566
cert_cover_5 1 2 0 1 3 4 22 566 3
cert_coverFacet 2 774
cert_cover_2 2 1 0 7 8 262 774 3
cert_coverFacet 3 154
cert_cover_2 3 2 0 3 6 26 154 3
cert_coverFacet 4 650
cert_cover_2 4 2 0 6 8 138 650 3
cert_coverFacet 5 722
cert_cover_5 5 3 0 3 5 6 146 722 2
cert_coverFacet 6 412
cert_cover_5 6 0 1 2 3 6 284 412 3
cert_coverFacet 7 180
cert_cover_2 7 3 1 4 6 52 180 3
cert_coverFacet 8 484
cert_cover_5 8 1 1 4 5 6 164 484 2
cert_coverFacet 9 456
cert_cover_2 9 5 2 6 7 200 456 3
cert_coverFacet 10 240
cert_cover_2 10 4 3 5 6 112 240 3
cert_coveringFacets_6
cert_coveringProof_3
cert_certificate 4 11
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0381

end
end BundlePart5

section BundlePart6
/- Source: ProjectionCertificates/R_m16e10q1_0382.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0382

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [659, 837, 217, 793, 329, 737, 310, 534, 614, 410, 426, 674, 236, 300, 332, 788, 25, 73, 265, 145, 529, 193, 321, 577, 641, 769, 22, 38, 518, 394, 146, 274, 530, 162, 290, 546, 642, 44, 76, 268, 276, 532, 100, 292, 324, 580, 772, 152, 280, 168, 296, 200, 328, 784, 224, 608, 672]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_659, vertices_837, vertices_217, vertices_793, vertices_329, vertices_737, vertices_310, vertices_534, vertices_614, vertices_410, vertices_426, vertices_674, vertices_236, vertices_300, vertices_332, vertices_788] (by decide +kernel)
  polygons := literalFinset [vertices_25, vertices_73, vertices_265, vertices_145, vertices_529, vertices_193, vertices_321, vertices_577, vertices_641, vertices_769, vertices_22, vertices_38, vertices_518, vertices_394, vertices_146, vertices_274, vertices_530, vertices_162, vertices_290, vertices_546, vertices_642, vertices_44, vertices_76, vertices_268, vertices_276, vertices_532, vertices_100, vertices_292, vertices_324, vertices_580, vertices_772, vertices_152, vertices_280, vertices_168, vertices_296, vertices_200, vertices_328, vertices_784, vertices_224, vertices_608, vertices_672] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_659), (false, vertices_837), (false, vertices_217), (false, vertices_793), (false, vertices_329), (false, vertices_737), (true, vertices_22), (true, vertices_38), (true, vertices_518), (true, vertices_394), (true, vertices_274), (true, vertices_162), (true, vertices_290), (true, vertices_546), (true, vertices_44), (true, vertices_76), (true, vertices_268), (true, vertices_276), (true, vertices_532), (true, vertices_100), (true, vertices_292), (true, vertices_168), (true, vertices_296)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 17 20 22 25 26 28 29 30 31
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_659) then 18 else
  if p.val = (false, vertices_837) then 21 else
  if p.val = (false, vertices_217) then 23 else
  if p.val = (false, vertices_793) then 24 else
  if p.val = (false, vertices_329) then 0 else
  if p.val = (false, vertices_737) then 27 else
  if p.val = (true, vertices_22) then 1 else
  if p.val = (true, vertices_38) then 2 else
  if p.val = (true, vertices_518) then 3 else
  if p.val = (true, vertices_394) then 19 else
  if p.val = (true, vertices_274) then 4 else
  if p.val = (true, vertices_162) then 5 else
  if p.val = (true, vertices_290) then 6 else
  if p.val = (true, vertices_546) then 7 else
  if p.val = (true, vertices_44) then 8 else
  if p.val = (true, vertices_76) then 9 else
  if p.val = (true, vertices_268) then 10 else
  if p.val = (true, vertices_276) then 11 else
  if p.val = (true, vertices_532) then 12 else
  if p.val = (true, vertices_100) then 13 else
  if p.val = (true, vertices_292) then 14 else
  if p.val = (true, vertices_168) then 15 else
  if p.val = (true, vertices_296) then 16 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_329), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_22), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_38), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_518), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_274), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_162), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_290), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_546), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_44), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_76), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_268), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_276), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_532), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_100), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_292), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_168), by decide +kernel⟩
  | 16 => Sum.inr ⟨(true, vertices_296), by decide +kernel⟩
  | 17 => Sum.inl 0
  | 18 => Sum.inr ⟨(false, vertices_659), by decide +kernel⟩
  | 19 => Sum.inr ⟨(true, vertices_394), by decide +kernel⟩
  | 20 => Sum.inl 1
  | 21 => Sum.inr ⟨(false, vertices_837), by decide +kernel⟩
  | 22 => Sum.inl 2
  | 23 => Sum.inr ⟨(false, vertices_217), by decide +kernel⟩
  | 24 => Sum.inr ⟨(false, vertices_793), by decide +kernel⟩
  | 25 => Sum.inl 3
  | 26 => Sum.inl 4
  | 27 => Sum.inr ⟨(false, vertices_737), by decide +kernel⟩
  | 28 => Sum.inl 5
  | 29 => Sum.inl 6
  | 30 => Sum.inl 7
  | 31 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 3 4 7 310 22 3
cert_row_2 1 0 2 6 7 394
cert_row_4 2 0 1 4 5 8 614 38 3
cert_row_4 3 1 2 4 5 6 236 44 3
cert_rows
cert_pivot_2 3 7 0 1
cert_heightProof 4
cert_coverFacet 0 310
cert_cover_5 0 0 0 1 3 4 22 310 3
cert_coverFacet 1 534
cert_cover_2 1 1 0 3 8 22 534 3
cert_coverFacet 2 614
cert_cover_5 2 2 0 1 4 5 38 614 3
cert_coverFacet 3 410
cert_cover_5 3 1 0 2 3 6 394 410 2
cert_coverFacet 4 426
cert_cover_5 4 1 0 2 4 6 394 426 2
cert_coverFacet 5 674
cert_cover_2 5 4 0 6 8 162 674 3
cert_coverFacet 6 236
cert_cover_5 6 3 1 2 4 5 44 236 3
cert_coverFacet 7 300
cert_cover_2 7 2 1 4 7 44 300 3
cert_coverFacet 8 332
cert_cover_2 8 2 1 5 7 76 332 3
cert_coverFacet 9 788
cert_cover_2 9 3 1 7 8 276 788 3
cert_coveringFacets_5
cert_coveringProof
cert_certificate 4 10
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0382

end
end BundlePart6

section BundlePart7
/- Source: ProjectionCertificates/R_m16e10q1_0383.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0383

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [611, 397, 597, 229, 773, 681, 777, 790, 314, 218, 234, 594, 802, 468, 408, 808, 69, 133, 261, 517, 137, 265, 521, 97, 161, 545, 577, 769, 26, 42, 202, 82, 274, 530, 98, 290, 546, 578, 770, 84, 276, 532, 196, 388, 772, 152, 280, 168, 296, 552, 392, 776, 208, 592, 400, 224, 800]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_611, vertices_397, vertices_597, vertices_229, vertices_773, vertices_681, vertices_777, vertices_790, vertices_314, vertices_218, vertices_234, vertices_594, vertices_802, vertices_468, vertices_408, vertices_808] (by decide +kernel)
  polygons := literalFinset [vertices_69, vertices_133, vertices_261, vertices_517, vertices_137, vertices_265, vertices_521, vertices_97, vertices_161, vertices_545, vertices_577, vertices_769, vertices_26, vertices_42, vertices_202, vertices_82, vertices_274, vertices_530, vertices_98, vertices_290, vertices_546, vertices_578, vertices_770, vertices_84, vertices_276, vertices_532, vertices_196, vertices_388, vertices_772, vertices_152, vertices_280, vertices_168, vertices_296, vertices_552, vertices_392, vertices_776, vertices_208, vertices_592, vertices_400, vertices_224, vertices_800] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_611), (false, vertices_397), (false, vertices_597), (false, vertices_229), (false, vertices_773), (false, vertices_681), (false, vertices_777), (true, vertices_26), (true, vertices_42), (true, vertices_202), (true, vertices_82), (true, vertices_274), (true, vertices_530), (true, vertices_290), (true, vertices_770), (true, vertices_276), (true, vertices_152), (true, vertices_280), (true, vertices_296), (true, vertices_208), (true, vertices_400), (true, vertices_800)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 16 19 23 25 26 27 28 29 30
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_611) then 17 else
  if p.val = (false, vertices_397) then 20 else
  if p.val = (false, vertices_597) then 21 else
  if p.val = (false, vertices_229) then 22 else
  if p.val = (false, vertices_773) then 0 else
  if p.val = (false, vertices_681) then 24 else
  if p.val = (false, vertices_777) then 1 else
  if p.val = (true, vertices_26) then 2 else
  if p.val = (true, vertices_42) then 3 else
  if p.val = (true, vertices_202) then 18 else
  if p.val = (true, vertices_82) then 4 else
  if p.val = (true, vertices_274) then 5 else
  if p.val = (true, vertices_530) then 6 else
  if p.val = (true, vertices_290) then 7 else
  if p.val = (true, vertices_770) then 8 else
  if p.val = (true, vertices_276) then 9 else
  if p.val = (true, vertices_152) then 10 else
  if p.val = (true, vertices_280) then 11 else
  if p.val = (true, vertices_296) then 12 else
  if p.val = (true, vertices_208) then 13 else
  if p.val = (true, vertices_400) then 14 else
  if p.val = (true, vertices_800) then 15 else
  0
cert_priority
cert_nodeAtPriority_5 0 773 1 777 26 42 82 274 530 290 770 276 152 280 296 208 400 800 611 202 397 597 229 681
cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 3 7 8 790 274 1
cert_row_4 1 0 2 3 4 7 314 26 3
cert_row_2 2 0 2 5 6 202
cert_row_4 3 1 3 5 6 7 468 84 3
cert_rows
cert_pivot_2 8 4 0 1
cert_heightProof 4
cert_coverFacet 0 790
cert_cover_5 0 0 0 1 3 7 274 790 1
cert_coverFacet 1 314
cert_cover_5 1 1 0 2 3 4 26 314 3
cert_coverFacet 2 218
cert_cover_5 2 2 0 2 3 5 26 218 3
cert_coverFacet 3 234
cert_cover_5 3 2 0 2 4 5 42 234 3
cert_coverFacet 4 594
cert_cover_2 4 3 0 5 8 82 594 3
cert_coverFacet 5 802
cert_cover_2 5 4 0 7 8 290 802 3
cert_coverFacet 6 468
cert_cover_5 6 3 1 3 5 6 84 468 3
cert_coverFacet 7 408
cert_cover_2 7 3 2 6 7 152 408 3
cert_coverFacet 8 808
cert_cover_2 8 4 2 7 8 296 808 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0383

end
end BundlePart7

section BundlePart8
/- Source: ProjectionCertificates/R_m16e10q1_0384.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0384

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [419, 565, 405, 293, 665, 737, 838, 410, 234, 330, 610, 802, 348, 604, 804, 712, 21, 37, 261, 145, 529, 161, 289, 545, 385, 641, 74, 138, 266, 98, 162, 290, 546, 322, 578, 386, 770, 92, 276, 532, 292, 548, 324, 580, 772, 152, 280, 536, 200, 328, 584, 648, 400, 224, 608, 800, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_419, vertices_565, vertices_405, vertices_293, vertices_665, vertices_737, vertices_838, vertices_410, vertices_234, vertices_330, vertices_610, vertices_802, vertices_348, vertices_604, vertices_804, vertices_712] (by decide +kernel)
  polygons := literalFinset [vertices_21, vertices_37, vertices_261, vertices_145, vertices_529, vertices_161, vertices_289, vertices_545, vertices_385, vertices_641, vertices_74, vertices_138, vertices_266, vertices_98, vertices_162, vertices_290, vertices_546, vertices_322, vertices_578, vertices_386, vertices_770, vertices_92, vertices_276, vertices_532, vertices_292, vertices_548, vertices_324, vertices_580, vertices_772, vertices_152, vertices_280, vertices_536, vertices_200, vertices_328, vertices_584, vertices_648, vertices_400, vertices_224, vertices_608, vertices_800, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_419), (false, vertices_565), (false, vertices_405), (false, vertices_293), (false, vertices_665), (false, vertices_737), (true, vertices_74), (true, vertices_138), (true, vertices_266), (true, vertices_98), (true, vertices_546), (true, vertices_322), (true, vertices_578), (true, vertices_770), (true, vertices_92), (true, vertices_324), (true, vertices_580), (true, vertices_772), (true, vertices_280), (true, vertices_200), (true, vertices_328), (true, vertices_584), (true, vertices_800)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 17 22 19 25 26 28 29 30 31
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_419) then 18 else
  if p.val = (false, vertices_565) then 23 else
  if p.val = (false, vertices_405) then 24 else
  if p.val = (false, vertices_293) then 0 else
  if p.val = (false, vertices_665) then 20 else
  if p.val = (false, vertices_737) then 27 else
  if p.val = (true, vertices_74) then 1 else
  if p.val = (true, vertices_138) then 2 else
  if p.val = (true, vertices_266) then 3 else
  if p.val = (true, vertices_98) then 4 else
  if p.val = (true, vertices_546) then 5 else
  if p.val = (true, vertices_322) then 6 else
  if p.val = (true, vertices_578) then 7 else
  if p.val = (true, vertices_770) then 8 else
  if p.val = (true, vertices_92) then 21 else
  if p.val = (true, vertices_324) then 9 else
  if p.val = (true, vertices_580) then 10 else
  if p.val = (true, vertices_772) then 11 else
  if p.val = (true, vertices_280) then 12 else
  if p.val = (true, vertices_200) then 13 else
  if p.val = (true, vertices_328) then 14 else
  if p.val = (true, vertices_584) then 15 else
  if p.val = (true, vertices_800) then 16 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_293), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_74), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_138), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_266), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_98), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_546), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_322), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_578), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_770), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_324), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_580), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_772), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_280), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_200), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_328), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_584), by decide +kernel⟩
  | 16 => Sum.inr ⟨(true, vertices_800), by decide +kernel⟩
  | 17 => Sum.inl 0
  | 18 => Sum.inr ⟨(false, vertices_419), by decide +kernel⟩
  | 19 => Sum.inl 2
  | 20 => Sum.inr ⟨(false, vertices_665), by decide +kernel⟩
  | 21 => Sum.inr ⟨(true, vertices_92), by decide +kernel⟩
  | 22 => Sum.inl 1
  | 23 => Sum.inr ⟨(false, vertices_565), by decide +kernel⟩
  | 24 => Sum.inr ⟨(false, vertices_405), by decide +kernel⟩
  | 25 => Sum.inl 3
  | 26 => Sum.inl 4
  | 27 => Sum.inr ⟨(false, vertices_737), by decide +kernel⟩
  | 28 => Sum.inl 5
  | 29 => Sum.inl 6
  | 30 => Sum.inl 7
  | 31 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 5 7 8 838 322 1
cert_row_2 1 1 2 3 5 92
cert_row_4 2 0 2 3 6 7 410 138 2
cert_row_4 3 0 2 4 5 6 234 74 2
cert_rows
cert_pivot_2 8 1 3 0
cert_heightProof 4
cert_coverFacet 0 838
cert_cover_5 0 0 0 1 5 7 322 838 1
cert_coverFacet 1 410
cert_cover_5 1 2 0 2 3 6 138 410 2
cert_coverFacet 2 234
cert_cover_5 2 3 0 2 4 5 74 234 2
cert_coverFacet 3 330
cert_cover_2 3 2 0 5 7 74 330 3
cert_coverFacet 4 610
cert_cover_2 4 4 0 5 8 98 610 3
cert_coverFacet 5 802
cert_cover_2 5 4 0 7 8 290 802 3
cert_coverFacet 6 348
cert_cover_5 6 1 1 2 3 7 92 348 3
cert_coverFacet 7 604
cert_cover_5 7 1 1 2 3 8 92 604 3
cert_coverFacet 8 804
cert_cover_2 8 4 1 7 8 292 804 3
cert_coverFacet 9 712
cert_cover_2 9 5 2 6 8 200 712 3
cert_coveringFacets_5
cert_coveringProof
cert_certificate 4 10
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0384

end
end BundlePart8

section BundlePart9
/- Source: ProjectionCertificates/R_m16e10q1_0385.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0385

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [647, 229, 805, 713, 849, 353, 174, 302, 790, 602, 282, 650, 184, 312, 216, 496, 37, 133, 517, 97, 289, 193, 321, 577, 641, 769, 46, 134, 262, 518, 26, 138, 266, 522, 274, 530, 642, 164, 292, 772, 56, 88, 152, 280, 168, 296, 200, 584, 648, 176, 304, 208, 336, 592, 784, 224, 352]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_647, vertices_229, vertices_805, vertices_713, vertices_849, vertices_353, vertices_174, vertices_302, vertices_790, vertices_602, vertices_282, vertices_650, vertices_184, vertices_312, vertices_216, vertices_496] (by decide +kernel)
  polygons := literalFinset [vertices_37, vertices_133, vertices_517, vertices_97, vertices_289, vertices_193, vertices_321, vertices_577, vertices_641, vertices_769, vertices_46, vertices_134, vertices_262, vertices_518, vertices_26, vertices_138, vertices_266, vertices_522, vertices_274, vertices_530, vertices_642, vertices_164, vertices_292, vertices_772, vertices_56, vertices_88, vertices_152, vertices_280, vertices_168, vertices_296, vertices_200, vertices_584, vertices_648, vertices_176, vertices_304, vertices_208, vertices_336, vertices_592, vertices_784, vertices_224, vertices_352] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_647), (false, vertices_229), (false, vertices_805), (false, vertices_713), (false, vertices_849), (false, vertices_353), (true, vertices_46), (true, vertices_262), (true, vertices_26), (true, vertices_138), (true, vertices_266), (true, vertices_522), (true, vertices_274), (true, vertices_530), (true, vertices_56), (true, vertices_88), (true, vertices_152), (true, vertices_280), (true, vertices_168), (true, vertices_296), (true, vertices_176), (true, vertices_304), (true, vertices_208)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 17 20 23 25 27 28 29 30 31
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_647) then 18 else
  if p.val = (false, vertices_229) then 21 else
  if p.val = (false, vertices_805) then 22 else
  if p.val = (false, vertices_713) then 24 else
  if p.val = (false, vertices_849) then 26 else
  if p.val = (false, vertices_353) then 0 else
  if p.val = (true, vertices_46) then 19 else
  if p.val = (true, vertices_262) then 1 else
  if p.val = (true, vertices_26) then 2 else
  if p.val = (true, vertices_138) then 3 else
  if p.val = (true, vertices_266) then 4 else
  if p.val = (true, vertices_522) then 5 else
  if p.val = (true, vertices_274) then 6 else
  if p.val = (true, vertices_530) then 7 else
  if p.val = (true, vertices_56) then 8 else
  if p.val = (true, vertices_88) then 9 else
  if p.val = (true, vertices_152) then 10 else
  if p.val = (true, vertices_280) then 11 else
  if p.val = (true, vertices_168) then 12 else
  if p.val = (true, vertices_296) then 13 else
  if p.val = (true, vertices_176) then 14 else
  if p.val = (true, vertices_304) then 15 else
  if p.val = (true, vertices_208) then 16 else
  0
cert_priority
cert_nodeAtPriority_14 353 262 26 138 266 522 274 530 56 88 152 280 168 296 176 304 208 647 46 229 805 713 849
cert_priority_injective
cert_incidenceProof
cert_row_4 0 3 4 5 6 7 496 176 2
cert_row_2 1 0 1 2 4 46
cert_row_4 2 0 1 3 7 8 790 262 2
cert_row_4 3 0 2 3 5 8 602 26 3
cert_rows
cert_pivot_2 6 4 1 0
cert_heightProof 4
cert_coverFacet 0 174
cert_cover_5 0 1 0 1 2 6 46 174 3
cert_coverFacet 1 302
cert_cover_5 1 1 0 1 2 7 46 302 3
cert_coverFacet 2 790
cert_cover_5 2 2 0 1 3 7 262 790 2
cert_coverFacet 3 602
cert_cover_5 3 3 0 2 3 5 26 602 3
cert_coverFacet 4 282
cert_cover_2 4 2 0 3 7 26 282 3
cert_coverFacet 5 650
cert_cover_2 5 2 0 6 8 138 650 3
cert_coverFacet 6 184
cert_cover_2 6 3 2 4 6 56 184 3
cert_coverFacet 7 312
cert_cover_2 7 3 2 4 7 56 312 3
cert_coverFacet 8 216
cert_cover_2 8 3 2 5 6 88 216 3
cert_coverFacet 9 496
cert_cover_5 9 0 3 4 5 6 176 496 2
cert_coveringFacets_5
cert_coveringProof
cert_certificate 4 10
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0385

end
end BundlePart9

section BundlePart10
/- Source: ProjectionCertificates/R_m16e10q1_0386.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0386

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [899, 109, 653, 789, 357, 425, 598, 714, 178, 818, 210, 418, 588, 340, 248, 368, 13, 101, 261, 517, 41, 137, 289, 385, 641, 769, 50, 82, 146, 530, 162, 290, 194, 578, 386, 642, 770, 76, 524, 84, 276, 532, 324, 580, 104, 168, 200, 584, 648, 112, 176, 304, 208, 336, 784, 352, 416]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_899, vertices_109, vertices_653, vertices_789, vertices_357, vertices_425, vertices_598, vertices_714, vertices_178, vertices_818, vertices_210, vertices_418, vertices_588, vertices_340, vertices_248, vertices_368] (by decide +kernel)
  polygons := literalFinset [vertices_13, vertices_101, vertices_261, vertices_517, vertices_41, vertices_137, vertices_289, vertices_385, vertices_641, vertices_769, vertices_50, vertices_82, vertices_146, vertices_530, vertices_162, vertices_290, vertices_194, vertices_578, vertices_386, vertices_642, vertices_770, vertices_76, vertices_524, vertices_84, vertices_276, vertices_532, vertices_324, vertices_580, vertices_104, vertices_168, vertices_200, vertices_584, vertices_648, vertices_112, vertices_176, vertices_304, vertices_208, vertices_336, vertices_784, vertices_352, vertices_416] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_899), (false, vertices_109), (false, vertices_653), (false, vertices_789), (false, vertices_357), (false, vertices_425), (true, vertices_50), (true, vertices_82), (true, vertices_146), (true, vertices_530), (true, vertices_162), (true, vertices_290), (true, vertices_194), (true, vertices_578), (true, vertices_84), (true, vertices_580), (true, vertices_200), (true, vertices_584), (true, vertices_112), (true, vertices_176), (true, vertices_304), (true, vertices_208), (true, vertices_336)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 17 22 19 26 27 28 29 30 31
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_899) then 18 else
  if p.val = (false, vertices_109) then 23 else
  if p.val = (false, vertices_653) then 20 else
  if p.val = (false, vertices_789) then 24 else
  if p.val = (false, vertices_357) then 25 else
  if p.val = (false, vertices_425) then 21 else
  if p.val = (true, vertices_50) then 0 else
  if p.val = (true, vertices_82) then 1 else
  if p.val = (true, vertices_146) then 2 else
  if p.val = (true, vertices_530) then 3 else
  if p.val = (true, vertices_162) then 4 else
  if p.val = (true, vertices_290) then 5 else
  if p.val = (true, vertices_194) then 6 else
  if p.val = (true, vertices_578) then 7 else
  if p.val = (true, vertices_84) then 8 else
  if p.val = (true, vertices_580) then 9 else
  if p.val = (true, vertices_200) then 10 else
  if p.val = (true, vertices_584) then 11 else
  if p.val = (true, vertices_112) then 12 else
  if p.val = (true, vertices_176) then 13 else
  if p.val = (true, vertices_304) then 14 else
  if p.val = (true, vertices_208) then 15 else
  if p.val = (true, vertices_336) then 16 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_50), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_82), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_146), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_530), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_162), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_290), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_194), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_578), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_84), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_580), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_200), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_584), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_112), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_176), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_304), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_208), by decide +kernel⟩
  | 16 => Sum.inr ⟨(true, vertices_336), by decide +kernel⟩
  | 17 => Sum.inl 0
  | 18 => Sum.inr ⟨(false, vertices_899), by decide +kernel⟩
  | 19 => Sum.inl 2
  | 20 => Sum.inr ⟨(false, vertices_653), by decide +kernel⟩
  | 21 => Sum.inr ⟨(false, vertices_425), by decide +kernel⟩
  | 22 => Sum.inl 1
  | 23 => Sum.inr ⟨(false, vertices_109), by decide +kernel⟩
  | 24 => Sum.inr ⟨(false, vertices_789), by decide +kernel⟩
  | 25 => Sum.inr ⟨(false, vertices_357), by decide +kernel⟩
  | 26 => Sum.inl 3
  | 27 => Sum.inl 4
  | 28 => Sum.inl 5
  | 29 => Sum.inl 6
  | 30 => Sum.inl 7
  | 31 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 3 5 8 598 82 1
cert_row_4 1 0 3 4 7 8 818 50 3
cert_row_4 2 0 2 5 6 8 714 194 1
cert_row_4 3 2 3 4 5 6 248 104 1
cert_rows
cert_pivot_2 1 7 0 2
cert_heightProof 4
cert_coverFacet 0 598
cert_cover_5 0 0 0 1 3 5 82 598 1
cert_coverFacet 1 714
cert_cover_5 1 2 0 2 5 6 194 714 1
cert_coverFacet 2 178
cert_cover_2 2 3 0 4 6 50 178 3
cert_coverFacet 3 818
cert_cover_5 3 1 0 3 4 7 50 818 3
cert_coverFacet 4 210
cert_cover_2 4 3 0 5 6 82 210 3
cert_coverFacet 5 418
cert_cover_2 5 4 0 6 7 162 418 3
cert_coverFacet 6 588
cert_cover_2 6 2 1 5 8 76 588 3
cert_coverFacet 7 340
cert_cover_2 7 3 1 5 7 84 340 3
cert_coverFacet 8 248
cert_cover_5 8 3 2 3 4 5 104 248 1
cert_coverFacet 9 368
cert_cover_2 9 4 3 5 7 112 368 3
cert_coveringFacets_5
cert_coveringProof
cert_certificate 4 10
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0386

end
end BundlePart10

section BundlePart11
/- Source: ProjectionCertificates/R_m16e10q1_0387.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0387

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [587, 451, 771, 901, 665, 233, 790, 370, 626, 316, 156, 172, 660, 484, 568, 616, 67, 259, 515, 73, 137, 521, 193, 385, 641, 769, 114, 274, 530, 322, 578, 770, 28, 44, 140, 148, 276, 532, 164, 292, 388, 644, 772, 56, 152, 536, 104, 168, 552, 584, 304, 560, 656, 224, 352, 608, 448]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_587, vertices_451, vertices_771, vertices_901, vertices_665, vertices_233, vertices_790, vertices_370, vertices_626, vertices_316, vertices_156, vertices_172, vertices_660, vertices_484, vertices_568, vertices_616] (by decide +kernel)
  polygons := literalFinset [vertices_67, vertices_259, vertices_515, vertices_73, vertices_137, vertices_521, vertices_193, vertices_385, vertices_641, vertices_769, vertices_114, vertices_274, vertices_530, vertices_322, vertices_578, vertices_770, vertices_28, vertices_44, vertices_140, vertices_148, vertices_276, vertices_532, vertices_164, vertices_292, vertices_388, vertices_644, vertices_772, vertices_56, vertices_152, vertices_536, vertices_104, vertices_168, vertices_552, vertices_584, vertices_304, vertices_560, vertices_656, vertices_224, vertices_352, vertices_608, vertices_448] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_587), (false, vertices_451), (false, vertices_771), (false, vertices_901), (false, vertices_665), (false, vertices_233), (true, vertices_114), (true, vertices_274), (true, vertices_530), (true, vertices_28), (true, vertices_44), (true, vertices_140), (true, vertices_148), (true, vertices_276), (true, vertices_532), (true, vertices_164), (true, vertices_292), (true, vertices_56), (true, vertices_552), (true, vertices_304), (true, vertices_560), (true, vertices_352), (true, vertices_608)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 23 17 19 26 27 28 29 30 31
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_587) then 20 else
  if p.val = (false, vertices_451) then 24 else
  if p.val = (false, vertices_771) then 0 else
  if p.val = (false, vertices_901) then 18 else
  if p.val = (false, vertices_665) then 21 else
  if p.val = (false, vertices_233) then 22 else
  if p.val = (true, vertices_114) then 25 else
  if p.val = (true, vertices_274) then 1 else
  if p.val = (true, vertices_530) then 2 else
  if p.val = (true, vertices_28) then 3 else
  if p.val = (true, vertices_44) then 4 else
  if p.val = (true, vertices_140) then 5 else
  if p.val = (true, vertices_148) then 6 else
  if p.val = (true, vertices_276) then 7 else
  if p.val = (true, vertices_532) then 8 else
  if p.val = (true, vertices_164) then 9 else
  if p.val = (true, vertices_292) then 10 else
  if p.val = (true, vertices_56) then 11 else
  if p.val = (true, vertices_552) then 12 else
  if p.val = (true, vertices_304) then 13 else
  if p.val = (true, vertices_560) then 14 else
  if p.val = (true, vertices_352) then 15 else
  if p.val = (true, vertices_608) then 16 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_771), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_274), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_530), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_28), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_44), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_140), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_148), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_276), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_532), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_164), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_292), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_56), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_552), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_304), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_560), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_352), by decide +kernel⟩
  | 16 => Sum.inr ⟨(true, vertices_608), by decide +kernel⟩
  | 17 => Sum.inl 1
  | 18 => Sum.inr ⟨(false, vertices_901), by decide +kernel⟩
  | 19 => Sum.inl 2
  | 20 => Sum.inr ⟨(false, vertices_587), by decide +kernel⟩
  | 21 => Sum.inr ⟨(false, vertices_665), by decide +kernel⟩
  | 22 => Sum.inr ⟨(false, vertices_233), by decide +kernel⟩
  | 23 => Sum.inl 0
  | 24 => Sum.inr ⟨(false, vertices_451), by decide +kernel⟩
  | 25 => Sum.inr ⟨(true, vertices_114), by decide +kernel⟩
  | 26 => Sum.inl 3
  | 27 => Sum.inl 4
  | 28 => Sum.inl 5
  | 29 => Sum.inl 6
  | 30 => Sum.inl 7
  | 31 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 3 7 8 790 274 1
cert_row_2 1 0 3 4 5 114
cert_row_4 2 1 2 3 4 7 316 28 3
cert_row_4 3 1 4 5 6 7 484 164 2
cert_rows
cert_pivot_2 8 0 2 1
cert_heightProof 4
cert_coverFacet 0 790
cert_cover_5 0 0 0 1 3 7 274 790 1
cert_coverFacet 1 370
cert_cover_5 1 1 0 3 4 7 114 370 3
cert_coverFacet 2 626
cert_cover_5 2 1 0 3 4 8 114 626 3
cert_coverFacet 3 316
cert_cover_5 3 2 1 2 3 4 28 316 3
cert_coverFacet 4 156
cert_cover_2 4 2 1 3 6 28 156 3
cert_coverFacet 5 172
cert_cover_2 5 2 1 4 6 44 172 3
cert_coverFacet 6 660
cert_cover_2 6 3 1 6 8 148 660 3
cert_coverFacet 7 484
cert_cover_5 7 3 1 4 5 6 164 484 2
cert_coverFacet 8 568
cert_cover_2 8 3 2 4 8 56 568 3
cert_coverFacet 9 616
cert_cover_2 9 4 2 5 8 104 616 3
cert_coveringFacets_5
cert_coveringProof
cert_certificate 4 10
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0387

end
end BundlePart11

section BundlePart12
/- Source: ProjectionCertificates/R_m16e10q1_0388.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0388

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [803, 565, 149, 421, 409, 849, 614, 346, 234, 426, 834, 668, 228, 708, 600, 712, 21, 37, 133, 145, 273, 529, 289, 545, 385, 769, 170, 74, 266, 98, 290, 546, 322, 578, 770, 148, 532, 100, 164, 548, 196, 580, 644, 88, 152, 280, 536, 200, 584, 392, 648, 336, 592, 224, 416, 704, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_803, vertices_565, vertices_149, vertices_421, vertices_409, vertices_849, vertices_614, vertices_346, vertices_234, vertices_426, vertices_834, vertices_668, vertices_228, vertices_708, vertices_600, vertices_712] (by decide +kernel)
  polygons := literalFinset [vertices_21, vertices_37, vertices_133, vertices_145, vertices_273, vertices_529, vertices_289, vertices_545, vertices_385, vertices_769, vertices_170, vertices_74, vertices_266, vertices_98, vertices_290, vertices_546, vertices_322, vertices_578, vertices_770, vertices_148, vertices_532, vertices_100, vertices_164, vertices_548, vertices_196, vertices_580, vertices_644, vertices_88, vertices_152, vertices_280, vertices_536, vertices_200, vertices_584, vertices_392, vertices_648, vertices_336, vertices_592, vertices_224, vertices_416, vertices_704, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_803), (false, vertices_565), (false, vertices_149), (false, vertices_421), (false, vertices_409), (false, vertices_849), (true, vertices_170), (true, vertices_74), (true, vertices_266), (true, vertices_98), (true, vertices_322), (true, vertices_578), (true, vertices_100), (true, vertices_196), (true, vertices_580), (true, vertices_644), (true, vertices_88), (true, vertices_536), (true, vertices_200), (true, vertices_584), (true, vertices_648), (true, vertices_224), (true, vertices_704)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 17 20 23 25 27 28 29 30 31
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_803) then 18 else
  if p.val = (false, vertices_565) then 21 else
  if p.val = (false, vertices_149) then 0 else
  if p.val = (false, vertices_421) then 22 else
  if p.val = (false, vertices_409) then 24 else
  if p.val = (false, vertices_849) then 26 else
  if p.val = (true, vertices_170) then 19 else
  if p.val = (true, vertices_74) then 1 else
  if p.val = (true, vertices_266) then 2 else
  if p.val = (true, vertices_98) then 3 else
  if p.val = (true, vertices_322) then 4 else
  if p.val = (true, vertices_578) then 5 else
  if p.val = (true, vertices_100) then 6 else
  if p.val = (true, vertices_196) then 7 else
  if p.val = (true, vertices_580) then 8 else
  if p.val = (true, vertices_644) then 9 else
  if p.val = (true, vertices_88) then 10 else
  if p.val = (true, vertices_536) then 11 else
  if p.val = (true, vertices_200) then 12 else
  if p.val = (true, vertices_584) then 13 else
  if p.val = (true, vertices_648) then 14 else
  if p.val = (true, vertices_224) then 15 else
  if p.val = (true, vertices_704) then 16 else
  0
cert_priority
cert_nodeAtPriority_14 149 74 266 98 322 578 100 196 580 644 88 536 200 584 648 224 704 803 170 565 421 409 849
cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 2 3 5 7 346 74 2
cert_row_4 1 0 1 4 5 8 614 98 1
cert_row_2 2 0 2 4 6 170
cert_row_4 3 1 2 3 6 8 668 148 1
cert_rows
cert_pivot_2 7 5 0 1
cert_heightProof 4
cert_coverFacet 0 614
cert_cover_5 0 1 0 1 4 5 98 614 1
cert_coverFacet 1 346
cert_cover_5 1 0 0 2 3 5 74 346 2
cert_coverFacet 2 234
cert_cover_5 2 2 0 2 4 5 170 234 3
cert_coverFacet 3 426
cert_cover_5 3 2 0 2 4 7 170 426 3
cert_coverFacet 4 834
cert_cover_2 4 5 0 7 8 322 834 3
cert_coverFacet 5 668
cert_cover_5 5 3 1 2 3 6 148 668 1
cert_coverFacet 6 228
cert_cover_2 6 4 1 5 6 100 228 3
cert_coverFacet 7 708
cert_cover_2 7 5 1 6 8 196 708 3
cert_coverFacet 8 600
cert_cover_2 8 3 2 5 8 88 600 3
cert_coverFacet 9 712
cert_cover_2 9 5 2 6 8 200 712 3
cert_coveringFacets_5
cert_coveringProof
cert_certificate 4 10
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0388

end
end BundlePart12

section BundlePart13
/- Source: ProjectionCertificates/R_m16e10q1_0389.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0389

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [647, 403, 355, 611, 157, 597, 337, 810, 898, 92, 620, 908, 120, 184, 424, 496, 99, 131, 259, 515, 21, 133, 517, 81, 145, 273, 321, 577, 290, 546, 386, 642, 770, 28, 76, 140, 524, 84, 580, 644, 56, 88, 152, 104, 168, 296, 552, 392, 776, 112, 176, 336, 400, 352, 608, 416, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_647, vertices_403, vertices_355, vertices_611, vertices_157, vertices_597, vertices_337, vertices_810, vertices_898, vertices_92, vertices_620, vertices_908, vertices_120, vertices_184, vertices_424, vertices_496] (by decide +kernel)
  polygons := literalFinset [vertices_99, vertices_131, vertices_259, vertices_515, vertices_21, vertices_133, vertices_517, vertices_81, vertices_145, vertices_273, vertices_321, vertices_577, vertices_290, vertices_546, vertices_386, vertices_642, vertices_770, vertices_28, vertices_76, vertices_140, vertices_524, vertices_84, vertices_580, vertices_644, vertices_56, vertices_88, vertices_152, vertices_104, vertices_168, vertices_296, vertices_552, vertices_392, vertices_776, vertices_112, vertices_176, vertices_336, vertices_400, vertices_352, vertices_608, vertices_416, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_647), (false, vertices_403), (false, vertices_355), (false, vertices_611), (false, vertices_157), (false, vertices_597), (false, vertices_337), (true, vertices_770), (true, vertices_76), (true, vertices_524), (true, vertices_56), (true, vertices_88), (true, vertices_104), (true, vertices_168), (true, vertices_296), (true, vertices_552), (true, vertices_392), (true, vertices_776), (true, vertices_112), (true, vertices_176), (true, vertices_416), (true, vertices_896)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 20 16 24 25 26 27 28 29 30
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_647) then 17 else
  if p.val = (false, vertices_403) then 21 else
  if p.val = (false, vertices_355) then 22 else
  if p.val = (false, vertices_611) then 23 else
  if p.val = (false, vertices_157) then 18 else
  if p.val = (false, vertices_597) then 19 else
  if p.val = (false, vertices_337) then 0 else
  if p.val = (true, vertices_770) then 1 else
  if p.val = (true, vertices_76) then 2 else
  if p.val = (true, vertices_524) then 3 else
  if p.val = (true, vertices_56) then 4 else
  if p.val = (true, vertices_88) then 5 else
  if p.val = (true, vertices_104) then 6 else
  if p.val = (true, vertices_168) then 7 else
  if p.val = (true, vertices_296) then 8 else
  if p.val = (true, vertices_552) then 9 else
  if p.val = (true, vertices_392) then 10 else
  if p.val = (true, vertices_776) then 11 else
  if p.val = (true, vertices_112) then 12 else
  if p.val = (true, vertices_176) then 13 else
  if p.val = (true, vertices_416) then 14 else
  if p.val = (true, vertices_896) then 15 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_337), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_770), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_76), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_524), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_56), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_88), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_104), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_168), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_296), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_552), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_392), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_776), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_112), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_176), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_416), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_896), by decide +kernel⟩
  | 16 => Sum.inl 1
  | 17 => Sum.inr ⟨(false, vertices_647), by decide +kernel⟩
  | 18 => Sum.inr ⟨(false, vertices_157), by decide +kernel⟩
  | 19 => Sum.inr ⟨(false, vertices_597), by decide +kernel⟩
  | 20 => Sum.inl 0
  | 21 => Sum.inr ⟨(false, vertices_403), by decide +kernel⟩
  | 22 => Sum.inr ⟨(false, vertices_355), by decide +kernel⟩
  | 23 => Sum.inr ⟨(false, vertices_611), by decide +kernel⟩
  | 24 => Sum.inl 2
  | 25 => Sum.inl 3
  | 26 => Sum.inl 4
  | 27 => Sum.inl 5
  | 28 => Sum.inl 6
  | 29 => Sum.inl 7
  | 30 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 2 4 7 8 810 290 1
cert_row_4 1 3 4 5 6 7 496 112 3
cert_row_4 2 1 2 4 5 8 620 76 2
cert_row_4 3 1 2 6 7 8 908 140 3
cert_rows
cert_pivot_2 0 3 4 1
cert_heightProof 4
cert_coverFacet 0 810
cert_cover_5 0 0 0 2 4 7 290 810 1
cert_coverFacet 1 898
cert_cover_2 1 6 0 7 8 386 898 3
cert_coverFacet 2 92
cert_cover_2 2 2 1 3 5 28 92 3
cert_coverFacet 3 620
cert_cover_5 3 2 1 2 4 5 76 620 2
cert_coverFacet 4 908
cert_cover_5 4 3 1 2 6 7 140 908 3
cert_coverFacet 5 120
cert_cover_2 5 3 2 4 5 56 120 3
cert_coverFacet 6 184
cert_cover_2 6 3 2 4 6 56 184 3
cert_coverFacet 7 424
cert_cover_2 7 4 2 6 7 168 424 3
cert_coverFacet 8 496
cert_cover_5 8 1 3 4 5 6 112 496 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0389

end
end BundlePart13

section BundlePart14
/- Source: ProjectionCertificates/R_m16e10q1_0390.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0390

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [803, 93, 565, 581, 185, 297, 841, 454, 234, 362, 690, 898, 212, 916, 836, 216, 21, 69, 517, 25, 41, 73, 265, 49, 289, 545, 577, 769, 106, 162, 290, 546, 194, 322, 386, 642, 770, 84, 148, 532, 196, 324, 580, 388, 772, 88, 152, 168, 296, 200, 328, 176, 560, 208, 656, 832, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_803, vertices_93, vertices_565, vertices_581, vertices_185, vertices_297, vertices_841, vertices_454, vertices_234, vertices_362, vertices_690, vertices_898, vertices_212, vertices_916, vertices_836, vertices_216] (by decide +kernel)
  polygons := literalFinset [vertices_21, vertices_69, vertices_517, vertices_25, vertices_41, vertices_73, vertices_265, vertices_49, vertices_289, vertices_545, vertices_577, vertices_769, vertices_106, vertices_162, vertices_290, vertices_546, vertices_194, vertices_322, vertices_386, vertices_642, vertices_770, vertices_84, vertices_148, vertices_532, vertices_196, vertices_324, vertices_580, vertices_388, vertices_772, vertices_88, vertices_152, vertices_168, vertices_296, vertices_200, vertices_328, vertices_176, vertices_560, vertices_208, vertices_656, vertices_832, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_803), (false, vertices_93), (false, vertices_565), (false, vertices_581), (false, vertices_185), (false, vertices_297), (false, vertices_841), (true, vertices_106), (true, vertices_162), (true, vertices_194), (true, vertices_322), (true, vertices_386), (true, vertices_642), (true, vertices_148), (true, vertices_196), (true, vertices_324), (true, vertices_388), (true, vertices_772), (true, vertices_200), (true, vertices_208), (true, vertices_656), (true, vertices_896)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 16 19 22 25 26 27 28 29 30
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_803) then 17 else
  if p.val = (false, vertices_93) then 20 else
  if p.val = (false, vertices_565) then 21 else
  if p.val = (false, vertices_581) then 0 else
  if p.val = (false, vertices_185) then 23 else
  if p.val = (false, vertices_297) then 1 else
  if p.val = (false, vertices_841) then 24 else
  if p.val = (true, vertices_106) then 18 else
  if p.val = (true, vertices_162) then 2 else
  if p.val = (true, vertices_194) then 3 else
  if p.val = (true, vertices_322) then 4 else
  if p.val = (true, vertices_386) then 5 else
  if p.val = (true, vertices_642) then 6 else
  if p.val = (true, vertices_148) then 7 else
  if p.val = (true, vertices_196) then 8 else
  if p.val = (true, vertices_324) then 9 else
  if p.val = (true, vertices_388) then 10 else
  if p.val = (true, vertices_772) then 11 else
  if p.val = (true, vertices_200) then 12 else
  if p.val = (true, vertices_208) then 13 else
  if p.val = (true, vertices_656) then 14 else
  if p.val = (true, vertices_896) then 15 else
  0
cert_priority
cert_nodeAtPriority_39 0 581 1 297 162 194 322 386 642 148 196 324 388 772 200 208 656 896 803 106 93 565 185 841
cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 2 4 5 106
cert_row_4 1 0 1 5 6 7 454 194 1
cert_row_4 2 0 3 4 6 8 690 162 1
cert_row_4 3 1 3 6 7 8 916 148 3
cert_rows
cert_pivot_2 2 5 0 1
cert_heightProof 4
cert_coverFacet 0 454
cert_cover_5 0 1 0 1 5 6 194 454 1
cert_coverFacet 1 234
cert_cover_5 1 0 0 2 4 6 106 234 3
cert_coverFacet 2 362
cert_cover_5 2 0 0 2 4 7 106 362 3
cert_coverFacet 3 690
cert_cover_5 3 2 0 3 4 6 162 690 1
cert_coverFacet 4 898
cert_cover_2 4 6 0 7 8 386 898 3
cert_coverFacet 5 212
cert_cover_2 5 3 1 5 6 84 212 3
cert_coverFacet 6 916
cert_cover_5 6 3 1 3 6 7 148 916 3
cert_coverFacet 7 836
cert_cover_2 7 5 1 7 8 324 836 3
cert_coverFacet 8 216
cert_cover_2 8 3 2 5 6 88 216 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0390

end
end BundlePart14

section BundlePart15
/- Source: ProjectionCertificates/R_m16e10q1_0391.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0391

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [779, 653, 229, 805, 313, 169, 838, 602, 282, 434, 210, 482, 724, 356, 184, 664, 37, 133, 517, 41, 137, 265, 521, 161, 289, 769, 26, 266, 522, 82, 146, 274, 418, 194, 322, 578, 770, 100, 292, 196, 324, 580, 644, 772, 56, 152, 280, 536, 168, 648, 176, 304, 208, 592, 656, 224, 352]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_779, vertices_653, vertices_229, vertices_805, vertices_313, vertices_169, vertices_838, vertices_602, vertices_282, vertices_434, vertices_210, vertices_482, vertices_724, vertices_356, vertices_184, vertices_664] (by decide +kernel)
  polygons := literalFinset [vertices_37, vertices_133, vertices_517, vertices_41, vertices_137, vertices_265, vertices_521, vertices_161, vertices_289, vertices_769, vertices_26, vertices_266, vertices_522, vertices_82, vertices_146, vertices_274, vertices_418, vertices_194, vertices_322, vertices_578, vertices_770, vertices_100, vertices_292, vertices_196, vertices_324, vertices_580, vertices_644, vertices_772, vertices_56, vertices_152, vertices_280, vertices_536, vertices_168, vertices_648, vertices_176, vertices_304, vertices_208, vertices_592, vertices_656, vertices_224, vertices_352] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_779), (false, vertices_653), (false, vertices_229), (false, vertices_805), (false, vertices_313), (false, vertices_169), (true, vertices_26), (true, vertices_82), (true, vertices_146), (true, vertices_274), (true, vertices_418), (true, vertices_194), (true, vertices_322), (true, vertices_578), (true, vertices_324), (true, vertices_580), (true, vertices_152), (true, vertices_536), (true, vertices_176), (true, vertices_208), (true, vertices_592), (true, vertices_656), (true, vertices_352)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 17 20 24 26 27 28 29 30 31
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_779) then 18 else
  if p.val = (false, vertices_653) then 21 else
  if p.val = (false, vertices_229) then 22 else
  if p.val = (false, vertices_805) then 23 else
  if p.val = (false, vertices_313) then 25 else
  if p.val = (false, vertices_169) then 0 else
  if p.val = (true, vertices_26) then 1 else
  if p.val = (true, vertices_82) then 2 else
  if p.val = (true, vertices_146) then 3 else
  if p.val = (true, vertices_274) then 4 else
  if p.val = (true, vertices_418) then 19 else
  if p.val = (true, vertices_194) then 5 else
  if p.val = (true, vertices_322) then 6 else
  if p.val = (true, vertices_578) then 7 else
  if p.val = (true, vertices_324) then 8 else
  if p.val = (true, vertices_580) then 9 else
  if p.val = (true, vertices_152) then 10 else
  if p.val = (true, vertices_536) then 11 else
  if p.val = (true, vertices_176) then 12 else
  if p.val = (true, vertices_208) then 13 else
  if p.val = (true, vertices_592) then 14 else
  if p.val = (true, vertices_656) then 15 else
  if p.val = (true, vertices_352) then 16 else
  0
cert_priority
cert_nodeAtPriority_63 169 26 82 146 274 194 322 578 324 580 152 536 176 208 592 656 352 779 418 653 229 805 313
cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 4 6 7 418
cert_row_4 1 0 1 5 7 8 838 322 1
cert_row_4 2 0 2 3 5 8 602 26 3
cert_row_4 3 1 3 5 6 8 724 196 1
cert_rows
cert_pivot_2 4 7 0 1
cert_heightProof 4
cert_coverFacet 0 838
cert_cover_5 0 1 0 1 5 7 322 838 1
cert_coverFacet 1 602
cert_cover_5 1 2 0 2 3 5 26 602 3
cert_coverFacet 2 282
cert_cover_2 2 2 0 3 7 26 282 3
cert_coverFacet 3 434
cert_cover_5 3 0 0 3 4 6 146 434 2
cert_coverFacet 4 210
cert_cover_2 4 3 0 5 6 82 210 3
cert_coverFacet 5 482
cert_cover_5 5 0 0 4 5 6 418 482 2
cert_coverFacet 6 724
cert_cover_5 6 3 1 3 5 6 196 724 1
cert_coverFacet 7 356
cert_cover_2 7 4 1 5 7 100 356 3
cert_coverFacet 8 184
cert_cover_2 8 3 2 4 6 56 184 3
cert_coverFacet 9 664
cert_cover_2 9 3 2 6 8 152 664 3
cert_coveringFacets_5
cert_coveringProof
cert_certificate 4 10
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0391

end
end BundlePart15

section BundlePart16
/- Source: ProjectionCertificates/R_m16e10q1_0392.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0392

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [787, 309, 661, 165, 681, 865, 342, 666, 618, 202, 210, 834, 428, 460, 212, 360, 21, 37, 133, 273, 529, 161, 289, 545, 641, 769, 74, 138, 522, 82, 146, 274, 530, 194, 322, 578, 770, 396, 84, 148, 276, 164, 292, 196, 324, 104, 168, 296, 552, 200, 328, 648, 208, 656, 352, 608, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_787, vertices_309, vertices_661, vertices_165, vertices_681, vertices_865, vertices_342, vertices_666, vertices_618, vertices_202, vertices_210, vertices_834, vertices_428, vertices_460, vertices_212, vertices_360] (by decide +kernel)
  polygons := literalFinset [vertices_21, vertices_37, vertices_133, vertices_273, vertices_529, vertices_161, vertices_289, vertices_545, vertices_641, vertices_769, vertices_74, vertices_138, vertices_522, vertices_82, vertices_146, vertices_274, vertices_530, vertices_194, vertices_322, vertices_578, vertices_770, vertices_396, vertices_84, vertices_148, vertices_276, vertices_164, vertices_292, vertices_196, vertices_324, vertices_104, vertices_168, vertices_296, vertices_552, vertices_200, vertices_328, vertices_648, vertices_208, vertices_656, vertices_352, vertices_608, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_787), (false, vertices_309), (false, vertices_661), (false, vertices_165), (false, vertices_681), (false, vertices_865), (true, vertices_74), (true, vertices_138), (true, vertices_522), (true, vertices_82), (true, vertices_146), (true, vertices_194), (true, vertices_322), (true, vertices_578), (true, vertices_396), (true, vertices_84), (true, vertices_196), (true, vertices_324), (true, vertices_104), (true, vertices_296), (true, vertices_200), (true, vertices_328), (true, vertices_208)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 17 19 23 25 26 28 29 30 31
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_787) then 18 else
  if p.val = (false, vertices_309) then 20 else
  if p.val = (false, vertices_661) then 21 else
  if p.val = (false, vertices_165) then 0 else
  if p.val = (false, vertices_681) then 24 else
  if p.val = (false, vertices_865) then 27 else
  if p.val = (true, vertices_74) then 1 else
  if p.val = (true, vertices_138) then 2 else
  if p.val = (true, vertices_522) then 3 else
  if p.val = (true, vertices_82) then 4 else
  if p.val = (true, vertices_146) then 5 else
  if p.val = (true, vertices_194) then 6 else
  if p.val = (true, vertices_322) then 7 else
  if p.val = (true, vertices_578) then 8 else
  if p.val = (true, vertices_396) then 22 else
  if p.val = (true, vertices_84) then 9 else
  if p.val = (true, vertices_196) then 10 else
  if p.val = (true, vertices_324) then 11 else
  if p.val = (true, vertices_104) then 12 else
  if p.val = (true, vertices_296) then 13 else
  if p.val = (true, vertices_200) then 14 else
  if p.val = (true, vertices_328) then 15 else
  if p.val = (true, vertices_208) then 16 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_165), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_74), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_138), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_522), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_82), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_146), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_194), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_322), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_578), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_84), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_196), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_324), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_104), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_296), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_200), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_328), by decide +kernel⟩
  | 16 => Sum.inr ⟨(true, vertices_208), by decide +kernel⟩
  | 17 => Sum.inl 0
  | 18 => Sum.inr ⟨(false, vertices_787), by decide +kernel⟩
  | 19 => Sum.inl 1
  | 20 => Sum.inr ⟨(false, vertices_309), by decide +kernel⟩
  | 21 => Sum.inr ⟨(false, vertices_661), by decide +kernel⟩
  | 22 => Sum.inr ⟨(true, vertices_396), by decide +kernel⟩
  | 23 => Sum.inl 2
  | 24 => Sum.inr ⟨(false, vertices_681), by decide +kernel⟩
  | 25 => Sum.inl 3
  | 26 => Sum.inl 4
  | 27 => Sum.inr ⟨(false, vertices_865), by decide +kernel⟩
  | 28 => Sum.inl 5
  | 29 => Sum.inl 6
  | 30 => Sum.inl 7
  | 31 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 2 4 5 8 618 74 2
cert_row_4 1 0 1 3 5 7 342 82 1
cert_row_2 2 1 2 6 7 396
cert_row_4 3 0 2 3 6 8 666 138 2
cert_rows
cert_pivot_2 4 5 1 0
cert_heightProof 4
cert_coverFacet 0 342
cert_cover_5 0 1 0 1 3 5 82 342 1
cert_coverFacet 1 666
cert_cover_5 1 3 0 2 3 6 138 666 2
cert_coverFacet 2 618
cert_cover_5 2 0 0 2 4 5 74 618 2
cert_coverFacet 3 202
cert_cover_2 3 2 0 5 6 74 202 3
cert_coverFacet 4 210
cert_cover_2 4 3 0 5 6 82 210 3
cert_coverFacet 5 834
cert_cover_2 5 5 0 7 8 322 834 3
cert_coverFacet 6 428
cert_cover_5 6 2 1 2 4 6 396 428 2
cert_coverFacet 7 460
cert_cover_5 7 2 1 2 5 6 396 460 2
cert_coverFacet 8 212
cert_cover_2 8 3 1 5 6 84 212 3
cert_coverFacet 9 360
cert_cover_2 9 4 2 5 7 104 360 3
cert_coveringFacets_5
cert_coveringProof
cert_certificate 4 10
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0392

end
end BundlePart16

section BundlePart17
/- Source: ProjectionCertificates/R_m16e10q1_0393.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0393

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [647, 779, 179, 291, 285, 589, 149, 305, 482, 898, 92, 628, 692, 376, 968, 736, 35, 131, 259, 515, 13, 21, 133, 517, 265, 521, 49, 145, 273, 289, 162, 290, 386, 642, 770, 28, 76, 564, 84, 148, 580, 644, 88, 280, 328, 584, 776, 112, 176, 304, 224, 352, 608, 672, 448, 704, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_647, vertices_779, vertices_179, vertices_291, vertices_285, vertices_589, vertices_149, vertices_305, vertices_482, vertices_898, vertices_92, vertices_628, vertices_692, vertices_376, vertices_968, vertices_736] (by decide +kernel)
  polygons := literalFinset [vertices_35, vertices_131, vertices_259, vertices_515, vertices_13, vertices_21, vertices_133, vertices_517, vertices_265, vertices_521, vertices_49, vertices_145, vertices_273, vertices_289, vertices_162, vertices_290, vertices_386, vertices_642, vertices_770, vertices_28, vertices_76, vertices_564, vertices_84, vertices_148, vertices_580, vertices_644, vertices_88, vertices_280, vertices_328, vertices_584, vertices_776, vertices_112, vertices_176, vertices_304, vertices_224, vertices_352, vertices_608, vertices_672, vertices_448, vertices_704, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_647), (false, vertices_779), (false, vertices_179), (false, vertices_291), (false, vertices_285), (false, vertices_589), (false, vertices_149), (false, vertices_305), (true, vertices_386), (true, vertices_564), (true, vertices_84), (true, vertices_88), (true, vertices_328), (true, vertices_112), (true, vertices_224), (true, vertices_352), (true, vertices_608), (true, vertices_672), (true, vertices_448), (true, vertices_704), (true, vertices_896)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 19 23 24 25 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_647) then 16 else
  if p.val = (false, vertices_779) then 17 else
  if p.val = (false, vertices_179) then 18 else
  if p.val = (false, vertices_291) then 0 else
  if p.val = (false, vertices_285) then 20 else
  if p.val = (false, vertices_589) then 21 else
  if p.val = (false, vertices_149) then 1 else
  if p.val = (false, vertices_305) then 2 else
  if p.val = (true, vertices_386) then 3 else
  if p.val = (true, vertices_564) then 22 else
  if p.val = (true, vertices_84) then 4 else
  if p.val = (true, vertices_88) then 5 else
  if p.val = (true, vertices_328) then 6 else
  if p.val = (true, vertices_112) then 7 else
  if p.val = (true, vertices_224) then 8 else
  if p.val = (true, vertices_352) then 9 else
  if p.val = (true, vertices_608) then 10 else
  if p.val = (true, vertices_672) then 11 else
  if p.val = (true, vertices_448) then 12 else
  if p.val = (true, vertices_704) then 13 else
  if p.val = (true, vertices_896) then 14 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_291), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_149), by decide +kernel⟩
  | 2 => Sum.inr ⟨(false, vertices_305), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_386), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_84), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_88), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_328), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_112), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_224), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_352), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_608), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_672), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_448), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_704), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_896), by decide +kernel⟩
  | 15 => Sum.inl 0
  | 16 => Sum.inr ⟨(false, vertices_647), by decide +kernel⟩
  | 17 => Sum.inr ⟨(false, vertices_779), by decide +kernel⟩
  | 18 => Sum.inr ⟨(false, vertices_179), by decide +kernel⟩
  | 19 => Sum.inl 1
  | 20 => Sum.inr ⟨(false, vertices_285), by decide +kernel⟩
  | 21 => Sum.inr ⟨(false, vertices_589), by decide +kernel⟩
  | 22 => Sum.inr ⟨(true, vertices_564), by decide +kernel⟩
  | 23 => Sum.inl 2
  | 24 => Sum.inl 3
  | 25 => Sum.inl 4
  | 26 => Sum.inl 5
  | 27 => Sum.inl 6
  | 28 => Sum.inl 7
  | 29 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 1 3 4 8 564
cert_row_4 1 0 4 5 6 7 482 162 2
cert_row_4 2 2 3 4 5 7 376 88 2
cert_row_4 3 2 5 6 7 8 968 328 2
cert_rows
cert_pivot_2 1 0 3 2
cert_heightProof 4
cert_coverFacet 0 482
cert_cover_5 0 1 0 4 5 6 162 482 2
cert_coverFacet 1 898
cert_cover_2 1 6 0 7 8 386 898 3
cert_coverFacet 2 92
cert_cover_2 2 2 1 3 5 28 92 3
cert_coverFacet 3 628
cert_cover_5 3 0 1 3 4 5 564 628 3
cert_coverFacet 4 692
cert_cover_5 4 0 1 3 4 6 564 692 3
cert_coverFacet 5 376
cert_cover_5 5 2 2 3 4 5 88 376 2
cert_coverFacet 6 968
cert_cover_5 6 3 2 5 6 7 328 968 2
cert_coverFacet 7 736
cert_cover_2 7 5 4 6 8 224 736 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0393

end
end BundlePart17

section BundlePart18
/- Source: ProjectionCertificates/R_m16e10q1_0394.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0394

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [647, 203, 331, 787, 565, 341, 197, 426, 898, 716, 116, 612, 376, 616, 680, 944, 75, 131, 259, 515, 21, 69, 133, 517, 273, 529, 193, 321, 138, 266, 386, 642, 770, 52, 84, 100, 548, 196, 580, 644, 104, 168, 296, 552, 200, 328, 584, 648, 112, 304, 560, 336, 784, 608, 416, 672, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_647, vertices_203, vertices_331, vertices_787, vertices_565, vertices_341, vertices_197, vertices_426, vertices_898, vertices_716, vertices_116, vertices_612, vertices_376, vertices_616, vertices_680, vertices_944] (by decide +kernel)
  polygons := literalFinset [vertices_75, vertices_131, vertices_259, vertices_515, vertices_21, vertices_69, vertices_133, vertices_517, vertices_273, vertices_529, vertices_193, vertices_321, vertices_138, vertices_266, vertices_386, vertices_642, vertices_770, vertices_52, vertices_84, vertices_100, vertices_548, vertices_196, vertices_580, vertices_644, vertices_104, vertices_168, vertices_296, vertices_552, vertices_200, vertices_328, vertices_584, vertices_648, vertices_112, vertices_304, vertices_560, vertices_336, vertices_784, vertices_608, vertices_416, vertices_672, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_647), (false, vertices_203), (false, vertices_331), (false, vertices_787), (false, vertices_565), (false, vertices_341), (false, vertices_197), (true, vertices_386), (true, vertices_100), (true, vertices_580), (true, vertices_104), (true, vertices_168), (true, vertices_296), (true, vertices_552), (true, vertices_584), (true, vertices_648), (true, vertices_112), (true, vertices_304), (true, vertices_608), (true, vertices_416), (true, vertices_672), (true, vertices_896)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 20 16 24 25 26 27 28 29 30
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_647) then 17 else
  if p.val = (false, vertices_203) then 21 else
  if p.val = (false, vertices_331) then 22 else
  if p.val = (false, vertices_787) then 23 else
  if p.val = (false, vertices_565) then 18 else
  if p.val = (false, vertices_341) then 19 else
  if p.val = (false, vertices_197) then 0 else
  if p.val = (true, vertices_386) then 1 else
  if p.val = (true, vertices_100) then 2 else
  if p.val = (true, vertices_580) then 3 else
  if p.val = (true, vertices_104) then 4 else
  if p.val = (true, vertices_168) then 5 else
  if p.val = (true, vertices_296) then 6 else
  if p.val = (true, vertices_552) then 7 else
  if p.val = (true, vertices_584) then 8 else
  if p.val = (true, vertices_648) then 9 else
  if p.val = (true, vertices_112) then 10 else
  if p.val = (true, vertices_304) then 11 else
  if p.val = (true, vertices_608) then 12 else
  if p.val = (true, vertices_416) then 13 else
  if p.val = (true, vertices_672) then 14 else
  if p.val = (true, vertices_896) then 15 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_197), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_386), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_100), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_580), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_104), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_168), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_296), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_552), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_584), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_648), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_112), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_304), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_608), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_416), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_672), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_896), by decide +kernel⟩
  | 16 => Sum.inl 1
  | 17 => Sum.inr ⟨(false, vertices_647), by decide +kernel⟩
  | 18 => Sum.inr ⟨(false, vertices_565), by decide +kernel⟩
  | 19 => Sum.inr ⟨(false, vertices_341), by decide +kernel⟩
  | 20 => Sum.inl 0
  | 21 => Sum.inr ⟨(false, vertices_203), by decide +kernel⟩
  | 22 => Sum.inr ⟨(false, vertices_331), by decide +kernel⟩
  | 23 => Sum.inr ⟨(false, vertices_787), by decide +kernel⟩
  | 24 => Sum.inl 2
  | 25 => Sum.inl 3
  | 26 => Sum.inl 4
  | 27 => Sum.inl 5
  | 28 => Sum.inl 6
  | 29 => Sum.inl 7
  | 30 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 2 4 6 7 426 138 2
cert_row_4 1 1 2 5 6 8 716 196 1
cert_row_4 2 2 3 4 5 7 376 104 1
cert_row_4 3 3 4 6 7 8 944 304 2
cert_rows
cert_pivot_2 0 1 2 3
cert_heightProof 4
cert_coverFacet 0 426
cert_cover_5 0 0 0 2 4 6 138 426 2
cert_coverFacet 1 898
cert_cover_2 1 6 0 7 8 386 898 3
cert_coverFacet 2 716
cert_cover_5 2 1 1 2 5 6 196 716 1
cert_coverFacet 3 116
cert_cover_2 3 3 1 4 5 52 116 3
cert_coverFacet 4 612
cert_cover_2 4 4 1 5 8 100 612 3
cert_coverFacet 5 376
cert_cover_5 5 2 2 3 4 5 104 376 1
cert_coverFacet 6 616
cert_cover_2 6 4 2 5 8 104 616 3
cert_coverFacet 7 680
cert_cover_2 7 4 2 6 8 168 680 3
cert_coverFacet 8 944
cert_cover_5 8 3 3 4 6 7 304 944 2
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0394

end
end BundlePart18

section BundlePart19
/- Source: ProjectionCertificates/R_m16e10q1_0395.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0395

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [835, 45, 589, 357, 569, 929, 454, 218, 602, 690, 898, 316, 156, 204, 404, 432, 13, 37, 69, 41, 521, 289, 545, 321, 577, 769, 90, 146, 530, 194, 322, 578, 386, 642, 770, 28, 44, 76, 140, 148, 276, 292, 196, 324, 388, 56, 152, 536, 200, 584, 176, 304, 560, 400, 416, 672, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_835, vertices_45, vertices_589, vertices_357, vertices_569, vertices_929, vertices_454, vertices_218, vertices_602, vertices_690, vertices_898, vertices_316, vertices_156, vertices_204, vertices_404, vertices_432] (by decide +kernel)
  polygons := literalFinset [vertices_13, vertices_37, vertices_69, vertices_41, vertices_521, vertices_289, vertices_545, vertices_321, vertices_577, vertices_769, vertices_90, vertices_146, vertices_530, vertices_194, vertices_322, vertices_578, vertices_386, vertices_642, vertices_770, vertices_28, vertices_44, vertices_76, vertices_140, vertices_148, vertices_276, vertices_292, vertices_196, vertices_324, vertices_388, vertices_56, vertices_152, vertices_536, vertices_200, vertices_584, vertices_176, vertices_304, vertices_560, vertices_400, vertices_416, vertices_672, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_835), (false, vertices_45), (false, vertices_589), (false, vertices_357), (false, vertices_569), (false, vertices_929), (true, vertices_90), (true, vertices_146), (true, vertices_530), (true, vertices_194), (true, vertices_386), (true, vertices_642), (true, vertices_28), (true, vertices_140), (true, vertices_148), (true, vertices_276), (true, vertices_196), (true, vertices_388), (true, vertices_152), (true, vertices_200), (true, vertices_176), (true, vertices_304), (true, vertices_400)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 17 20 23 25 26 28 29 30 31
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_835) then 18 else
  if p.val = (false, vertices_45) then 0 else
  if p.val = (false, vertices_589) then 21 else
  if p.val = (false, vertices_357) then 22 else
  if p.val = (false, vertices_569) then 24 else
  if p.val = (false, vertices_929) then 27 else
  if p.val = (true, vertices_90) then 19 else
  if p.val = (true, vertices_146) then 1 else
  if p.val = (true, vertices_530) then 2 else
  if p.val = (true, vertices_194) then 3 else
  if p.val = (true, vertices_386) then 4 else
  if p.val = (true, vertices_642) then 5 else
  if p.val = (true, vertices_28) then 6 else
  if p.val = (true, vertices_140) then 7 else
  if p.val = (true, vertices_148) then 8 else
  if p.val = (true, vertices_276) then 9 else
  if p.val = (true, vertices_196) then 10 else
  if p.val = (true, vertices_388) then 11 else
  if p.val = (true, vertices_152) then 12 else
  if p.val = (true, vertices_200) then 13 else
  if p.val = (true, vertices_176) then 14 else
  if p.val = (true, vertices_304) then 15 else
  if p.val = (true, vertices_400) then 16 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_45), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_146), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_530), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_194), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_386), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_642), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_28), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_140), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_148), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_276), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_196), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_388), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_152), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_200), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_176), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_304), by decide +kernel⟩
  | 16 => Sum.inr ⟨(true, vertices_400), by decide +kernel⟩
  | 17 => Sum.inl 0
  | 18 => Sum.inr ⟨(false, vertices_835), by decide +kernel⟩
  | 19 => Sum.inr ⟨(true, vertices_90), by decide +kernel⟩
  | 20 => Sum.inl 1
  | 21 => Sum.inr ⟨(false, vertices_589), by decide +kernel⟩
  | 22 => Sum.inr ⟨(false, vertices_357), by decide +kernel⟩
  | 23 => Sum.inl 2
  | 24 => Sum.inr ⟨(false, vertices_569), by decide +kernel⟩
  | 25 => Sum.inl 3
  | 26 => Sum.inl 4
  | 27 => Sum.inr ⟨(false, vertices_929), by decide +kernel⟩
  | 28 => Sum.inl 5
  | 29 => Sum.inl 6
  | 30 => Sum.inl 7
  | 31 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 3 4 6 8 690 146 2
cert_row_4 1 0 1 5 6 7 454 194 1
cert_row_2 2 0 2 3 5 90
cert_row_4 3 1 2 3 4 7 316 28 3
cert_rows
cert_pivot_2 8 6 0 1
cert_heightProof 4
cert_coverFacet 0 454
cert_cover_5 0 1 0 1 5 6 194 454 1
cert_coverFacet 1 218
cert_cover_5 1 2 0 2 3 6 90 218 3
cert_coverFacet 2 602
cert_cover_5 2 2 0 2 3 8 90 602 3
cert_coverFacet 3 690
cert_cover_5 3 0 0 3 4 6 146 690 2
cert_coverFacet 4 898
cert_cover_2 4 6 0 7 8 386 898 3
cert_coverFacet 5 316
cert_cover_5 5 3 1 2 3 4 28 316 3
cert_coverFacet 6 156
cert_cover_2 6 2 1 3 6 28 156 3
cert_coverFacet 7 204
cert_cover_2 7 2 1 5 6 76 204 3
cert_coverFacet 8 404
cert_cover_2 8 3 1 6 7 148 404 3
cert_coverFacet 9 432
cert_cover_2 9 4 3 6 7 176 432 3
cert_coveringFacets_5
cert_coveringProof
cert_certificate 4 10
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0395

end
end BundlePart19

section BundlePart20
/- Source: ProjectionCertificates/R_m16e10q1_0396.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0396

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [675, 333, 565, 277, 709, 241, 337, 782, 170, 298, 714, 818, 588, 788, 440, 472, 21, 69, 261, 517, 49, 81, 273, 161, 545, 193, 321, 641, 42, 138, 266, 522, 162, 290, 546, 642, 770, 76, 268, 524, 276, 532, 580, 772, 408, 168, 296, 200, 328, 584, 176, 304, 560, 208, 336, 784, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_675, vertices_333, vertices_565, vertices_277, vertices_709, vertices_241, vertices_337, vertices_782, vertices_170, vertices_298, vertices_714, vertices_818, vertices_588, vertices_788, vertices_440, vertices_472] (by decide +kernel)
  polygons := literalFinset [vertices_21, vertices_69, vertices_261, vertices_517, vertices_49, vertices_81, vertices_273, vertices_161, vertices_545, vertices_193, vertices_321, vertices_641, vertices_42, vertices_138, vertices_266, vertices_522, vertices_162, vertices_290, vertices_546, vertices_642, vertices_770, vertices_76, vertices_268, vertices_524, vertices_276, vertices_532, vertices_580, vertices_772, vertices_408, vertices_168, vertices_296, vertices_200, vertices_328, vertices_584, vertices_176, vertices_304, vertices_560, vertices_208, vertices_336, vertices_784, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_675), (false, vertices_333), (false, vertices_565), (false, vertices_277), (false, vertices_709), (false, vertices_241), (false, vertices_337), (true, vertices_42), (true, vertices_138), (true, vertices_266), (true, vertices_522), (true, vertices_290), (true, vertices_770), (true, vertices_524), (true, vertices_772), (true, vertices_408), (true, vertices_168), (true, vertices_296), (true, vertices_200), (true, vertices_584), (true, vertices_304), (true, vertices_784)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 16 18 22 24 26 27 28 29 30
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_675) then 17 else
  if p.val = (false, vertices_333) then 19 else
  if p.val = (false, vertices_565) then 20 else
  if p.val = (false, vertices_277) then 0 else
  if p.val = (false, vertices_709) then 21 else
  if p.val = (false, vertices_241) then 25 else
  if p.val = (false, vertices_337) then 1 else
  if p.val = (true, vertices_42) then 2 else
  if p.val = (true, vertices_138) then 3 else
  if p.val = (true, vertices_266) then 4 else
  if p.val = (true, vertices_522) then 5 else
  if p.val = (true, vertices_290) then 6 else
  if p.val = (true, vertices_770) then 7 else
  if p.val = (true, vertices_524) then 8 else
  if p.val = (true, vertices_772) then 9 else
  if p.val = (true, vertices_408) then 23 else
  if p.val = (true, vertices_168) then 10 else
  if p.val = (true, vertices_296) then 11 else
  if p.val = (true, vertices_200) then 12 else
  if p.val = (true, vertices_584) then 13 else
  if p.val = (true, vertices_304) then 14 else
  if p.val = (true, vertices_784) then 15 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_277), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_337), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_42), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_138), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_266), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_522), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_290), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_770), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_524), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_772), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_168), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_296), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_200), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_584), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_304), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_784), by decide +kernel⟩
  | 16 => Sum.inl 0
  | 17 => Sum.inr ⟨(false, vertices_675), by decide +kernel⟩
  | 18 => Sum.inl 1
  | 19 => Sum.inr ⟨(false, vertices_333), by decide +kernel⟩
  | 20 => Sum.inr ⟨(false, vertices_565), by decide +kernel⟩
  | 21 => Sum.inr ⟨(false, vertices_709), by decide +kernel⟩
  | 22 => Sum.inl 2
  | 23 => Sum.inr ⟨(true, vertices_408), by decide +kernel⟩
  | 24 => Sum.inl 3
  | 25 => Sum.inr ⟨(false, vertices_241), by decide +kernel⟩
  | 26 => Sum.inl 4
  | 27 => Sum.inl 5
  | 28 => Sum.inl 6
  | 29 => Sum.inl 7
  | 30 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 2 7 8 782 266 1
cert_row_4 1 0 2 5 6 8 714 138 2
cert_row_2 2 2 3 6 7 408
cert_row_4 3 0 3 4 7 8 818 290 1
cert_rows
cert_pivot_2 1 5 2 0
cert_heightProof 4
cert_coverFacet 0 782
cert_cover_5 0 0 0 1 2 7 266 782 1
cert_coverFacet 1 170
cert_cover_2 1 2 0 4 6 42 170 3
cert_coverFacet 2 298
cert_cover_2 2 2 0 4 7 42 298 3
cert_coverFacet 3 714
cert_cover_5 3 1 0 2 5 6 138 714 2
cert_coverFacet 4 818
cert_cover_5 4 3 0 3 4 7 290 818 1
cert_coverFacet 5 588
cert_cover_2 5 2 1 5 8 76 588 3
cert_coverFacet 6 788
cert_cover_2 6 3 1 7 8 276 788 3
cert_coverFacet 7 440
cert_cover_5 7 2 2 3 4 6 408 440 2
cert_coverFacet 8 472
cert_cover_5 8 2 2 3 5 6 408 472 2
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0396

end
end BundlePart20

section BundlePart21
/- Source: ProjectionCertificates/R_m16e10q1_0397.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0397

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [339, 611, 899, 677, 425, 353, 598, 794, 156, 540, 908, 212, 228, 612, 248, 376, 67, 259, 515, 97, 161, 289, 545, 321, 385, 641, 82, 274, 530, 578, 770, 28, 140, 524, 84, 148, 532, 100, 164, 548, 196, 580, 644, 120, 152, 280, 536, 168, 296, 392, 776, 208, 336, 224, 352, 608, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_339, vertices_611, vertices_899, vertices_677, vertices_425, vertices_353, vertices_598, vertices_794, vertices_156, vertices_540, vertices_908, vertices_212, vertices_228, vertices_612, vertices_248, vertices_376] (by decide +kernel)
  polygons := literalFinset [vertices_67, vertices_259, vertices_515, vertices_97, vertices_161, vertices_289, vertices_545, vertices_321, vertices_385, vertices_641, vertices_82, vertices_274, vertices_530, vertices_578, vertices_770, vertices_28, vertices_140, vertices_524, vertices_84, vertices_148, vertices_532, vertices_100, vertices_164, vertices_548, vertices_196, vertices_580, vertices_644, vertices_120, vertices_152, vertices_280, vertices_536, vertices_168, vertices_296, vertices_392, vertices_776, vertices_208, vertices_336, vertices_224, vertices_352, vertices_608, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_339), (false, vertices_611), (false, vertices_899), (false, vertices_677), (false, vertices_425), (false, vertices_353), (true, vertices_530), (true, vertices_28), (true, vertices_140), (true, vertices_524), (true, vertices_84), (true, vertices_148), (true, vertices_532), (true, vertices_100), (true, vertices_196), (true, vertices_580), (true, vertices_120), (true, vertices_152), (true, vertices_280), (true, vertices_536), (true, vertices_776), (true, vertices_208), (true, vertices_224)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 17 21 23 26 27 28 29 30 31
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_339) then 18 else
  if p.val = (false, vertices_611) then 19 else
  if p.val = (false, vertices_899) then 20 else
  if p.val = (false, vertices_677) then 22 else
  if p.val = (false, vertices_425) then 24 else
  if p.val = (false, vertices_353) then 0 else
  if p.val = (true, vertices_530) then 1 else
  if p.val = (true, vertices_28) then 2 else
  if p.val = (true, vertices_140) then 3 else
  if p.val = (true, vertices_524) then 4 else
  if p.val = (true, vertices_84) then 5 else
  if p.val = (true, vertices_148) then 6 else
  if p.val = (true, vertices_532) then 7 else
  if p.val = (true, vertices_100) then 8 else
  if p.val = (true, vertices_196) then 9 else
  if p.val = (true, vertices_580) then 10 else
  if p.val = (true, vertices_120) then 25 else
  if p.val = (true, vertices_152) then 11 else
  if p.val = (true, vertices_280) then 12 else
  if p.val = (true, vertices_536) then 13 else
  if p.val = (true, vertices_776) then 14 else
  if p.val = (true, vertices_208) then 15 else
  if p.val = (true, vertices_224) then 16 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_353), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_530), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_28), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_140), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_524), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_84), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_148), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_532), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_100), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_196), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_580), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_152), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_280), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_536), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_776), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_208), by decide +kernel⟩
  | 16 => Sum.inr ⟨(true, vertices_224), by decide +kernel⟩
  | 17 => Sum.inl 0
  | 18 => Sum.inr ⟨(false, vertices_339), by decide +kernel⟩
  | 19 => Sum.inr ⟨(false, vertices_611), by decide +kernel⟩
  | 20 => Sum.inr ⟨(false, vertices_899), by decide +kernel⟩
  | 21 => Sum.inl 1
  | 22 => Sum.inr ⟨(false, vertices_677), by decide +kernel⟩
  | 23 => Sum.inl 2
  | 24 => Sum.inr ⟨(false, vertices_425), by decide +kernel⟩
  | 25 => Sum.inr ⟨(true, vertices_120), by decide +kernel⟩
  | 26 => Sum.inl 3
  | 27 => Sum.inl 4
  | 28 => Sum.inl 5
  | 29 => Sum.inl 6
  | 30 => Sum.inl 7
  | 31 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 2 3 4 5 120
cert_row_4 1 0 1 3 5 8 598 82 1
cert_row_4 2 0 2 3 7 8 794 274 1
cert_row_4 3 1 2 6 7 8 908 140 3
cert_rows
cert_pivot_2 4 5 0 1
cert_heightProof 4
cert_coverFacet 0 598
cert_cover_5 0 1 0 1 3 5 82 598 1
cert_coverFacet 1 794
cert_cover_5 1 2 0 2 3 7 274 794 1
cert_coverFacet 2 156
cert_cover_2 2 2 1 3 6 28 156 3
cert_coverFacet 3 540
cert_cover_2 3 2 1 3 8 28 540 3
cert_coverFacet 4 908
cert_cover_5 4 3 1 2 6 7 140 908 3
cert_coverFacet 5 212
cert_cover_2 5 3 1 5 6 84 212 3
cert_coverFacet 6 228
cert_cover_2 6 4 1 5 6 100 228 3
cert_coverFacet 7 612
cert_cover_2 7 4 1 5 8 100 612 3
cert_coverFacet 8 248
cert_cover_5 8 0 2 3 4 6 120 248 3
cert_coverFacet 9 376
cert_cover_5 9 0 2 3 4 7 120 376 3
cert_coveringFacets_5
cert_coveringProof
cert_certificate 4 10
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0397

end
end BundlePart21

section BundlePart22
/- Source: ProjectionCertificates/R_m16e10q1_0398.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0398

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [779, 339, 707, 677, 233, 553, 329, 310, 534, 774, 594, 812, 180, 724, 440, 472, 67, 259, 515, 41, 73, 265, 521, 161, 545, 193, 321, 641, 22, 262, 518, 82, 274, 530, 578, 770, 52, 148, 532, 164, 292, 548, 644, 772, 408, 168, 296, 552, 200, 328, 776, 176, 304, 208, 336, 592, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_779, vertices_339, vertices_707, vertices_677, vertices_233, vertices_553, vertices_329, vertices_310, vertices_534, vertices_774, vertices_594, vertices_812, vertices_180, vertices_724, vertices_440, vertices_472] (by decide +kernel)
  polygons := literalFinset [vertices_67, vertices_259, vertices_515, vertices_41, vertices_73, vertices_265, vertices_521, vertices_161, vertices_545, vertices_193, vertices_321, vertices_641, vertices_22, vertices_262, vertices_518, vertices_82, vertices_274, vertices_530, vertices_578, vertices_770, vertices_52, vertices_148, vertices_532, vertices_164, vertices_292, vertices_548, vertices_644, vertices_772, vertices_408, vertices_168, vertices_296, vertices_552, vertices_200, vertices_328, vertices_776, vertices_176, vertices_304, vertices_208, vertices_336, vertices_592, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_779), (false, vertices_339), (false, vertices_707), (false, vertices_677), (false, vertices_233), (false, vertices_553), (false, vertices_329), (true, vertices_22), (true, vertices_262), (true, vertices_518), (true, vertices_530), (true, vertices_52), (true, vertices_148), (true, vertices_532), (true, vertices_292), (true, vertices_772), (true, vertices_408), (true, vertices_296), (true, vertices_176), (true, vertices_304), (true, vertices_208), (true, vertices_592)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 16 20 22 25 26 27 28 29 30
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_779) then 17 else
  if p.val = (false, vertices_339) then 18 else
  if p.val = (false, vertices_707) then 19 else
  if p.val = (false, vertices_677) then 21 else
  if p.val = (false, vertices_233) then 23 else
  if p.val = (false, vertices_553) then 0 else
  if p.val = (false, vertices_329) then 1 else
  if p.val = (true, vertices_22) then 2 else
  if p.val = (true, vertices_262) then 3 else
  if p.val = (true, vertices_518) then 4 else
  if p.val = (true, vertices_530) then 5 else
  if p.val = (true, vertices_52) then 6 else
  if p.val = (true, vertices_148) then 7 else
  if p.val = (true, vertices_532) then 8 else
  if p.val = (true, vertices_292) then 9 else
  if p.val = (true, vertices_772) then 10 else
  if p.val = (true, vertices_408) then 24 else
  if p.val = (true, vertices_296) then 11 else
  if p.val = (true, vertices_176) then 12 else
  if p.val = (true, vertices_304) then 13 else
  if p.val = (true, vertices_208) then 14 else
  if p.val = (true, vertices_592) then 15 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_553), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_329), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_22), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_262), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_518), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_530), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_52), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_148), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_532), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_292), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_772), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_296), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_176), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_304), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_208), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_592), by decide +kernel⟩
  | 16 => Sum.inl 0
  | 17 => Sum.inr ⟨(false, vertices_779), by decide +kernel⟩
  | 18 => Sum.inr ⟨(false, vertices_339), by decide +kernel⟩
  | 19 => Sum.inr ⟨(false, vertices_707), by decide +kernel⟩
  | 20 => Sum.inl 1
  | 21 => Sum.inr ⟨(false, vertices_677), by decide +kernel⟩
  | 22 => Sum.inl 2
  | 23 => Sum.inr ⟨(false, vertices_233), by decide +kernel⟩
  | 24 => Sum.inr ⟨(true, vertices_408), by decide +kernel⟩
  | 25 => Sum.inl 3
  | 26 => Sum.inl 4
  | 27 => Sum.inl 5
  | 28 => Sum.inl 6
  | 29 => Sum.inl 7
  | 30 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 3 4 7 310 22 3
cert_row_4 1 1 2 4 7 8 812 292 1
cert_row_2 2 2 3 6 7 408
cert_row_4 3 1 3 5 6 8 724 148 2
cert_rows
cert_pivot_2 0 4 2 1
cert_heightProof 4
cert_coverFacet 0 310
cert_cover_5 0 0 0 1 3 4 22 310 3
cert_coverFacet 1 534
cert_cover_2 1 1 0 3 8 22 534 3
cert_coverFacet 2 774
cert_cover_2 2 1 0 7 8 262 774 3
cert_coverFacet 3 594
cert_cover_2 3 3 0 5 8 82 594 3
cert_coverFacet 4 812
cert_cover_5 4 1 1 2 4 7 292 812 1
cert_coverFacet 5 180
cert_cover_2 5 3 1 4 6 52 180 3
cert_coverFacet 6 724
cert_cover_5 6 3 1 3 5 6 148 724 2
cert_coverFacet 7 440
cert_cover_5 7 2 2 3 4 6 408 440 2
cert_coverFacet 8 472
cert_cover_5 8 2 2 3 5 6 408 472 2
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0398

end
end BundlePart22

section BundlePart23
/- Source: ProjectionCertificates/R_m16e10q1_0399.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0399

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [835, 557, 397, 709, 777, 465, 566, 662, 810, 242, 354, 706, 60, 156, 376, 408, 13, 133, 517, 265, 521, 193, 321, 577, 385, 769, 534, 50, 146, 98, 290, 546, 194, 322, 578, 642, 770, 28, 44, 140, 52, 148, 548, 644, 56, 152, 280, 296, 552, 392, 776, 112, 208, 336, 400, 352, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_835, vertices_557, vertices_397, vertices_709, vertices_777, vertices_465, vertices_566, vertices_662, vertices_810, vertices_242, vertices_354, vertices_706, vertices_60, vertices_156, vertices_376, vertices_408] (by decide +kernel)
  polygons := literalFinset [vertices_13, vertices_133, vertices_517, vertices_265, vertices_521, vertices_193, vertices_321, vertices_577, vertices_385, vertices_769, vertices_534, vertices_50, vertices_146, vertices_98, vertices_290, vertices_546, vertices_194, vertices_322, vertices_578, vertices_642, vertices_770, vertices_28, vertices_44, vertices_140, vertices_52, vertices_148, vertices_548, vertices_644, vertices_56, vertices_152, vertices_280, vertices_296, vertices_552, vertices_392, vertices_776, vertices_112, vertices_208, vertices_336, vertices_400, vertices_352, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_835), (false, vertices_557), (false, vertices_397), (false, vertices_709), (false, vertices_777), (false, vertices_465), (true, vertices_534), (true, vertices_50), (true, vertices_146), (true, vertices_98), (true, vertices_290), (true, vertices_546), (true, vertices_194), (true, vertices_642), (true, vertices_28), (true, vertices_52), (true, vertices_148), (true, vertices_56), (true, vertices_152), (true, vertices_280), (true, vertices_296), (true, vertices_112), (true, vertices_352)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 17 20 24 25 27 28 29 30 31
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_835) then 18 else
  if p.val = (false, vertices_557) then 21 else
  if p.val = (false, vertices_397) then 22 else
  if p.val = (false, vertices_709) then 23 else
  if p.val = (false, vertices_777) then 0 else
  if p.val = (false, vertices_465) then 26 else
  if p.val = (true, vertices_534) then 19 else
  if p.val = (true, vertices_50) then 1 else
  if p.val = (true, vertices_146) then 2 else
  if p.val = (true, vertices_98) then 3 else
  if p.val = (true, vertices_290) then 4 else
  if p.val = (true, vertices_546) then 5 else
  if p.val = (true, vertices_194) then 6 else
  if p.val = (true, vertices_642) then 7 else
  if p.val = (true, vertices_28) then 8 else
  if p.val = (true, vertices_52) then 9 else
  if p.val = (true, vertices_148) then 10 else
  if p.val = (true, vertices_56) then 11 else
  if p.val = (true, vertices_152) then 12 else
  if p.val = (true, vertices_280) then 13 else
  if p.val = (true, vertices_296) then 14 else
  if p.val = (true, vertices_112) then 15 else
  if p.val = (true, vertices_352) then 16 else
  0
cert_priority
cert_nodeAtPriority_45 777 50 146 98 290 546 194 642 28 52 148 56 152 280 296 112 352 835 534 557 397 709 465
cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 1 3 8 534
cert_row_4 1 0 2 4 7 8 810 290 1
cert_row_4 2 0 3 4 5 6 242 50 3
cert_row_4 3 2 3 4 5 7 376 56 3
cert_rows
cert_pivot_2 1 8 0 2
cert_heightProof 4
cert_coverFacet 0 566
cert_cover_5 0 0 0 1 3 4 534 566 3
cert_coverFacet 1 662
cert_cover_5 1 0 0 1 3 6 534 662 3
cert_coverFacet 2 810
cert_cover_5 2 1 0 2 4 7 290 810 1
cert_coverFacet 3 242
cert_cover_5 3 2 0 3 4 5 50 242 3
cert_coverFacet 4 354
cert_cover_2 4 4 0 5 7 98 354 3
cert_coverFacet 5 706
cert_cover_2 5 5 0 6 8 194 706 3
cert_coverFacet 6 60
cert_cover_2 6 2 1 3 4 28 60 3
cert_coverFacet 7 156
cert_cover_2 7 2 1 3 6 28 156 3
cert_coverFacet 8 376
cert_cover_5 8 3 2 3 4 5 56 376 3
cert_coverFacet 9 408
cert_cover_2 9 3 2 6 7 152 408 3
cert_coveringFacets_5
cert_coveringProof
cert_certificate 4 10
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0399

end
end BundlePart23

section BundlePart24
/- Source: ProjectionCertificates/R_m16e10q1_0400.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0400

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [647, 781, 357, 165, 601, 329, 737, 182, 310, 774, 794, 722, 184, 312, 216, 488, 37, 133, 261, 517, 73, 265, 521, 97, 161, 321, 577, 641, 54, 134, 262, 518, 146, 274, 530, 642, 770, 164, 292, 772, 56, 88, 152, 280, 536, 168, 296, 200, 328, 776, 176, 304, 208, 592, 224, 352, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_647, vertices_781, vertices_357, vertices_165, vertices_601, vertices_329, vertices_737, vertices_182, vertices_310, vertices_774, vertices_794, vertices_722, vertices_184, vertices_312, vertices_216, vertices_488] (by decide +kernel)
  polygons := literalFinset [vertices_37, vertices_133, vertices_261, vertices_517, vertices_73, vertices_265, vertices_521, vertices_97, vertices_161, vertices_321, vertices_577, vertices_641, vertices_54, vertices_134, vertices_262, vertices_518, vertices_146, vertices_274, vertices_530, vertices_642, vertices_770, vertices_164, vertices_292, vertices_772, vertices_56, vertices_88, vertices_152, vertices_280, vertices_536, vertices_168, vertices_296, vertices_200, vertices_328, vertices_776, vertices_176, vertices_304, vertices_208, vertices_592, vertices_224, vertices_352, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_647), (false, vertices_781), (false, vertices_357), (false, vertices_165), (false, vertices_601), (false, vertices_329), (false, vertices_737), (true, vertices_54), (true, vertices_262), (true, vertices_146), (true, vertices_274), (true, vertices_530), (true, vertices_770), (true, vertices_56), (true, vertices_152), (true, vertices_280), (true, vertices_168), (true, vertices_296), (true, vertices_200), (true, vertices_176), (true, vertices_304), (true, vertices_208)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 16 19 22 24 25 27 28 29 30
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_647) then 17 else
  if p.val = (false, vertices_781) then 20 else
  if p.val = (false, vertices_357) then 21 else
  if p.val = (false, vertices_165) then 0 else
  if p.val = (false, vertices_601) then 23 else
  if p.val = (false, vertices_329) then 1 else
  if p.val = (false, vertices_737) then 26 else
  if p.val = (true, vertices_54) then 18 else
  if p.val = (true, vertices_262) then 2 else
  if p.val = (true, vertices_146) then 3 else
  if p.val = (true, vertices_274) then 4 else
  if p.val = (true, vertices_530) then 5 else
  if p.val = (true, vertices_770) then 6 else
  if p.val = (true, vertices_56) then 7 else
  if p.val = (true, vertices_152) then 8 else
  if p.val = (true, vertices_280) then 9 else
  if p.val = (true, vertices_168) then 10 else
  if p.val = (true, vertices_296) then 11 else
  if p.val = (true, vertices_200) then 12 else
  if p.val = (true, vertices_176) then 13 else
  if p.val = (true, vertices_304) then 14 else
  if p.val = (true, vertices_208) then 15 else
  0
cert_priority
cert_nodeAtPriority_24 1 165 0 329 262 146 274 530 770 56 152 280 168 296 200 176 304 208 647 54 781 357 601 737
cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 1 3 4 54
cert_row_4 1 2 4 5 6 7 488 168 2
cert_row_4 2 0 2 3 7 8 794 274 1
cert_row_4 3 0 3 5 6 8 722 146 2
cert_rows
cert_pivot_2 1 4 2 0
cert_heightProof 4
cert_coverFacet 0 182
cert_cover_5 0 0 0 1 3 6 54 182 3
cert_coverFacet 1 310
cert_cover_5 1 0 0 1 3 7 54 310 3
cert_coverFacet 2 774
cert_cover_2 2 1 0 7 8 262 774 3
cert_coverFacet 3 794
cert_cover_5 3 2 0 2 3 7 274 794 1
cert_coverFacet 4 722
cert_cover_5 4 3 0 3 5 6 146 722 2
cert_coverFacet 5 184
cert_cover_2 5 3 2 4 6 56 184 3
cert_coverFacet 6 312
cert_cover_2 6 3 2 4 7 56 312 3
cert_coverFacet 7 216
cert_cover_2 7 3 2 5 6 88 216 3
cert_coverFacet 8 488
cert_cover_5 8 1 2 4 5 6 168 488 2
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0400

end
end BundlePart24

section BundlePart25
/- Source: ProjectionCertificates/R_m16e10q1_0401.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0401

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [659, 405, 229, 293, 313, 537, 681, 454, 346, 602, 402, 738, 844, 612, 804, 808, 37, 133, 261, 25, 41, 521, 145, 273, 529, 161, 289, 641, 90, 146, 274, 530, 194, 322, 578, 386, 642, 100, 292, 548, 196, 324, 580, 388, 772, 280, 536, 296, 552, 328, 584, 776, 400, 224, 608, 672, 800]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_659, vertices_405, vertices_229, vertices_293, vertices_313, vertices_537, vertices_681, vertices_454, vertices_346, vertices_602, vertices_402, vertices_738, vertices_844, vertices_612, vertices_804, vertices_808] (by decide +kernel)
  polygons := literalFinset [vertices_37, vertices_133, vertices_261, vertices_25, vertices_41, vertices_521, vertices_145, vertices_273, vertices_529, vertices_161, vertices_289, vertices_641, vertices_90, vertices_146, vertices_274, vertices_530, vertices_194, vertices_322, vertices_578, vertices_386, vertices_642, vertices_100, vertices_292, vertices_548, vertices_196, vertices_324, vertices_580, vertices_388, vertices_772, vertices_280, vertices_536, vertices_296, vertices_552, vertices_328, vertices_584, vertices_776, vertices_400, vertices_224, vertices_608, vertices_672, vertices_800] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_659), (false, vertices_405), (false, vertices_229), (false, vertices_293), (false, vertices_313), (false, vertices_537), (false, vertices_681), (true, vertices_90), (true, vertices_274), (true, vertices_194), (true, vertices_322), (true, vertices_578), (true, vertices_386), (true, vertices_548), (true, vertices_324), (true, vertices_580), (true, vertices_772), (true, vertices_328), (true, vertices_584), (true, vertices_776), (true, vertices_608), (true, vertices_800)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 16 19 22 25 26 27 28 29 30
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_659) then 17 else
  if p.val = (false, vertices_405) then 20 else
  if p.val = (false, vertices_229) then 21 else
  if p.val = (false, vertices_293) then 0 else
  if p.val = (false, vertices_313) then 23 else
  if p.val = (false, vertices_537) then 1 else
  if p.val = (false, vertices_681) then 24 else
  if p.val = (true, vertices_90) then 18 else
  if p.val = (true, vertices_274) then 2 else
  if p.val = (true, vertices_194) then 3 else
  if p.val = (true, vertices_322) then 4 else
  if p.val = (true, vertices_578) then 5 else
  if p.val = (true, vertices_386) then 6 else
  if p.val = (true, vertices_548) then 7 else
  if p.val = (true, vertices_324) then 8 else
  if p.val = (true, vertices_580) then 9 else
  if p.val = (true, vertices_772) then 10 else
  if p.val = (true, vertices_328) then 11 else
  if p.val = (true, vertices_584) then 12 else
  if p.val = (true, vertices_776) then 13 else
  if p.val = (true, vertices_608) then 14 else
  if p.val = (true, vertices_800) then 15 else
  0
cert_priority
cert_nodeAtPriority_39 0 293 1 537 274 194 322 578 386 548 324 580 772 328 584 776 608 800 659 90 405 229 313 681
cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 2 3 5 90
cert_row_4 1 0 4 5 6 8 738 194 1
cert_row_4 2 0 1 5 6 7 454 194 1
cert_row_4 3 1 2 5 7 8 844 324 1
cert_rows
cert_pivot_2 3 4 0 1
cert_heightProof 4
cert_coverFacet 0 454
cert_cover_5 0 2 0 1 5 6 194 454 1
cert_coverFacet 1 346
cert_cover_5 1 0 0 2 3 7 90 346 3
cert_coverFacet 2 602
cert_cover_5 2 0 0 2 3 8 90 602 3
cert_coverFacet 3 402
cert_cover_2 3 3 0 6 7 146 402 3
cert_coverFacet 4 738
cert_cover_5 4 1 0 4 5 6 194 738 1
cert_coverFacet 5 844
cert_cover_5 5 3 1 2 5 7 324 844 1
cert_coverFacet 6 612
cert_cover_2 6 4 1 5 8 100 612 3
cert_coverFacet 7 804
cert_cover_2 7 4 1 7 8 292 804 3
cert_coverFacet 8 808
cert_cover_2 8 4 2 7 8 296 808 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0401

end
end BundlePart25

section BundlePart26
/- Source: ProjectionCertificates/R_m16e10q1_0402.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0402

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [707, 301, 53, 789, 241, 657, 865, 398, 618, 202, 778, 914, 124, 220, 404, 808, 21, 37, 261, 49, 145, 529, 97, 289, 193, 577, 641, 769, 74, 138, 266, 522, 194, 578, 386, 642, 770, 92, 44, 140, 268, 52, 148, 276, 388, 104, 296, 552, 200, 776, 112, 208, 400, 656, 784, 608, 800]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_707, vertices_301, vertices_53, vertices_789, vertices_241, vertices_657, vertices_865, vertices_398, vertices_618, vertices_202, vertices_778, vertices_914, vertices_124, vertices_220, vertices_404, vertices_808] (by decide +kernel)
  polygons := literalFinset [vertices_21, vertices_37, vertices_261, vertices_49, vertices_145, vertices_529, vertices_97, vertices_289, vertices_193, vertices_577, vertices_641, vertices_769, vertices_74, vertices_138, vertices_266, vertices_522, vertices_194, vertices_578, vertices_386, vertices_642, vertices_770, vertices_92, vertices_44, vertices_140, vertices_268, vertices_52, vertices_148, vertices_276, vertices_388, vertices_104, vertices_296, vertices_552, vertices_200, vertices_776, vertices_112, vertices_208, vertices_400, vertices_656, vertices_784, vertices_608, vertices_800] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_707), (false, vertices_301), (false, vertices_53), (false, vertices_789), (false, vertices_241), (false, vertices_657), (false, vertices_865), (true, vertices_74), (true, vertices_138), (true, vertices_266), (true, vertices_522), (true, vertices_386), (true, vertices_770), (true, vertices_92), (true, vertices_140), (true, vertices_148), (true, vertices_388), (true, vertices_104), (true, vertices_552), (true, vertices_200), (true, vertices_776), (true, vertices_400)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 16 18 22 23 25 27 28 29 30
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_707) then 17 else
  if p.val = (false, vertices_301) then 19 else
  if p.val = (false, vertices_53) then 0 else
  if p.val = (false, vertices_789) then 20 else
  if p.val = (false, vertices_241) then 24 else
  if p.val = (false, vertices_657) then 1 else
  if p.val = (false, vertices_865) then 26 else
  if p.val = (true, vertices_74) then 2 else
  if p.val = (true, vertices_138) then 3 else
  if p.val = (true, vertices_266) then 4 else
  if p.val = (true, vertices_522) then 5 else
  if p.val = (true, vertices_386) then 6 else
  if p.val = (true, vertices_770) then 7 else
  if p.val = (true, vertices_92) then 21 else
  if p.val = (true, vertices_140) then 8 else
  if p.val = (true, vertices_148) then 9 else
  if p.val = (true, vertices_388) then 10 else
  if p.val = (true, vertices_104) then 11 else
  if p.val = (true, vertices_552) then 12 else
  if p.val = (true, vertices_200) then 13 else
  if p.val = (true, vertices_776) then 14 else
  if p.val = (true, vertices_400) then 15 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_53), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_657), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_74), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_138), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_266), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_522), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_386), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_770), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_140), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_148), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_388), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_104), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_552), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_200), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_776), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_400), by decide +kernel⟩
  | 16 => Sum.inl 0
  | 17 => Sum.inr ⟨(false, vertices_707), by decide +kernel⟩
  | 18 => Sum.inl 1
  | 19 => Sum.inr ⟨(false, vertices_301), by decide +kernel⟩
  | 20 => Sum.inr ⟨(false, vertices_789), by decide +kernel⟩
  | 21 => Sum.inr ⟨(true, vertices_92), by decide +kernel⟩
  | 22 => Sum.inl 2
  | 23 => Sum.inl 3
  | 24 => Sum.inr ⟨(false, vertices_241), by decide +kernel⟩
  | 25 => Sum.inl 4
  | 26 => Sum.inr ⟨(false, vertices_865), by decide +kernel⟩
  | 27 => Sum.inl 5
  | 28 => Sum.inl 6
  | 29 => Sum.inl 7
  | 30 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 2 4 5 8 618 74 2
cert_row_2 1 1 2 3 5 92
cert_row_4 2 0 1 2 6 7 398 138 1
cert_row_4 3 0 3 6 7 8 914 386 1
cert_rows
cert_pivot_2 4 5 1 0
cert_heightProof 4
cert_coverFacet 0 398
cert_cover_5 0 2 0 1 2 6 138 398 1
cert_coverFacet 1 618
cert_cover_5 1 0 0 2 4 5 74 618 2
cert_coverFacet 2 202
cert_cover_2 2 2 0 5 6 74 202 3
cert_coverFacet 3 778
cert_cover_2 3 2 0 7 8 266 778 3
cert_coverFacet 4 914
cert_cover_5 4 3 0 3 6 7 386 914 1
cert_coverFacet 5 124
cert_cover_5 5 1 1 2 3 4 92 124 3
cert_coverFacet 6 220
cert_cover_5 6 1 1 2 3 6 92 220 3
cert_coverFacet 7 404
cert_cover_2 7 3 1 6 7 148 404 3
cert_coverFacet 8 808
cert_cover_2 8 4 2 7 8 296 808 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0402

end
end BundlePart26

section BundlePart27
/- Source: ProjectionCertificates/R_m16e10q1_0403.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0403

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [779, 211, 275, 675, 613, 849, 225, 654, 154, 282, 188, 316, 844, 356, 676, 496, 19, 131, 259, 515, 81, 273, 97, 161, 545, 193, 577, 769, 26, 138, 266, 522, 146, 274, 642, 60, 140, 268, 524, 100, 164, 292, 548, 324, 580, 644, 152, 280, 776, 176, 304, 208, 336, 224, 352, 672, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_779, vertices_211, vertices_275, vertices_675, vertices_613, vertices_849, vertices_225, vertices_654, vertices_154, vertices_282, vertices_188, vertices_316, vertices_844, vertices_356, vertices_676, vertices_496] (by decide +kernel)
  polygons := literalFinset [vertices_19, vertices_131, vertices_259, vertices_515, vertices_81, vertices_273, vertices_97, vertices_161, vertices_545, vertices_193, vertices_577, vertices_769, vertices_26, vertices_138, vertices_266, vertices_522, vertices_146, vertices_274, vertices_642, vertices_60, vertices_140, vertices_268, vertices_524, vertices_100, vertices_164, vertices_292, vertices_548, vertices_324, vertices_580, vertices_644, vertices_152, vertices_280, vertices_776, vertices_176, vertices_304, vertices_208, vertices_336, vertices_224, vertices_352, vertices_672, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_779), (false, vertices_211), (false, vertices_275), (false, vertices_675), (false, vertices_613), (false, vertices_849), (false, vertices_225), (true, vertices_26), (true, vertices_138), (true, vertices_60), (true, vertices_140), (true, vertices_268), (true, vertices_524), (true, vertices_164), (true, vertices_292), (true, vertices_324), (true, vertices_644), (true, vertices_152), (true, vertices_280), (true, vertices_176), (true, vertices_304), (true, vertices_352)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 16 20 23 24 26 27 28 29 30
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_779) then 17 else
  if p.val = (false, vertices_211) then 18 else
  if p.val = (false, vertices_275) then 0 else
  if p.val = (false, vertices_675) then 19 else
  if p.val = (false, vertices_613) then 21 else
  if p.val = (false, vertices_849) then 25 else
  if p.val = (false, vertices_225) then 1 else
  if p.val = (true, vertices_26) then 2 else
  if p.val = (true, vertices_138) then 3 else
  if p.val = (true, vertices_60) then 22 else
  if p.val = (true, vertices_140) then 4 else
  if p.val = (true, vertices_268) then 5 else
  if p.val = (true, vertices_524) then 6 else
  if p.val = (true, vertices_164) then 7 else
  if p.val = (true, vertices_292) then 8 else
  if p.val = (true, vertices_324) then 9 else
  if p.val = (true, vertices_644) then 10 else
  if p.val = (true, vertices_152) then 11 else
  if p.val = (true, vertices_280) then 12 else
  if p.val = (true, vertices_176) then 13 else
  if p.val = (true, vertices_304) then 14 else
  if p.val = (true, vertices_352) then 15 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_275), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_225), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_26), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_138), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_140), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_268), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_524), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_164), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_292), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_324), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_644), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_152), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_280), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_176), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_304), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_352), by decide +kernel⟩
  | 16 => Sum.inl 0
  | 17 => Sum.inr ⟨(false, vertices_779), by decide +kernel⟩
  | 18 => Sum.inr ⟨(false, vertices_211), by decide +kernel⟩
  | 19 => Sum.inr ⟨(false, vertices_675), by decide +kernel⟩
  | 20 => Sum.inl 1
  | 21 => Sum.inr ⟨(false, vertices_613), by decide +kernel⟩
  | 22 => Sum.inr ⟨(true, vertices_60), by decide +kernel⟩
  | 23 => Sum.inl 2
  | 24 => Sum.inl 3
  | 25 => Sum.inr ⟨(false, vertices_849), by decide +kernel⟩
  | 26 => Sum.inl 4
  | 27 => Sum.inl 5
  | 28 => Sum.inl 6
  | 29 => Sum.inl 7
  | 30 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 2 6 8 654 138 1
cert_row_4 1 1 2 5 7 8 844 268 2
cert_row_2 2 1 2 3 4 60
cert_row_4 3 3 4 5 6 7 496 176 2
cert_rows
cert_pivot_2 0 8 1 3
cert_heightProof 4
cert_coverFacet 0 654
cert_cover_5 0 0 0 1 2 6 138 654 1
cert_coverFacet 1 154
cert_cover_2 1 2 0 3 6 26 154 3
cert_coverFacet 2 282
cert_cover_2 2 2 0 3 7 26 282 3
cert_coverFacet 3 188
cert_cover_5 3 2 1 2 3 6 60 188 3
cert_coverFacet 4 316
cert_cover_5 4 2 1 2 3 7 60 316 3
cert_coverFacet 5 844
cert_cover_5 5 1 1 2 5 7 268 844 2
cert_coverFacet 6 356
cert_cover_2 6 4 1 5 7 100 356 3
cert_coverFacet 7 676
cert_cover_2 7 4 1 6 8 164 676 3
cert_coverFacet 8 496
cert_cover_5 8 3 3 4 5 6 176 496 2
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0403

end
end BundlePart27

section BundlePart28
/- Source: ProjectionCertificates/R_m16e10q1_0404.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0404

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [659, 173, 77, 597, 149, 361, 737, 406, 810, 370, 626, 898, 348, 396, 680, 904, 13, 21, 69, 133, 41, 73, 145, 529, 97, 161, 577, 641, 114, 146, 274, 530, 290, 546, 386, 642, 770, 76, 140, 268, 84, 148, 276, 388, 168, 296, 552, 328, 392, 648, 776, 336, 592, 352, 608, 672, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_659, vertices_173, vertices_77, vertices_597, vertices_149, vertices_361, vertices_737, vertices_406, vertices_810, vertices_370, vertices_626, vertices_898, vertices_348, vertices_396, vertices_680, vertices_904] (by decide +kernel)
  polygons := literalFinset [vertices_13, vertices_21, vertices_69, vertices_133, vertices_41, vertices_73, vertices_145, vertices_529, vertices_97, vertices_161, vertices_577, vertices_641, vertices_114, vertices_146, vertices_274, vertices_530, vertices_290, vertices_546, vertices_386, vertices_642, vertices_770, vertices_76, vertices_140, vertices_268, vertices_84, vertices_148, vertices_276, vertices_388, vertices_168, vertices_296, vertices_552, vertices_328, vertices_392, vertices_648, vertices_776, vertices_336, vertices_592, vertices_352, vertices_608, vertices_672, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_659), (false, vertices_173), (false, vertices_77), (false, vertices_597), (false, vertices_149), (false, vertices_361), (false, vertices_737), (true, vertices_114), (true, vertices_274), (true, vertices_290), (true, vertices_546), (true, vertices_386), (true, vertices_770), (true, vertices_268), (true, vertices_276), (true, vertices_388), (true, vertices_552), (true, vertices_392), (true, vertices_648), (true, vertices_776), (true, vertices_336), (true, vertices_896)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 16 19 22 24 25 27 28 29 30
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_659) then 17 else
  if p.val = (false, vertices_173) then 20 else
  if p.val = (false, vertices_77) then 0 else
  if p.val = (false, vertices_597) then 21 else
  if p.val = (false, vertices_149) then 1 else
  if p.val = (false, vertices_361) then 23 else
  if p.val = (false, vertices_737) then 26 else
  if p.val = (true, vertices_114) then 18 else
  if p.val = (true, vertices_274) then 2 else
  if p.val = (true, vertices_290) then 3 else
  if p.val = (true, vertices_546) then 4 else
  if p.val = (true, vertices_386) then 5 else
  if p.val = (true, vertices_770) then 6 else
  if p.val = (true, vertices_268) then 7 else
  if p.val = (true, vertices_276) then 8 else
  if p.val = (true, vertices_388) then 9 else
  if p.val = (true, vertices_552) then 10 else
  if p.val = (true, vertices_392) then 11 else
  if p.val = (true, vertices_648) then 12 else
  if p.val = (true, vertices_776) then 13 else
  if p.val = (true, vertices_336) then 14 else
  if p.val = (true, vertices_896) then 15 else
  0
cert_priority
cert_nodeAtPriority_24 1 77 0 149 274 290 546 386 770 268 276 388 552 392 648 776 336 896 659 114 173 597 361 737
cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 3 6 7 406 146 1
cert_row_4 1 0 2 4 7 8 810 290 1
cert_row_2 2 0 3 4 5 114
cert_row_4 3 1 2 3 5 7 348 76 2
cert_rows
cert_pivot_2 6 8 0 1
cert_heightProof 4
cert_coverFacet 0 406
cert_cover_5 0 0 0 1 3 6 146 406 1
cert_coverFacet 1 810
cert_cover_5 1 1 0 2 4 7 290 810 1
cert_coverFacet 2 370
cert_cover_5 2 2 0 3 4 7 114 370 3
cert_coverFacet 3 626
cert_cover_5 3 2 0 3 4 8 114 626 3
cert_coverFacet 4 898
cert_cover_2 4 6 0 7 8 386 898 3
cert_coverFacet 5 348
cert_cover_5 5 3 1 2 3 5 76 348 2
cert_coverFacet 6 396
cert_cover_2 6 2 1 6 7 140 396 3
cert_coverFacet 7 680
cert_cover_2 7 4 2 6 8 168 680 3
cert_coverFacet 8 904
cert_cover_2 8 6 2 7 8 392 904 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0404

end
end BundlePart28

section BundlePart29
/- Source: ProjectionCertificates/R_m16e10q1_0405.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0405

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [779, 227, 579, 387, 613, 409, 681, 598, 466, 786, 220, 284, 236, 300, 820, 808, 67, 131, 259, 515, 137, 265, 521, 97, 161, 545, 577, 385, 82, 274, 530, 194, 578, 386, 770, 28, 44, 204, 268, 84, 276, 532, 100, 292, 548, 580, 152, 280, 168, 296, 552, 776, 208, 400, 784, 224, 800]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_779, vertices_227, vertices_579, vertices_387, vertices_613, vertices_409, vertices_681, vertices_598, vertices_466, vertices_786, vertices_220, vertices_284, vertices_236, vertices_300, vertices_820, vertices_808] (by decide +kernel)
  polygons := literalFinset [vertices_67, vertices_131, vertices_259, vertices_515, vertices_137, vertices_265, vertices_521, vertices_97, vertices_161, vertices_545, vertices_577, vertices_385, vertices_82, vertices_274, vertices_530, vertices_194, vertices_578, vertices_386, vertices_770, vertices_28, vertices_44, vertices_204, vertices_268, vertices_84, vertices_276, vertices_532, vertices_100, vertices_292, vertices_548, vertices_580, vertices_152, vertices_280, vertices_168, vertices_296, vertices_552, vertices_776, vertices_208, vertices_400, vertices_784, vertices_224, vertices_800] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_779), (false, vertices_227), (false, vertices_579), (false, vertices_387), (false, vertices_613), (false, vertices_409), (false, vertices_681), (true, vertices_82), (true, vertices_274), (true, vertices_530), (true, vertices_28), (true, vertices_44), (true, vertices_204), (true, vertices_268), (true, vertices_84), (true, vertices_276), (true, vertices_532), (true, vertices_292), (true, vertices_296), (true, vertices_208), (true, vertices_784), (true, vertices_800)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 16 19 22 25 26 27 28 29 30
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_779) then 17 else
  if p.val = (false, vertices_227) then 18 else
  if p.val = (false, vertices_579) then 0 else
  if p.val = (false, vertices_387) then 1 else
  if p.val = (false, vertices_613) then 20 else
  if p.val = (false, vertices_409) then 23 else
  if p.val = (false, vertices_681) then 24 else
  if p.val = (true, vertices_82) then 2 else
  if p.val = (true, vertices_274) then 3 else
  if p.val = (true, vertices_530) then 4 else
  if p.val = (true, vertices_28) then 5 else
  if p.val = (true, vertices_44) then 6 else
  if p.val = (true, vertices_204) then 21 else
  if p.val = (true, vertices_268) then 7 else
  if p.val = (true, vertices_84) then 8 else
  if p.val = (true, vertices_276) then 9 else
  if p.val = (true, vertices_532) then 10 else
  if p.val = (true, vertices_292) then 11 else
  if p.val = (true, vertices_296) then 12 else
  if p.val = (true, vertices_208) then 13 else
  if p.val = (true, vertices_784) then 14 else
  if p.val = (true, vertices_800) then 15 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_579), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_387), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_82), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_274), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_530), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_28), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_44), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_268), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_84), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_276), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_532), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_292), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_296), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_208), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_784), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_800), by decide +kernel⟩
  | 16 => Sum.inl 0
  | 17 => Sum.inr ⟨(false, vertices_779), by decide +kernel⟩
  | 18 => Sum.inr ⟨(false, vertices_227), by decide +kernel⟩
  | 19 => Sum.inl 1
  | 20 => Sum.inr ⟨(false, vertices_613), by decide +kernel⟩
  | 21 => Sum.inr ⟨(true, vertices_204), by decide +kernel⟩
  | 22 => Sum.inl 2
  | 23 => Sum.inr ⟨(false, vertices_409), by decide +kernel⟩
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
cert_row_2 0 1 2 5 6 204
cert_row_4 1 0 3 5 6 7 466 82 3
cert_row_4 2 0 1 3 5 8 598 82 1
cert_row_4 3 1 3 4 7 8 820 276 2
cert_rows
cert_pivot_2 2 6 0 1
cert_heightProof 4
cert_coverFacet 0 598
cert_cover_5 0 2 0 1 3 5 82 598 1
cert_coverFacet 1 466
cert_cover_5 1 1 0 3 5 6 82 466 3
cert_coverFacet 2 786
cert_cover_2 2 3 0 7 8 274 786 3
cert_coverFacet 3 220
cert_cover_5 3 0 1 2 3 5 28 220 3
cert_coverFacet 4 284
cert_cover_2 4 2 1 3 7 28 284 3
cert_coverFacet 5 236
cert_cover_5 5 0 1 2 4 5 44 236 3
cert_coverFacet 6 300
cert_cover_2 6 2 1 4 7 44 300 3
cert_coverFacet 7 820
cert_cover_5 7 3 1 3 4 7 276 820 2
cert_coverFacet 8 808
cert_cover_2 8 4 2 7 8 296 808 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0405

end
end BundlePart29

-- Public target certificates; internal witness data stays private.
namespace Nonrational.TerminalVerification
open Papers.RationalityTen.ChirotopeDensity.FiniteProjection
open Nonrational.TerminalData
set_option maxRecDepth 100000
set_option maxHeartbeats 0

public theorem projection_4263 : Certifies 4263 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0375.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_4264 : Certifies 4264 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0376.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_4265 : Certifies 4265 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0377.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_4266 : Certifies 4266 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0379.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_4267 : Certifies 4267 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0380.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_4268 : Certifies 4268 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0381.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_4269 : Certifies 4269 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0382.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_4270 : Certifies 4270 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0383.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_4271 : Certifies 4271 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0384.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_4272 : Certifies 4272 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0385.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_4273 : Certifies 4273 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0386.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_4274 : Certifies 4274 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0387.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_4275 : Certifies 4275 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0388.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_4276 : Certifies 4276 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0389.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_4277 : Certifies 4277 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0390.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_4278 : Certifies 4278 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0391.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_4279 : Certifies 4279 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0392.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_4280 : Certifies 4280 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0393.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_4281 : Certifies 4281 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0394.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_4282 : Certifies 4282 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0395.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_4283 : Certifies 4283 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0396.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_4284 : Certifies 4284 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0397.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_4285 : Certifies 4285 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0398.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_4286 : Certifies 4286 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0399.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_4287 : Certifies 4287 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0400.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_4288 : Certifies 4288 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0401.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_4289 : Certifies 4289 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0402.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_4290 : Certifies 4290 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0403.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_4291 : Certifies 4291 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0404.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_4292 : Certifies 4292 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0405.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem certified_B141 (j : Fin 30) :
    Certifies (4263 + j.val) := by
  fin_cases j
  · exact projection_4263
  · exact projection_4264
  · exact projection_4265
  · exact projection_4266
  · exact projection_4267
  · exact projection_4268
  · exact projection_4269
  · exact projection_4270
  · exact projection_4271
  · exact projection_4272
  · exact projection_4273
  · exact projection_4274
  · exact projection_4275
  · exact projection_4276
  · exact projection_4277
  · exact projection_4278
  · exact projection_4279
  · exact projection_4280
  · exact projection_4281
  · exact projection_4282
  · exact projection_4283
  · exact projection_4284
  · exact projection_4285
  · exact projection_4286
  · exact projection_4287
  · exact projection_4288
  · exact projection_4289
  · exact projection_4290
  · exact projection_4291
  · exact projection_4292

end Nonrational.TerminalVerification
-- Explicit facial frame witnesses, with lexical vector tracking.
