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
/- Source: ProjectionCertificates/R_m16e10q1_0345.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0345

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [155, 539, 803, 451, 357, 657, 737, 398, 778, 60, 220, 300, 628, 452, 824, 720, 27, 131, 259, 515, 145, 529, 97, 289, 545, 193, 321, 641, 138, 266, 522, 386, 770, 28, 44, 140, 268, 52, 84, 100, 292, 196, 324, 388, 56, 152, 536, 296, 776, 560, 208, 592, 656, 608, 800, 448, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_155, vertices_539, vertices_803, vertices_451, vertices_357, vertices_657, vertices_737, vertices_398, vertices_778, vertices_60, vertices_220, vertices_300, vertices_628, vertices_452, vertices_824, vertices_720] (by decide +kernel)
  polygons := literalFinset [vertices_27, vertices_131, vertices_259, vertices_515, vertices_145, vertices_529, vertices_97, vertices_289, vertices_545, vertices_193, vertices_321, vertices_641, vertices_138, vertices_266, vertices_522, vertices_386, vertices_770, vertices_28, vertices_44, vertices_140, vertices_268, vertices_52, vertices_84, vertices_100, vertices_292, vertices_196, vertices_324, vertices_388, vertices_56, vertices_152, vertices_536, vertices_296, vertices_776, vertices_560, vertices_208, vertices_592, vertices_656, vertices_608, vertices_800, vertices_448, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_155), (false, vertices_539), (false, vertices_803), (false, vertices_451), (false, vertices_357), (false, vertices_657), (false, vertices_737), (true, vertices_266), (true, vertices_28), (true, vertices_44), (true, vertices_140), (true, vertices_268), (true, vertices_52), (true, vertices_84), (true, vertices_196), (true, vertices_388), (true, vertices_56), (true, vertices_296), (true, vertices_776), (true, vertices_560), (true, vertices_208), (true, vertices_592)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 21 16 18 24 25 27 28 29 30
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_155) then 19 else
  if p.val = (false, vertices_539) then 20 else
  if p.val = (false, vertices_803) then 22 else
  if p.val = (false, vertices_451) then 23 else
  if p.val = (false, vertices_357) then 17 else
  if p.val = (false, vertices_657) then 0 else
  if p.val = (false, vertices_737) then 26 else
  if p.val = (true, vertices_266) then 1 else
  if p.val = (true, vertices_28) then 2 else
  if p.val = (true, vertices_44) then 3 else
  if p.val = (true, vertices_140) then 4 else
  if p.val = (true, vertices_268) then 5 else
  if p.val = (true, vertices_52) then 6 else
  if p.val = (true, vertices_84) then 7 else
  if p.val = (true, vertices_196) then 8 else
  if p.val = (true, vertices_388) then 9 else
  if p.val = (true, vertices_56) then 10 else
  if p.val = (true, vertices_296) then 11 else
  if p.val = (true, vertices_776) then 12 else
  if p.val = (true, vertices_560) then 13 else
  if p.val = (true, vertices_208) then 14 else
  if p.val = (true, vertices_592) then 15 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_657), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_266), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_28), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_44), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_140), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_268), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_52), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_84), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_196), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_388), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_56), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_296), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_776), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_560), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_208), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_592), by decide +kernel⟩
  | 16 => Sum.inl 1
  | 17 => Sum.inr ⟨(false, vertices_357), by decide +kernel⟩
  | 18 => Sum.inl 2
  | 19 => Sum.inr ⟨(false, vertices_155), by decide +kernel⟩
  | 20 => Sum.inr ⟨(false, vertices_539), by decide +kernel⟩
  | 21 => Sum.inl 0
  | 22 => Sum.inr ⟨(false, vertices_803), by decide +kernel⟩
  | 23 => Sum.inr ⟨(false, vertices_451), by decide +kernel⟩
  | 24 => Sum.inl 3
  | 25 => Sum.inl 4
  | 26 => Sum.inr ⟨(false, vertices_737), by decide +kernel⟩
  | 27 => Sum.inl 5
  | 28 => Sum.inl 6
  | 29 => Sum.inl 7
  | 30 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 2 6 7 398 138 1
cert_row_4 1 1 2 3 5 6 220 28 3
cert_row_4 2 1 3 4 5 8 628 52 3
cert_row_4 3 2 3 4 7 8 824 56 3
cert_rows
cert_pivot_2 0 6 1 2
cert_heightProof 4
cert_coverFacet 0 398
cert_cover_5 0 0 0 1 2 6 138 398 1
cert_coverFacet 1 778
cert_cover_2 1 2 0 7 8 266 778 3
cert_coverFacet 2 60
cert_cover_2 2 2 1 3 4 28 60 3
cert_coverFacet 3 220
cert_cover_5 3 1 1 2 3 5 28 220 3
cert_coverFacet 4 300
cert_cover_2 4 2 1 4 7 44 300 3
cert_coverFacet 5 628
cert_cover_5 5 2 1 3 4 5 52 628 3
cert_coverFacet 6 452
cert_cover_2 6 5 1 6 7 196 452 3
cert_coverFacet 7 824
cert_cover_5 7 3 2 3 4 7 56 824 3
cert_coverFacet 8 720
cert_cover_2 8 5 3 6 8 208 720 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0345

end
end BundlePart0

section BundlePart1
/- Source: ProjectionCertificates/R_m16e10q1_0346.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0346

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [775, 115, 531, 419, 601, 737, 897, 286, 542, 306, 236, 588, 396, 964, 120, 440, 19, 35, 259, 515, 81, 529, 97, 161, 577, 385, 641, 769, 30, 262, 518, 50, 274, 530, 290, 76, 140, 268, 524, 196, 580, 388, 772, 56, 88, 280, 536, 104, 168, 584, 392, 112, 304, 224, 416, 704, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_775, vertices_115, vertices_531, vertices_419, vertices_601, vertices_737, vertices_897, vertices_286, vertices_542, vertices_306, vertices_236, vertices_588, vertices_396, vertices_964, vertices_120, vertices_440] (by decide +kernel)
  polygons := literalFinset [vertices_19, vertices_35, vertices_259, vertices_515, vertices_81, vertices_529, vertices_97, vertices_161, vertices_577, vertices_385, vertices_641, vertices_769, vertices_30, vertices_262, vertices_518, vertices_50, vertices_274, vertices_530, vertices_290, vertices_76, vertices_140, vertices_268, vertices_524, vertices_196, vertices_580, vertices_388, vertices_772, vertices_56, vertices_88, vertices_280, vertices_536, vertices_104, vertices_168, vertices_584, vertices_392, vertices_112, vertices_304, vertices_224, vertices_416, vertices_704, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_775), (false, vertices_115), (false, vertices_531), (false, vertices_419), (false, vertices_601), (false, vertices_737), (false, vertices_897), (true, vertices_30), (true, vertices_274), (true, vertices_76), (true, vertices_140), (true, vertices_268), (true, vertices_524), (true, vertices_196), (true, vertices_580), (true, vertices_388), (true, vertices_56), (true, vertices_280), (true, vertices_104), (true, vertices_168), (true, vertices_392), (true, vertices_304)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 19 16 22 24 25 27 28 29 30
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_775) then 17 else
  if p.val = (false, vertices_115) then 20 else
  if p.val = (false, vertices_531) then 0 else
  if p.val = (false, vertices_419) then 21 else
  if p.val = (false, vertices_601) then 23 else
  if p.val = (false, vertices_737) then 26 else
  if p.val = (false, vertices_897) then 1 else
  if p.val = (true, vertices_30) then 18 else
  if p.val = (true, vertices_274) then 2 else
  if p.val = (true, vertices_76) then 3 else
  if p.val = (true, vertices_140) then 4 else
  if p.val = (true, vertices_268) then 5 else
  if p.val = (true, vertices_524) then 6 else
  if p.val = (true, vertices_196) then 7 else
  if p.val = (true, vertices_580) then 8 else
  if p.val = (true, vertices_388) then 9 else
  if p.val = (true, vertices_56) then 10 else
  if p.val = (true, vertices_280) then 11 else
  if p.val = (true, vertices_104) then 12 else
  if p.val = (true, vertices_168) then 13 else
  if p.val = (true, vertices_392) then 14 else
  if p.val = (true, vertices_304) then 15 else
  0
cert_priority
cert_nodeAtPriority_24 0 531 1 897 274 76 140 268 524 196 580 388 56 280 104 168 392 304 775 30 115 419 601 737
cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 1 2 3 30
cert_row_4 1 1 5 6 7 8 964 196 3
cert_row_4 2 1 2 4 5 6 236 76 2
cert_row_4 3 2 3 4 6 7 440 56 3
cert_rows
cert_pivot_2 0 8 1 2
cert_heightProof 4
cert_coverFacet 0 286
cert_cover_5 0 0 0 1 2 7 30 286 3
cert_coverFacet 1 542
cert_cover_5 1 0 0 1 2 8 30 542 3
cert_coverFacet 2 306
cert_cover_2 2 3 0 4 7 50 306 3
cert_coverFacet 3 236
cert_cover_5 3 2 1 2 4 5 76 236 2
cert_coverFacet 4 588
cert_cover_2 4 2 1 5 8 76 588 3
cert_coverFacet 5 396
cert_cover_2 5 2 1 6 7 140 396 3
cert_coverFacet 6 964
cert_cover_5 6 1 1 5 6 7 196 964 3
cert_coverFacet 7 120
cert_cover_2 7 3 2 4 5 56 120 3
cert_coverFacet 8 440
cert_cover_5 8 3 2 3 4 6 56 440 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0346

end
end BundlePart1

section BundlePart2
/- Source: ProjectionCertificates/R_m16e10q1_0347.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0347

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [647, 781, 309, 149, 425, 649, 241, 214, 342, 774, 842, 738, 632, 312, 344, 680, 21, 133, 261, 517, 137, 265, 521, 49, 145, 161, 289, 641, 86, 134, 262, 518, 194, 322, 578, 642, 770, 148, 276, 772, 56, 88, 280, 168, 296, 552, 328, 584, 648, 776, 112, 304, 208, 336, 224, 608, 672]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_647, vertices_781, vertices_309, vertices_149, vertices_425, vertices_649, vertices_241, vertices_214, vertices_342, vertices_774, vertices_842, vertices_738, vertices_632, vertices_312, vertices_344, vertices_680] (by decide +kernel)
  polygons := literalFinset [vertices_21, vertices_133, vertices_261, vertices_517, vertices_137, vertices_265, vertices_521, vertices_49, vertices_145, vertices_161, vertices_289, vertices_641, vertices_86, vertices_134, vertices_262, vertices_518, vertices_194, vertices_322, vertices_578, vertices_642, vertices_770, vertices_148, vertices_276, vertices_772, vertices_56, vertices_88, vertices_280, vertices_168, vertices_296, vertices_552, vertices_328, vertices_584, vertices_648, vertices_776, vertices_112, vertices_304, vertices_208, vertices_336, vertices_224, vertices_608, vertices_672] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_647), (false, vertices_781), (false, vertices_309), (false, vertices_149), (false, vertices_425), (false, vertices_649), (false, vertices_241), (true, vertices_86), (true, vertices_262), (true, vertices_194), (true, vertices_322), (true, vertices_578), (true, vertices_770), (true, vertices_56), (true, vertices_88), (true, vertices_280), (true, vertices_552), (true, vertices_328), (true, vertices_584), (true, vertices_336), (true, vertices_608), (true, vertices_672)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 16 19 22 24 26 27 28 29 30
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_647) then 17 else
  if p.val = (false, vertices_781) then 20 else
  if p.val = (false, vertices_309) then 21 else
  if p.val = (false, vertices_149) then 0 else
  if p.val = (false, vertices_425) then 23 else
  if p.val = (false, vertices_649) then 1 else
  if p.val = (false, vertices_241) then 25 else
  if p.val = (true, vertices_86) then 18 else
  if p.val = (true, vertices_262) then 2 else
  if p.val = (true, vertices_194) then 3 else
  if p.val = (true, vertices_322) then 4 else
  if p.val = (true, vertices_578) then 5 else
  if p.val = (true, vertices_770) then 6 else
  if p.val = (true, vertices_56) then 7 else
  if p.val = (true, vertices_88) then 8 else
  if p.val = (true, vertices_280) then 9 else
  if p.val = (true, vertices_552) then 10 else
  if p.val = (true, vertices_328) then 11 else
  if p.val = (true, vertices_584) then 12 else
  if p.val = (true, vertices_336) then 13 else
  if p.val = (true, vertices_608) then 14 else
  if p.val = (true, vertices_672) then 15 else
  0
cert_priority
cert_nodeAtPriority_50 1 149 0 649 262 194 322 578 770 56 88 280 552 328 584 336 608 672 647 86 781 309 425 241
cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 1 3 5 86
cert_row_4 1 0 2 5 7 8 842 322 1
cert_row_4 2 0 4 5 6 8 738 194 1
cert_row_4 3 2 3 4 5 8 632 56 3
cert_rows
cert_pivot_2 1 7 0 2
cert_heightProof 4
cert_coverFacet 0 214
cert_cover_5 0 0 0 1 3 6 86 214 3
cert_coverFacet 1 342
cert_cover_5 1 0 0 1 3 7 86 342 3
cert_coverFacet 2 774
cert_cover_2 2 1 0 7 8 262 774 3
cert_coverFacet 3 842
cert_cover_5 3 1 0 2 5 7 322 842 1
cert_coverFacet 4 738
cert_cover_5 4 2 0 4 5 6 194 738 1
cert_coverFacet 5 632
cert_cover_5 5 3 2 3 4 5 56 632 3
cert_coverFacet 6 312
cert_cover_2 6 3 2 4 7 56 312 3
cert_coverFacet 7 344
cert_cover_2 7 3 2 5 7 88 344 3
cert_coverFacet 8 680
cert_cover_2 8 4 2 6 8 168 680 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0347

end
end BundlePart2

section BundlePart3
/- Source: ProjectionCertificates/R_m16e10q1_0348.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0348

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [279, 535, 357, 677, 617, 849, 398, 646, 602, 282, 682, 420, 216, 408, 232, 496, 23, 37, 261, 517, 273, 529, 97, 545, 321, 577, 134, 262, 518, 26, 138, 266, 522, 274, 530, 642, 164, 292, 388, 644, 88, 152, 280, 104, 168, 552, 200, 584, 392, 208, 336, 592, 400, 224, 352, 416, 672]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_279, vertices_535, vertices_357, vertices_677, vertices_617, vertices_849, vertices_398, vertices_646, vertices_602, vertices_282, vertices_682, vertices_420, vertices_216, vertices_408, vertices_232, vertices_496] (by decide +kernel)
  polygons := literalFinset [vertices_23, vertices_37, vertices_261, vertices_517, vertices_273, vertices_529, vertices_97, vertices_545, vertices_321, vertices_577, vertices_134, vertices_262, vertices_518, vertices_26, vertices_138, vertices_266, vertices_522, vertices_274, vertices_530, vertices_642, vertices_164, vertices_292, vertices_388, vertices_644, vertices_88, vertices_152, vertices_280, vertices_104, vertices_168, vertices_552, vertices_200, vertices_584, vertices_392, vertices_208, vertices_336, vertices_592, vertices_400, vertices_224, vertices_352, vertices_416, vertices_672] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_279), (false, vertices_535), (false, vertices_357), (false, vertices_677), (false, vertices_617), (false, vertices_849), (true, vertices_134), (true, vertices_26), (true, vertices_138), (true, vertices_266), (true, vertices_522), (true, vertices_642), (true, vertices_388), (true, vertices_88), (true, vertices_152), (true, vertices_280), (true, vertices_168), (true, vertices_200), (true, vertices_392), (true, vertices_208), (true, vertices_400), (true, vertices_224), (true, vertices_416)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 17 20 23 25 27 28 29 30 31
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_279) then 18 else
  if p.val = (false, vertices_535) then 19 else
  if p.val = (false, vertices_357) then 21 else
  if p.val = (false, vertices_677) then 22 else
  if p.val = (false, vertices_617) then 24 else
  if p.val = (false, vertices_849) then 26 else
  if p.val = (true, vertices_134) then 0 else
  if p.val = (true, vertices_26) then 1 else
  if p.val = (true, vertices_138) then 2 else
  if p.val = (true, vertices_266) then 3 else
  if p.val = (true, vertices_522) then 4 else
  if p.val = (true, vertices_642) then 5 else
  if p.val = (true, vertices_388) then 6 else
  if p.val = (true, vertices_88) then 7 else
  if p.val = (true, vertices_152) then 8 else
  if p.val = (true, vertices_280) then 9 else
  if p.val = (true, vertices_168) then 10 else
  if p.val = (true, vertices_200) then 11 else
  if p.val = (true, vertices_392) then 12 else
  if p.val = (true, vertices_208) then 13 else
  if p.val = (true, vertices_400) then 14 else
  if p.val = (true, vertices_224) then 15 else
  if p.val = (true, vertices_416) then 16 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_134), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_26), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_138), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_266), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_522), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_642), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_388), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_88), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_152), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_280), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_168), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_200), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_392), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_208), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_400), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_224), by decide +kernel⟩
  | 16 => Sum.inr ⟨(true, vertices_416), by decide +kernel⟩
  | 17 => Sum.inl 0
  | 18 => Sum.inr ⟨(false, vertices_279), by decide +kernel⟩
  | 19 => Sum.inr ⟨(false, vertices_535), by decide +kernel⟩
  | 20 => Sum.inl 1
  | 21 => Sum.inr ⟨(false, vertices_357), by decide +kernel⟩
  | 22 => Sum.inr ⟨(false, vertices_677), by decide +kernel⟩
  | 23 => Sum.inl 2
  | 24 => Sum.inr ⟨(false, vertices_617), by decide +kernel⟩
  | 25 => Sum.inl 3
  | 26 => Sum.inr ⟨(false, vertices_849), by decide +kernel⟩
  | 27 => Sum.inl 4
  | 28 => Sum.inl 5
  | 29 => Sum.inl 6
  | 30 => Sum.inl 7
  | 31 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 2 6 7 398 134 2
cert_row_4 1 3 4 5 6 7 496 208 1
cert_row_4 2 0 2 3 5 8 602 26 3
cert_row_4 3 0 2 4 6 8 682 138 2
cert_rows
cert_pivot_2 1 7 3 0
cert_heightProof 4
cert_coverFacet 0 398
cert_cover_5 0 0 0 1 2 6 134 398 2
cert_coverFacet 1 646
cert_cover_2 1 1 0 6 8 134 646 3
cert_coverFacet 2 602
cert_cover_5 2 2 0 2 3 5 26 602 3
cert_coverFacet 3 282
cert_cover_2 3 2 0 3 7 26 282 3
cert_coverFacet 4 682
cert_cover_5 4 3 0 2 4 6 138 682 2
cert_coverFacet 5 420
cert_cover_2 5 4 1 6 7 164 420 3
cert_coverFacet 6 216
cert_cover_2 6 3 2 5 6 88 216 3
cert_coverFacet 7 408
cert_cover_2 7 3 2 6 7 152 408 3
cert_coverFacet 8 232
cert_cover_2 8 4 2 5 6 104 232 3
cert_coverFacet 9 496
cert_cover_5 9 1 3 4 5 6 208 496 1
cert_coveringFacets_5
cert_coveringProof
cert_certificate 4 10
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0348

end
end BundlePart3

section BundlePart4
/- Source: ProjectionCertificates/R_m16e10q1_0349.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0349

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [331, 677, 809, 713, 433, 449, 206, 654, 118, 534, 794, 338, 820, 228, 240, 464, 73, 265, 521, 161, 289, 545, 193, 321, 385, 641, 142, 22, 70, 518, 74, 266, 522, 82, 274, 530, 322, 52, 532, 100, 164, 548, 196, 644, 200, 648, 776, 112, 176, 304, 208, 336, 400, 784, 224, 800, 448]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_331, vertices_677, vertices_809, vertices_713, vertices_433, vertices_449, vertices_206, vertices_654, vertices_118, vertices_534, vertices_794, vertices_338, vertices_820, vertices_228, vertices_240, vertices_464] (by decide +kernel)
  polygons := literalFinset [vertices_73, vertices_265, vertices_521, vertices_161, vertices_289, vertices_545, vertices_193, vertices_321, vertices_385, vertices_641, vertices_142, vertices_22, vertices_70, vertices_518, vertices_74, vertices_266, vertices_522, vertices_82, vertices_274, vertices_530, vertices_322, vertices_52, vertices_532, vertices_100, vertices_164, vertices_548, vertices_196, vertices_644, vertices_200, vertices_648, vertices_776, vertices_112, vertices_176, vertices_304, vertices_208, vertices_336, vertices_400, vertices_784, vertices_224, vertices_800, vertices_448] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_331), (false, vertices_677), (false, vertices_809), (false, vertices_713), (false, vertices_433), (false, vertices_449), (true, vertices_142), (true, vertices_22), (true, vertices_70), (true, vertices_518), (true, vertices_522), (true, vertices_82), (true, vertices_274), (true, vertices_530), (true, vertices_52), (true, vertices_532), (true, vertices_100), (true, vertices_196), (true, vertices_112), (true, vertices_208), (true, vertices_336), (true, vertices_784), (true, vertices_224)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 17 20 22 25 27 28 29 30 31
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_331) then 18 else
  if p.val = (false, vertices_677) then 21 else
  if p.val = (false, vertices_809) then 23 else
  if p.val = (false, vertices_713) then 24 else
  if p.val = (false, vertices_433) then 26 else
  if p.val = (false, vertices_449) then 0 else
  if p.val = (true, vertices_142) then 19 else
  if p.val = (true, vertices_22) then 1 else
  if p.val = (true, vertices_70) then 2 else
  if p.val = (true, vertices_518) then 3 else
  if p.val = (true, vertices_522) then 4 else
  if p.val = (true, vertices_82) then 5 else
  if p.val = (true, vertices_274) then 6 else
  if p.val = (true, vertices_530) then 7 else
  if p.val = (true, vertices_52) then 8 else
  if p.val = (true, vertices_532) then 9 else
  if p.val = (true, vertices_100) then 10 else
  if p.val = (true, vertices_196) then 11 else
  if p.val = (true, vertices_112) then 12 else
  if p.val = (true, vertices_208) then 13 else
  if p.val = (true, vertices_336) then 14 else
  if p.val = (true, vertices_784) then 15 else
  if p.val = (true, vertices_224) then 16 else
  0
cert_priority
cert_nodeAtPriority_33 449 22 70 518 522 82 274 530 52 532 100 196 112 208 336 784 224 331 142 677 809 713 433
cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 1 2 6 142
cert_row_4 1 0 1 3 4 5 118 22 3
cert_row_4 2 0 2 3 7 8 794 266 2
cert_row_4 3 1 3 4 7 8 820 52 3
cert_rows
cert_pivot_2 6 5 0 1
cert_heightProof 4
cert_coverFacet 0 206
cert_cover_5 0 0 0 1 2 5 142 206 3
cert_coverFacet 1 654
cert_cover_5 1 0 0 1 2 8 142 654 3
cert_coverFacet 2 118
cert_cover_5 2 1 0 1 3 4 22 118 3
cert_coverFacet 3 534
cert_cover_2 3 1 0 3 8 22 534 3
cert_coverFacet 4 794
cert_cover_5 4 2 0 2 3 7 266 794 2
cert_coverFacet 5 338
cert_cover_2 5 3 0 5 7 82 338 3
cert_coverFacet 6 820
cert_cover_5 6 3 1 3 4 7 52 820 3
cert_coverFacet 7 228
cert_cover_2 7 4 1 5 6 100 228 3
cert_coverFacet 8 240
cert_cover_2 8 4 3 5 6 112 240 3
cert_coverFacet 9 464
cert_cover_2 9 5 3 6 7 208 464 3
cert_coveringFacets_5
cert_coveringProof
cert_certificate 4 10
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0349

end
end BundlePart4

section BundlePart5
/- Source: ProjectionCertificates/R_m16e10q1_0350.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0350

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [787, 837, 233, 689, 465, 609, 30, 46, 278, 614, 774, 666, 682, 412, 364, 456, 145, 273, 529, 97, 161, 545, 193, 321, 577, 769, 14, 22, 38, 262, 518, 26, 42, 650, 274, 530, 546, 770, 28, 44, 268, 276, 100, 324, 580, 772, 152, 104, 168, 200, 328, 392, 400, 656, 608, 672, 448]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_787, vertices_837, vertices_233, vertices_689, vertices_465, vertices_609, vertices_30, vertices_46, vertices_278, vertices_614, vertices_774, vertices_666, vertices_682, vertices_412, vertices_364, vertices_456] (by decide +kernel)
  polygons := literalFinset [vertices_145, vertices_273, vertices_529, vertices_97, vertices_161, vertices_545, vertices_193, vertices_321, vertices_577, vertices_769, vertices_14, vertices_22, vertices_38, vertices_262, vertices_518, vertices_26, vertices_42, vertices_650, vertices_274, vertices_530, vertices_546, vertices_770, vertices_28, vertices_44, vertices_268, vertices_276, vertices_100, vertices_324, vertices_580, vertices_772, vertices_152, vertices_104, vertices_168, vertices_200, vertices_328, vertices_392, vertices_400, vertices_656, vertices_608, vertices_672, vertices_448] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_787), (false, vertices_837), (false, vertices_233), (false, vertices_689), (false, vertices_465), (false, vertices_609), (true, vertices_14), (true, vertices_22), (true, vertices_38), (true, vertices_262), (true, vertices_518), (true, vertices_26), (true, vertices_42), (true, vertices_650), (true, vertices_546), (true, vertices_28), (true, vertices_44), (true, vertices_268), (true, vertices_276), (true, vertices_100), (true, vertices_152), (true, vertices_328), (true, vertices_392)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 17 20 22 24 27 28 29 30 31
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_787) then 18 else
  if p.val = (false, vertices_837) then 21 else
  if p.val = (false, vertices_233) then 23 else
  if p.val = (false, vertices_689) then 25 else
  if p.val = (false, vertices_465) then 26 else
  if p.val = (false, vertices_609) then 0 else
  if p.val = (true, vertices_14) then 1 else
  if p.val = (true, vertices_22) then 2 else
  if p.val = (true, vertices_38) then 3 else
  if p.val = (true, vertices_262) then 4 else
  if p.val = (true, vertices_518) then 5 else
  if p.val = (true, vertices_26) then 6 else
  if p.val = (true, vertices_42) then 7 else
  if p.val = (true, vertices_650) then 19 else
  if p.val = (true, vertices_546) then 8 else
  if p.val = (true, vertices_28) then 9 else
  if p.val = (true, vertices_44) then 10 else
  if p.val = (true, vertices_268) then 11 else
  if p.val = (true, vertices_276) then 12 else
  if p.val = (true, vertices_100) then 13 else
  if p.val = (true, vertices_152) then 14 else
  if p.val = (true, vertices_328) then 15 else
  if p.val = (true, vertices_392) then 16 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_609), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_14), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_22), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_38), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_262), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_518), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_26), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_42), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_546), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_28), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_44), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_268), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_276), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_100), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_152), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_328), by decide +kernel⟩
  | 16 => Sum.inr ⟨(true, vertices_392), by decide +kernel⟩
  | 17 => Sum.inl 0
  | 18 => Sum.inr ⟨(false, vertices_787), by decide +kernel⟩
  | 19 => Sum.inr ⟨(true, vertices_650), by decide +kernel⟩
  | 20 => Sum.inl 1
  | 21 => Sum.inr ⟨(false, vertices_837), by decide +kernel⟩
  | 22 => Sum.inl 2
  | 23 => Sum.inr ⟨(false, vertices_233), by decide +kernel⟩
  | 24 => Sum.inl 3
  | 25 => Sum.inr ⟨(false, vertices_689), by decide +kernel⟩
  | 26 => Sum.inr ⟨(false, vertices_465), by decide +kernel⟩
  | 27 => Sum.inl 4
  | 28 => Sum.inl 5
  | 29 => Sum.inl 6
  | 30 => Sum.inl 7
  | 31 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 1 2 3 6 7 412 28 3
cert_row_2 1 0 2 6 8 650
cert_row_4 2 0 1 4 5 8 614 38 3
cert_row_4 3 1 2 4 5 7 364 44 3
cert_rows
cert_pivot_2 3 6 0 1
cert_heightProof 4
cert_coverFacet 0 30
cert_cover_2 0 1 0 2 3 14 30 3
cert_coverFacet 1 46
cert_cover_2 1 1 0 2 4 14 46 3
cert_coverFacet 2 278
cert_cover_2 2 1 0 3 7 22 278 3
cert_coverFacet 3 614
cert_cover_5 3 2 0 1 4 5 38 614 3
cert_coverFacet 4 774
cert_cover_2 4 1 0 7 8 262 774 3
cert_coverFacet 5 666
cert_cover_5 5 1 0 2 3 6 26 666 3
cert_coverFacet 6 682
cert_cover_5 6 1 0 2 4 6 42 682 3
cert_coverFacet 7 412
cert_cover_5 7 0 1 2 3 6 28 412 3
cert_coverFacet 8 364
cert_cover_5 8 3 1 2 4 5 44 364 3
cert_coverFacet 9 456
cert_cover_2 9 5 2 6 7 200 456 3
cert_coveringFacets_5
cert_coveringProof
cert_certificate 4 10
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0350

end
end BundlePart5

section BundlePart6
/- Source: ProjectionCertificates/R_m16e10q1_0351.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0351

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [419, 597, 361, 689, 465, 609, 158, 526, 678, 410, 618, 298, 284, 844, 340, 660, 81, 145, 529, 97, 161, 289, 545, 321, 577, 385, 14, 134, 518, 154, 42, 266, 522, 162, 290, 546, 386, 28, 268, 524, 84, 148, 276, 532, 324, 580, 644, 280, 104, 296, 328, 584, 336, 400, 656, 608, 672]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_419, vertices_597, vertices_361, vertices_689, vertices_465, vertices_609, vertices_158, vertices_526, vertices_678, vertices_410, vertices_618, vertices_298, vertices_284, vertices_844, vertices_340, vertices_660] (by decide +kernel)
  polygons := literalFinset [vertices_81, vertices_145, vertices_529, vertices_97, vertices_161, vertices_289, vertices_545, vertices_321, vertices_577, vertices_385, vertices_14, vertices_134, vertices_518, vertices_154, vertices_42, vertices_266, vertices_522, vertices_162, vertices_290, vertices_546, vertices_386, vertices_28, vertices_268, vertices_524, vertices_84, vertices_148, vertices_276, vertices_532, vertices_324, vertices_580, vertices_644, vertices_280, vertices_104, vertices_296, vertices_328, vertices_584, vertices_336, vertices_400, vertices_656, vertices_608, vertices_672] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_419), (false, vertices_597), (false, vertices_361), (false, vertices_689), (false, vertices_465), (false, vertices_609), (true, vertices_14), (true, vertices_134), (true, vertices_518), (true, vertices_154), (true, vertices_42), (true, vertices_266), (true, vertices_522), (true, vertices_546), (true, vertices_28), (true, vertices_268), (true, vertices_524), (true, vertices_148), (true, vertices_276), (true, vertices_324), (true, vertices_644), (true, vertices_280), (true, vertices_584)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 17 20 22 24 27 28 29 30 31
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_419) then 18 else
  if p.val = (false, vertices_597) then 21 else
  if p.val = (false, vertices_361) then 23 else
  if p.val = (false, vertices_689) then 25 else
  if p.val = (false, vertices_465) then 26 else
  if p.val = (false, vertices_609) then 0 else
  if p.val = (true, vertices_14) then 1 else
  if p.val = (true, vertices_134) then 2 else
  if p.val = (true, vertices_518) then 3 else
  if p.val = (true, vertices_154) then 19 else
  if p.val = (true, vertices_42) then 4 else
  if p.val = (true, vertices_266) then 5 else
  if p.val = (true, vertices_522) then 6 else
  if p.val = (true, vertices_546) then 7 else
  if p.val = (true, vertices_28) then 8 else
  if p.val = (true, vertices_268) then 9 else
  if p.val = (true, vertices_524) then 10 else
  if p.val = (true, vertices_148) then 11 else
  if p.val = (true, vertices_276) then 12 else
  if p.val = (true, vertices_324) then 13 else
  if p.val = (true, vertices_644) then 14 else
  if p.val = (true, vertices_280) then 15 else
  if p.val = (true, vertices_584) then 16 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_609), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_14), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_134), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_518), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_42), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_266), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_522), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_546), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_28), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_268), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_524), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_148), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_276), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_324), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_644), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_280), by decide +kernel⟩
  | 16 => Sum.inr ⟨(true, vertices_584), by decide +kernel⟩
  | 17 => Sum.inl 0
  | 18 => Sum.inr ⟨(false, vertices_419), by decide +kernel⟩
  | 19 => Sum.inr ⟨(true, vertices_154), by decide +kernel⟩
  | 20 => Sum.inl 1
  | 21 => Sum.inr ⟨(false, vertices_597), by decide +kernel⟩
  | 22 => Sum.inl 2
  | 23 => Sum.inr ⟨(false, vertices_361), by decide +kernel⟩
  | 24 => Sum.inl 3
  | 25 => Sum.inr ⟨(false, vertices_689), by decide +kernel⟩
  | 26 => Sum.inr ⟨(false, vertices_465), by decide +kernel⟩
  | 27 => Sum.inl 4
  | 28 => Sum.inl 5
  | 29 => Sum.inl 6
  | 30 => Sum.inl 7
  | 31 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 2 3 6 154
cert_row_4 1 0 1 4 6 8 678 134 2
cert_row_4 2 0 2 4 5 8 618 42 3
cert_row_4 3 1 2 5 7 8 844 268 2
cert_rows
cert_pivot_2 3 6 0 1
cert_heightProof 4
cert_coverFacet 0 158
cert_cover_5 0 0 0 1 2 3 14 158 3
cert_coverFacet 1 526
cert_cover_2 1 1 0 2 8 14 526 3
cert_coverFacet 2 678
cert_cover_5 2 1 0 1 4 6 134 678 2
cert_coverFacet 3 410
cert_cover_5 3 0 0 2 3 7 154 410 3
cert_coverFacet 4 618
cert_cover_5 4 2 0 2 4 5 42 618 3
cert_coverFacet 5 298
cert_cover_2 5 2 0 4 7 42 298 3
cert_coverFacet 6 284
cert_cover_2 6 2 1 3 7 28 284 3
cert_coverFacet 7 844
cert_cover_5 7 3 1 2 5 7 268 844 2
cert_coverFacet 8 340
cert_cover_2 8 3 1 5 7 84 340 3
cert_coverFacet 9 660
cert_cover_2 9 3 1 6 8 148 660 3
cert_coveringFacets_5
cert_coveringProof
cert_certificate 4 10
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0351

end
end BundlePart6

section BundlePart7
/- Source: ProjectionCertificates/R_m16e10q1_0352.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0352

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [419, 661, 361, 625, 465, 673, 158, 526, 678, 410, 618, 298, 284, 844, 340, 596, 81, 145, 529, 97, 161, 289, 545, 321, 385, 641, 14, 134, 518, 154, 42, 266, 522, 162, 290, 546, 386, 28, 268, 524, 84, 148, 276, 532, 324, 580, 644, 280, 104, 296, 328, 584, 336, 592, 400, 608, 672]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_419, vertices_661, vertices_361, vertices_625, vertices_465, vertices_673, vertices_158, vertices_526, vertices_678, vertices_410, vertices_618, vertices_298, vertices_284, vertices_844, vertices_340, vertices_596] (by decide +kernel)
  polygons := literalFinset [vertices_81, vertices_145, vertices_529, vertices_97, vertices_161, vertices_289, vertices_545, vertices_321, vertices_385, vertices_641, vertices_14, vertices_134, vertices_518, vertices_154, vertices_42, vertices_266, vertices_522, vertices_162, vertices_290, vertices_546, vertices_386, vertices_28, vertices_268, vertices_524, vertices_84, vertices_148, vertices_276, vertices_532, vertices_324, vertices_580, vertices_644, vertices_280, vertices_104, vertices_296, vertices_328, vertices_584, vertices_336, vertices_592, vertices_400, vertices_608, vertices_672] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_419), (false, vertices_661), (false, vertices_361), (false, vertices_625), (false, vertices_465), (false, vertices_673), (true, vertices_14), (true, vertices_134), (true, vertices_518), (true, vertices_154), (true, vertices_42), (true, vertices_266), (true, vertices_522), (true, vertices_546), (true, vertices_28), (true, vertices_268), (true, vertices_524), (true, vertices_84), (true, vertices_276), (true, vertices_324), (true, vertices_580), (true, vertices_280), (true, vertices_584)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 17 20 22 24 27 28 29 30 31
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_419) then 18 else
  if p.val = (false, vertices_661) then 21 else
  if p.val = (false, vertices_361) then 23 else
  if p.val = (false, vertices_625) then 25 else
  if p.val = (false, vertices_465) then 26 else
  if p.val = (false, vertices_673) then 0 else
  if p.val = (true, vertices_14) then 1 else
  if p.val = (true, vertices_134) then 2 else
  if p.val = (true, vertices_518) then 3 else
  if p.val = (true, vertices_154) then 19 else
  if p.val = (true, vertices_42) then 4 else
  if p.val = (true, vertices_266) then 5 else
  if p.val = (true, vertices_522) then 6 else
  if p.val = (true, vertices_546) then 7 else
  if p.val = (true, vertices_28) then 8 else
  if p.val = (true, vertices_268) then 9 else
  if p.val = (true, vertices_524) then 10 else
  if p.val = (true, vertices_84) then 11 else
  if p.val = (true, vertices_276) then 12 else
  if p.val = (true, vertices_324) then 13 else
  if p.val = (true, vertices_580) then 14 else
  if p.val = (true, vertices_280) then 15 else
  if p.val = (true, vertices_584) then 16 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_673), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_14), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_134), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_518), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_42), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_266), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_522), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_546), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_28), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_268), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_524), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_84), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_276), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_324), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_580), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_280), by decide +kernel⟩
  | 16 => Sum.inr ⟨(true, vertices_584), by decide +kernel⟩
  | 17 => Sum.inl 0
  | 18 => Sum.inr ⟨(false, vertices_419), by decide +kernel⟩
  | 19 => Sum.inr ⟨(true, vertices_154), by decide +kernel⟩
  | 20 => Sum.inl 1
  | 21 => Sum.inr ⟨(false, vertices_661), by decide +kernel⟩
  | 22 => Sum.inl 2
  | 23 => Sum.inr ⟨(false, vertices_361), by decide +kernel⟩
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
cert_row_2 0 0 2 3 6 154
cert_row_4 1 0 1 4 6 8 678 134 2
cert_row_4 2 0 2 4 5 8 618 42 3
cert_row_4 3 1 2 5 7 8 844 268 2
cert_rows
cert_pivot_2 3 6 0 1
cert_heightProof 4
cert_coverFacet 0 158
cert_cover_5 0 0 0 1 2 3 14 158 3
cert_coverFacet 1 526
cert_cover_2 1 1 0 2 8 14 526 3
cert_coverFacet 2 678
cert_cover_5 2 1 0 1 4 6 134 678 2
cert_coverFacet 3 410
cert_cover_5 3 0 0 2 3 7 154 410 3
cert_coverFacet 4 618
cert_cover_5 4 2 0 2 4 5 42 618 3
cert_coverFacet 5 298
cert_cover_2 5 2 0 4 7 42 298 3
cert_coverFacet 6 284
cert_cover_2 6 2 1 3 7 28 284 3
cert_coverFacet 7 844
cert_cover_5 7 3 1 2 5 7 268 844 2
cert_coverFacet 8 340
cert_cover_2 8 3 1 5 7 84 340 3
cert_coverFacet 9 596
cert_cover_2 9 3 1 5 8 84 596 3
cert_coveringFacets_5
cert_coveringProof
cert_certificate 4 10
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0352

end
end BundlePart7

section BundlePart8
/- Source: ProjectionCertificates/R_m16e10q1_0353.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0353

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [451, 613, 569, 425, 713, 353, 214, 278, 358, 906, 658, 786, 316, 564, 724, 792, 41, 137, 521, 97, 289, 545, 193, 321, 577, 385, 22, 70, 262, 146, 274, 530, 194, 322, 386, 642, 770, 52, 212, 276, 532, 100, 292, 548, 580, 56, 280, 536, 296, 392, 648, 776, 560, 656, 784, 352, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_451, vertices_613, vertices_569, vertices_425, vertices_713, vertices_353, vertices_214, vertices_278, vertices_358, vertices_906, vertices_658, vertices_786, vertices_316, vertices_564, vertices_724, vertices_792] (by decide +kernel)
  polygons := literalFinset [vertices_41, vertices_137, vertices_521, vertices_97, vertices_289, vertices_545, vertices_193, vertices_321, vertices_577, vertices_385, vertices_22, vertices_70, vertices_262, vertices_146, vertices_274, vertices_530, vertices_194, vertices_322, vertices_386, vertices_642, vertices_770, vertices_52, vertices_212, vertices_276, vertices_532, vertices_100, vertices_292, vertices_548, vertices_580, vertices_56, vertices_280, vertices_536, vertices_296, vertices_392, vertices_648, vertices_776, vertices_560, vertices_656, vertices_784, vertices_352, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_451), (false, vertices_613), (false, vertices_569), (false, vertices_425), (false, vertices_713), (false, vertices_353), (true, vertices_22), (true, vertices_70), (true, vertices_262), (true, vertices_146), (true, vertices_274), (true, vertices_530), (true, vertices_642), (true, vertices_770), (true, vertices_52), (true, vertices_212), (true, vertices_276), (true, vertices_532), (true, vertices_292), (true, vertices_280), (true, vertices_776), (true, vertices_656), (true, vertices_784)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 17 19 22 26 27 28 29 30 31
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_451) then 18 else
  if p.val = (false, vertices_613) then 20 else
  if p.val = (false, vertices_569) then 23 else
  if p.val = (false, vertices_425) then 24 else
  if p.val = (false, vertices_713) then 25 else
  if p.val = (false, vertices_353) then 0 else
  if p.val = (true, vertices_22) then 1 else
  if p.val = (true, vertices_70) then 2 else
  if p.val = (true, vertices_262) then 3 else
  if p.val = (true, vertices_146) then 4 else
  if p.val = (true, vertices_274) then 5 else
  if p.val = (true, vertices_530) then 6 else
  if p.val = (true, vertices_642) then 7 else
  if p.val = (true, vertices_770) then 8 else
  if p.val = (true, vertices_52) then 9 else
  if p.val = (true, vertices_212) then 21 else
  if p.val = (true, vertices_276) then 10 else
  if p.val = (true, vertices_532) then 11 else
  if p.val = (true, vertices_292) then 12 else
  if p.val = (true, vertices_280) then 13 else
  if p.val = (true, vertices_776) then 14 else
  if p.val = (true, vertices_656) then 15 else
  if p.val = (true, vertices_784) then 16 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_353), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_22), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_70), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_262), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_146), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_274), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_530), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_642), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_770), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_52), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_276), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_532), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_292), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_280), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_776), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_656), by decide +kernel⟩
  | 16 => Sum.inr ⟨(true, vertices_784), by decide +kernel⟩
  | 17 => Sum.inl 0
  | 18 => Sum.inr ⟨(false, vertices_451), by decide +kernel⟩
  | 19 => Sum.inl 1
  | 20 => Sum.inr ⟨(false, vertices_613), by decide +kernel⟩
  | 21 => Sum.inr ⟨(true, vertices_212), by decide +kernel⟩
  | 22 => Sum.inl 2
  | 23 => Sum.inr ⟨(false, vertices_569), by decide +kernel⟩
  | 24 => Sum.inr ⟨(false, vertices_425), by decide +kernel⟩
  | 25 => Sum.inr ⟨(false, vertices_713), by decide +kernel⟩
  | 26 => Sum.inl 3
  | 27 => Sum.inl 4
  | 28 => Sum.inl 5
  | 29 => Sum.inl 6
  | 30 => Sum.inl 7
  | 31 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 2 6 7 8 906 386 1
cert_row_2 1 1 3 5 6 212
cert_row_4 2 0 1 4 5 7 358 70 2
cert_row_4 3 1 2 3 4 7 316 52 1
cert_rows
cert_pivot_2 8 6 0 1
cert_heightProof 4
cert_coverFacet 0 214
cert_cover_5 0 1 0 1 3 5 22 214 3
cert_coverFacet 1 278
cert_cover_2 1 1 0 3 7 22 278 3
cert_coverFacet 2 358
cert_cover_5 2 2 0 1 4 5 70 358 2
cert_coverFacet 3 906
cert_cover_5 3 0 0 2 6 7 386 906 1
cert_coverFacet 4 658
cert_cover_2 4 3 0 6 8 146 658 3
cert_coverFacet 5 786
cert_cover_2 5 3 0 7 8 274 786 3
cert_coverFacet 6 316
cert_cover_5 6 3 1 2 3 4 52 316 1
cert_coverFacet 7 564
cert_cover_2 7 3 1 4 8 52 564 3
cert_coverFacet 8 724
cert_cover_5 8 1 1 3 5 8 212 724 3
cert_coverFacet 9 792
cert_cover_2 9 3 2 7 8 280 792 3
cert_coveringFacets_5
cert_coveringProof
cert_certificate 4 10
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0353

end
end BundlePart8

section BundlePart9
/- Source: ProjectionCertificates/R_m16e10q1_0354.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0354

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [675, 557, 77, 709, 345, 297, 481, 662, 810, 242, 370, 786, 220, 284, 780, 788, 13, 69, 517, 41, 73, 265, 161, 289, 545, 193, 321, 641, 114, 146, 274, 530, 162, 290, 546, 642, 770, 28, 76, 268, 524, 148, 276, 532, 196, 644, 772, 88, 280, 296, 552, 776, 208, 336, 784, 224, 352]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_675, vertices_557, vertices_77, vertices_709, vertices_345, vertices_297, vertices_481, vertices_662, vertices_810, vertices_242, vertices_370, vertices_786, vertices_220, vertices_284, vertices_780, vertices_788] (by decide +kernel)
  polygons := literalFinset [vertices_13, vertices_69, vertices_517, vertices_41, vertices_73, vertices_265, vertices_161, vertices_289, vertices_545, vertices_193, vertices_321, vertices_641, vertices_114, vertices_146, vertices_274, vertices_530, vertices_162, vertices_290, vertices_546, vertices_642, vertices_770, vertices_28, vertices_76, vertices_268, vertices_524, vertices_148, vertices_276, vertices_532, vertices_196, vertices_644, vertices_772, vertices_88, vertices_280, vertices_296, vertices_552, vertices_776, vertices_208, vertices_336, vertices_784, vertices_224, vertices_352] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_675), (false, vertices_557), (false, vertices_77), (false, vertices_709), (false, vertices_345), (false, vertices_297), (false, vertices_481), (true, vertices_114), (true, vertices_146), (true, vertices_274), (true, vertices_530), (true, vertices_290), (true, vertices_770), (true, vertices_28), (true, vertices_268), (true, vertices_148), (true, vertices_276), (true, vertices_532), (true, vertices_772), (true, vertices_776), (true, vertices_208), (true, vertices_784)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 16 19 22 24 25 27 28 29 30
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_675) then 17 else
  if p.val = (false, vertices_557) then 20 else
  if p.val = (false, vertices_77) then 0 else
  if p.val = (false, vertices_709) then 21 else
  if p.val = (false, vertices_345) then 23 else
  if p.val = (false, vertices_297) then 1 else
  if p.val = (false, vertices_481) then 26 else
  if p.val = (true, vertices_114) then 18 else
  if p.val = (true, vertices_146) then 2 else
  if p.val = (true, vertices_274) then 3 else
  if p.val = (true, vertices_530) then 4 else
  if p.val = (true, vertices_290) then 5 else
  if p.val = (true, vertices_770) then 6 else
  if p.val = (true, vertices_28) then 7 else
  if p.val = (true, vertices_268) then 8 else
  if p.val = (true, vertices_148) then 9 else
  if p.val = (true, vertices_276) then 10 else
  if p.val = (true, vertices_532) then 11 else
  if p.val = (true, vertices_772) then 12 else
  if p.val = (true, vertices_776) then 13 else
  if p.val = (true, vertices_208) then 14 else
  if p.val = (true, vertices_784) then 15 else
  0
cert_priority
cert_nodeAtPriority_24 1 77 0 297 146 274 530 290 770 28 268 148 276 532 772 776 208 784 675 114 557 709 345 481
cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 2 4 7 8 810 290 1
cert_row_2 1 0 3 4 5 114
cert_row_4 2 0 1 3 6 8 662 146 1
cert_row_4 3 1 2 3 5 6 220 28 3
cert_rows
cert_pivot_2 7 4 0 1
cert_heightProof 4
cert_coverFacet 0 662
cert_cover_5 0 2 0 1 3 6 146 662 1
cert_coverFacet 1 810
cert_cover_5 1 0 0 2 4 7 290 810 1
cert_coverFacet 2 242
cert_cover_5 2 1 0 3 4 6 114 242 3
cert_coverFacet 3 370
cert_cover_5 3 1 0 3 4 7 114 370 3
cert_coverFacet 4 786
cert_cover_2 4 3 0 7 8 274 786 3
cert_coverFacet 5 220
cert_cover_5 5 3 1 2 3 5 28 220 3
cert_coverFacet 6 284
cert_cover_2 6 2 1 3 7 28 284 3
cert_coverFacet 7 780
cert_cover_2 7 2 1 7 8 268 780 3
cert_coverFacet 8 788
cert_cover_2 8 3 1 7 8 276 788 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0354

end
end BundlePart9

section BundlePart10
/- Source: ProjectionCertificates/R_m16e10q1_0355.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0355

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [651, 355, 547, 451, 557, 205, 117, 806, 914, 92, 284, 780, 308, 728, 792, 496, 35, 323, 131, 515, 13, 37, 69, 137, 521, 97, 545, 193, 290, 546, 386, 642, 770, 28, 76, 268, 524, 52, 84, 276, 292, 548, 772, 88, 280, 536, 200, 648, 776, 112, 304, 208, 400, 656, 784, 352, 448]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_651, vertices_355, vertices_547, vertices_451, vertices_557, vertices_205, vertices_117, vertices_806, vertices_914, vertices_92, vertices_284, vertices_780, vertices_308, vertices_728, vertices_792, vertices_496] (by decide +kernel)
  polygons := literalFinset [vertices_35, vertices_323, vertices_131, vertices_515, vertices_13, vertices_37, vertices_69, vertices_137, vertices_521, vertices_97, vertices_545, vertices_193, vertices_290, vertices_546, vertices_386, vertices_642, vertices_770, vertices_28, vertices_76, vertices_268, vertices_524, vertices_52, vertices_84, vertices_276, vertices_292, vertices_548, vertices_772, vertices_88, vertices_280, vertices_536, vertices_200, vertices_648, vertices_776, vertices_112, vertices_304, vertices_208, vertices_400, vertices_656, vertices_784, vertices_352, vertices_448] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_651), (false, vertices_355), (false, vertices_547), (false, vertices_451), (false, vertices_557), (false, vertices_205), (false, vertices_117), (true, vertices_770), (true, vertices_28), (true, vertices_268), (true, vertices_276), (true, vertices_292), (true, vertices_772), (true, vertices_88), (true, vertices_280), (true, vertices_536), (true, vertices_776), (true, vertices_304), (true, vertices_208), (true, vertices_400), (true, vertices_656), (true, vertices_784)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 16 20 24 25 26 27 28 29 30
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_651) then 17 else
  if p.val = (false, vertices_355) then 18 else
  if p.val = (false, vertices_547) then 0 else
  if p.val = (false, vertices_451) then 19 else
  if p.val = (false, vertices_557) then 21 else
  if p.val = (false, vertices_205) then 22 else
  if p.val = (false, vertices_117) then 23 else
  if p.val = (true, vertices_770) then 1 else
  if p.val = (true, vertices_28) then 2 else
  if p.val = (true, vertices_268) then 3 else
  if p.val = (true, vertices_276) then 4 else
  if p.val = (true, vertices_292) then 5 else
  if p.val = (true, vertices_772) then 6 else
  if p.val = (true, vertices_88) then 7 else
  if p.val = (true, vertices_280) then 8 else
  if p.val = (true, vertices_536) then 9 else
  if p.val = (true, vertices_776) then 10 else
  if p.val = (true, vertices_304) then 11 else
  if p.val = (true, vertices_208) then 12 else
  if p.val = (true, vertices_400) then 13 else
  if p.val = (true, vertices_656) then 14 else
  if p.val = (true, vertices_784) then 15 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_547), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_770), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_28), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_268), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_276), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_292), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_772), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_88), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_280), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_536), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_776), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_304), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_208), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_400), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_656), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_784), by decide +kernel⟩
  | 16 => Sum.inl 0
  | 17 => Sum.inr ⟨(false, vertices_651), by decide +kernel⟩
  | 18 => Sum.inr ⟨(false, vertices_355), by decide +kernel⟩
  | 19 => Sum.inr ⟨(false, vertices_451), by decide +kernel⟩
  | 20 => Sum.inl 1
  | 21 => Sum.inr ⟨(false, vertices_557), by decide +kernel⟩
  | 22 => Sum.inr ⟨(false, vertices_205), by decide +kernel⟩
  | 23 => Sum.inr ⟨(false, vertices_117), by decide +kernel⟩
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
cert_row_4 0 0 1 4 7 8 806 290 1
cert_row_4 1 0 3 6 7 8 914 386 1
cert_row_4 2 2 3 5 6 8 728 88 3
cert_row_4 3 3 4 5 6 7 496 112 3
cert_rows
cert_pivot_2 1 0 2 3
cert_heightProof 4
cert_coverFacet 0 806
cert_cover_5 0 0 0 1 4 7 290 806 1
cert_coverFacet 1 914
cert_cover_5 1 1 0 3 6 7 386 914 1
cert_coverFacet 2 92
cert_cover_2 2 2 1 3 5 28 92 3
cert_coverFacet 3 284
cert_cover_2 3 2 1 3 7 28 284 3
cert_coverFacet 4 780
cert_cover_2 4 2 1 7 8 268 780 3
cert_coverFacet 5 308
cert_cover_2 5 3 1 4 7 52 308 3
cert_coverFacet 6 728
cert_cover_5 6 2 2 3 5 6 88 728 3
cert_coverFacet 7 792
cert_cover_2 7 3 2 7 8 280 792 3
cert_coverFacet 8 496
cert_cover_5 8 3 3 4 5 6 112 496 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0355

end
end BundlePart10

section BundlePart11
/- Source: ProjectionCertificates/R_m16e10q1_0356.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0356

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [675, 805, 793, 721, 337, 481, 110, 270, 550, 774, 666, 234, 778, 220, 284, 372, 81, 273, 529, 161, 289, 545, 193, 321, 641, 769, 14, 38, 262, 518, 106, 138, 266, 522, 162, 546, 642, 770, 28, 76, 268, 84, 276, 100, 292, 548, 772, 152, 280, 536, 200, 776, 208, 336, 656, 224, 352]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_675, vertices_805, vertices_793, vertices_721, vertices_337, vertices_481, vertices_110, vertices_270, vertices_550, vertices_774, vertices_666, vertices_234, vertices_778, vertices_220, vertices_284, vertices_372] (by decide +kernel)
  polygons := literalFinset [vertices_81, vertices_273, vertices_529, vertices_161, vertices_289, vertices_545, vertices_193, vertices_321, vertices_641, vertices_769, vertices_14, vertices_38, vertices_262, vertices_518, vertices_106, vertices_138, vertices_266, vertices_522, vertices_162, vertices_546, vertices_642, vertices_770, vertices_28, vertices_76, vertices_268, vertices_84, vertices_276, vertices_100, vertices_292, vertices_548, vertices_772, vertices_152, vertices_280, vertices_536, vertices_200, vertices_776, vertices_208, vertices_336, vertices_656, vertices_224, vertices_352] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_675), (false, vertices_805), (false, vertices_793), (false, vertices_721), (false, vertices_337), (false, vertices_481), (true, vertices_14), (true, vertices_38), (true, vertices_262), (true, vertices_518), (true, vertices_106), (true, vertices_138), (true, vertices_266), (true, vertices_522), (true, vertices_770), (true, vertices_28), (true, vertices_76), (true, vertices_268), (true, vertices_84), (true, vertices_276), (true, vertices_100), (true, vertices_152), (true, vertices_200)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 17 20 22 24 26 28 29 30 31
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_675) then 18 else
  if p.val = (false, vertices_805) then 21 else
  if p.val = (false, vertices_793) then 23 else
  if p.val = (false, vertices_721) then 25 else
  if p.val = (false, vertices_337) then 0 else
  if p.val = (false, vertices_481) then 27 else
  if p.val = (true, vertices_14) then 1 else
  if p.val = (true, vertices_38) then 2 else
  if p.val = (true, vertices_262) then 3 else
  if p.val = (true, vertices_518) then 4 else
  if p.val = (true, vertices_106) then 19 else
  if p.val = (true, vertices_138) then 5 else
  if p.val = (true, vertices_266) then 6 else
  if p.val = (true, vertices_522) then 7 else
  if p.val = (true, vertices_770) then 8 else
  if p.val = (true, vertices_28) then 9 else
  if p.val = (true, vertices_76) then 10 else
  if p.val = (true, vertices_268) then 11 else
  if p.val = (true, vertices_84) then 12 else
  if p.val = (true, vertices_276) then 13 else
  if p.val = (true, vertices_100) then 14 else
  if p.val = (true, vertices_152) then 15 else
  if p.val = (true, vertices_200) then 16 else
  0
cert_priority
cert_nodeAtPriority_66 337 14 38 262 518 138 266 522 770 28 76 268 84 276 100 152 200 675 106 805 793 721 481
cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 2 3 6 8 666 138 2
cert_row_2 1 0 2 4 5 106
cert_row_4 2 1 2 3 5 6 220 28 3
cert_row_4 3 1 3 4 5 7 372 84 2
cert_rows
cert_pivot_2 8 0 2 1
cert_heightProof 4
cert_coverFacet 0 110
cert_cover_5 0 1 0 1 2 4 14 110 3
cert_coverFacet 1 270
cert_cover_2 1 1 0 2 7 14 270 3
cert_coverFacet 2 550
cert_cover_2 2 1 0 4 8 38 550 3
cert_coverFacet 3 774
cert_cover_2 3 1 0 7 8 262 774 3
cert_coverFacet 4 666
cert_cover_5 4 0 0 2 3 6 138 666 2
cert_coverFacet 5 234
cert_cover_5 5 1 0 2 4 6 106 234 3
cert_coverFacet 6 778
cert_cover_2 6 2 0 7 8 266 778 3
cert_coverFacet 7 220
cert_cover_5 7 2 1 2 3 5 28 220 3
cert_coverFacet 8 284
cert_cover_2 8 2 1 3 7 28 284 3
cert_coverFacet 9 372
cert_cover_5 9 3 1 3 4 5 84 372 2
cert_coveringFacets_5
cert_coveringProof
cert_certificate 4 10
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0356

end
end BundlePart11

section BundlePart12
/- Source: ProjectionCertificates/R_m16e10q1_0357.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0357

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [775, 651, 179, 275, 425, 777, 369, 214, 278, 710, 348, 620, 780, 360, 680, 752, 19, 131, 259, 515, 137, 265, 521, 49, 273, 161, 289, 769, 22, 198, 262, 518, 146, 274, 642, 76, 268, 524, 84, 276, 580, 772, 104, 168, 296, 552, 328, 648, 776, 112, 176, 208, 336, 352, 608, 672, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_775, vertices_651, vertices_179, vertices_275, vertices_425, vertices_777, vertices_369, vertices_214, vertices_278, vertices_710, vertices_348, vertices_620, vertices_780, vertices_360, vertices_680, vertices_752] (by decide +kernel)
  polygons := literalFinset [vertices_19, vertices_131, vertices_259, vertices_515, vertices_137, vertices_265, vertices_521, vertices_49, vertices_273, vertices_161, vertices_289, vertices_769, vertices_22, vertices_198, vertices_262, vertices_518, vertices_146, vertices_274, vertices_642, vertices_76, vertices_268, vertices_524, vertices_84, vertices_276, vertices_580, vertices_772, vertices_104, vertices_168, vertices_296, vertices_552, vertices_328, vertices_648, vertices_776, vertices_112, vertices_176, vertices_208, vertices_336, vertices_352, vertices_608, vertices_672, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_775), (false, vertices_651), (false, vertices_179), (false, vertices_275), (false, vertices_425), (false, vertices_777), (false, vertices_369), (true, vertices_22), (true, vertices_198), (true, vertices_76), (true, vertices_268), (true, vertices_524), (true, vertices_84), (true, vertices_276), (true, vertices_580), (true, vertices_104), (true, vertices_552), (true, vertices_328), (true, vertices_208), (true, vertices_608), (true, vertices_672), (true, vertices_704)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 19 16 22 24 26 27 28 29 30
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_775) then 17 else
  if p.val = (false, vertices_651) then 20 else
  if p.val = (false, vertices_179) then 21 else
  if p.val = (false, vertices_275) then 0 else
  if p.val = (false, vertices_425) then 23 else
  if p.val = (false, vertices_777) then 1 else
  if p.val = (false, vertices_369) then 25 else
  if p.val = (true, vertices_22) then 2 else
  if p.val = (true, vertices_198) then 18 else
  if p.val = (true, vertices_76) then 3 else
  if p.val = (true, vertices_268) then 4 else
  if p.val = (true, vertices_524) then 5 else
  if p.val = (true, vertices_84) then 6 else
  if p.val = (true, vertices_276) then 7 else
  if p.val = (true, vertices_580) then 8 else
  if p.val = (true, vertices_104) then 9 else
  if p.val = (true, vertices_552) then 10 else
  if p.val = (true, vertices_328) then 11 else
  if p.val = (true, vertices_208) then 12 else
  if p.val = (true, vertices_608) then 13 else
  if p.val = (true, vertices_672) then 14 else
  if p.val = (true, vertices_704) then 15 else
  0
cert_priority
cert_nodeAtPriority_50 0 275 1 777 22 76 268 524 84 276 580 104 552 328 208 608 672 704 775 198 651 179 425 369
cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 1 5 6 198
cert_row_4 1 1 2 3 5 7 348 76 2
cert_row_4 2 1 2 4 5 8 620 76 2
cert_row_4 3 3 4 5 6 8 752 112 3
cert_rows
cert_pivot_2 0 7 1 3
cert_heightProof 4
cert_coverFacet 0 214
cert_cover_5 0 0 0 1 3 5 22 214 3
cert_coverFacet 1 278
cert_cover_2 1 1 0 3 7 22 278 3
cert_coverFacet 2 710
cert_cover_5 2 0 0 1 5 8 198 710 3
cert_coverFacet 3 348
cert_cover_5 3 1 1 2 3 5 76 348 2
cert_coverFacet 4 620
cert_cover_5 4 2 1 2 4 5 76 620 2
cert_coverFacet 5 780
cert_cover_2 5 2 1 7 8 268 780 3
cert_coverFacet 6 360
cert_cover_2 6 4 2 5 7 104 360 3
cert_coverFacet 7 680
cert_cover_2 7 4 2 6 8 168 680 3
cert_coverFacet 8 752
cert_cover_5 8 3 3 4 5 6 112 752 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0357

end
end BundlePart12

section BundlePart13
/- Source: ProjectionCertificates/R_m16e10q1_0358.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0358

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [675, 285, 557, 709, 325, 361, 225, 30, 526, 534, 410, 426, 554, 722, 852, 496, 13, 69, 261, 517, 41, 265, 97, 161, 545, 193, 321, 641, 14, 22, 518, 26, 42, 394, 522, 146, 530, 162, 546, 642, 28, 524, 276, 532, 324, 580, 280, 296, 552, 208, 336, 592, 400, 224, 352, 416, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_675, vertices_285, vertices_557, vertices_709, vertices_325, vertices_361, vertices_225, vertices_30, vertices_526, vertices_534, vertices_410, vertices_426, vertices_554, vertices_722, vertices_852, vertices_496] (by decide +kernel)
  polygons := literalFinset [vertices_13, vertices_69, vertices_261, vertices_517, vertices_41, vertices_265, vertices_97, vertices_161, vertices_545, vertices_193, vertices_321, vertices_641, vertices_14, vertices_22, vertices_518, vertices_26, vertices_42, vertices_394, vertices_522, vertices_146, vertices_530, vertices_162, vertices_546, vertices_642, vertices_28, vertices_524, vertices_276, vertices_532, vertices_324, vertices_580, vertices_280, vertices_296, vertices_552, vertices_208, vertices_336, vertices_592, vertices_400, vertices_224, vertices_352, vertices_416, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_675), (false, vertices_285), (false, vertices_557), (false, vertices_709), (false, vertices_325), (false, vertices_361), (false, vertices_225), (true, vertices_14), (true, vertices_22), (true, vertices_518), (true, vertices_26), (true, vertices_42), (true, vertices_394), (true, vertices_522), (true, vertices_146), (true, vertices_530), (true, vertices_532), (true, vertices_208), (true, vertices_336), (true, vertices_592), (true, vertices_400), (true, vertices_416)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 16 19 23 25 26 27 28 29 30
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_675) then 17 else
  if p.val = (false, vertices_285) then 20 else
  if p.val = (false, vertices_557) then 21 else
  if p.val = (false, vertices_709) then 22 else
  if p.val = (false, vertices_325) then 0 else
  if p.val = (false, vertices_361) then 24 else
  if p.val = (false, vertices_225) then 1 else
  if p.val = (true, vertices_14) then 2 else
  if p.val = (true, vertices_22) then 3 else
  if p.val = (true, vertices_518) then 4 else
  if p.val = (true, vertices_26) then 5 else
  if p.val = (true, vertices_42) then 6 else
  if p.val = (true, vertices_394) then 18 else
  if p.val = (true, vertices_522) then 7 else
  if p.val = (true, vertices_146) then 8 else
  if p.val = (true, vertices_530) then 9 else
  if p.val = (true, vertices_532) then 10 else
  if p.val = (true, vertices_208) then 11 else
  if p.val = (true, vertices_336) then 12 else
  if p.val = (true, vertices_592) then 13 else
  if p.val = (true, vertices_400) then 14 else
  if p.val = (true, vertices_416) then 15 else
  0
cert_priority
cert_nodeAtPriority_5 0 325 1 225 14 22 518 26 42 522 146 530 532 208 336 592 400 416 675 394 285 557 709 361
cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 2 6 7 394
cert_row_4 1 0 3 5 6 8 722 146 2
cert_row_4 2 1 3 5 7 8 852 276 2
cert_row_4 3 3 4 5 6 7 496 208 1
cert_rows
cert_pivot_2 2 0 1 3
cert_heightProof 4
cert_coverFacet 0 30
cert_cover_2 0 1 0 2 3 14 30 3
cert_coverFacet 1 526
cert_cover_2 1 1 0 2 8 14 526 3
cert_coverFacet 2 534
cert_cover_2 2 1 0 3 8 22 534 3
cert_coverFacet 3 410
cert_cover_5 3 0 0 2 3 6 26 410 3
cert_coverFacet 4 426
cert_cover_5 4 0 0 2 4 6 42 426 3
cert_coverFacet 5 554
cert_cover_2 5 2 0 4 8 42 554 3
cert_coverFacet 6 722
cert_cover_5 6 1 0 3 5 6 146 722 2
cert_coverFacet 7 852
cert_cover_5 7 2 1 3 5 7 276 852 2
cert_coverFacet 8 496
cert_cover_5 8 3 3 4 5 6 208 496 1
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0358

end
end BundlePart13

section BundlePart14
/- Source: ProjectionCertificates/R_m16e10q1_0359.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0359

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [587, 805, 233, 905, 625, 417, 206, 270, 566, 214, 774, 778, 594, 412, 308, 496, 73, 137, 521, 97, 161, 289, 545, 577, 385, 769, 14, 22, 198, 262, 518, 74, 266, 522, 82, 530, 578, 770, 140, 268, 52, 148, 276, 292, 548, 772, 200, 392, 776, 112, 304, 560, 208, 592, 400, 224, 416]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_587, vertices_805, vertices_233, vertices_905, vertices_625, vertices_417, vertices_206, vertices_270, vertices_566, vertices_214, vertices_774, vertices_778, vertices_594, vertices_412, vertices_308, vertices_496] (by decide +kernel)
  polygons := literalFinset [vertices_73, vertices_137, vertices_521, vertices_97, vertices_161, vertices_289, vertices_545, vertices_577, vertices_385, vertices_769, vertices_14, vertices_22, vertices_198, vertices_262, vertices_518, vertices_74, vertices_266, vertices_522, vertices_82, vertices_530, vertices_578, vertices_770, vertices_140, vertices_268, vertices_52, vertices_148, vertices_276, vertices_292, vertices_548, vertices_772, vertices_200, vertices_392, vertices_776, vertices_112, vertices_304, vertices_560, vertices_208, vertices_592, vertices_400, vertices_224, vertices_416] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_587), (false, vertices_805), (false, vertices_233), (false, vertices_905), (false, vertices_625), (false, vertices_417), (true, vertices_14), (true, vertices_22), (true, vertices_198), (true, vertices_262), (true, vertices_518), (true, vertices_266), (true, vertices_82), (true, vertices_530), (true, vertices_770), (true, vertices_140), (true, vertices_268), (true, vertices_52), (true, vertices_148), (true, vertices_276), (true, vertices_304), (true, vertices_208), (true, vertices_400)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 17 20 22 25 27 28 29 30 31
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_587) then 18 else
  if p.val = (false, vertices_805) then 21 else
  if p.val = (false, vertices_233) then 23 else
  if p.val = (false, vertices_905) then 24 else
  if p.val = (false, vertices_625) then 26 else
  if p.val = (false, vertices_417) then 0 else
  if p.val = (true, vertices_14) then 1 else
  if p.val = (true, vertices_22) then 2 else
  if p.val = (true, vertices_198) then 19 else
  if p.val = (true, vertices_262) then 3 else
  if p.val = (true, vertices_518) then 4 else
  if p.val = (true, vertices_266) then 5 else
  if p.val = (true, vertices_82) then 6 else
  if p.val = (true, vertices_530) then 7 else
  if p.val = (true, vertices_770) then 8 else
  if p.val = (true, vertices_140) then 9 else
  if p.val = (true, vertices_268) then 10 else
  if p.val = (true, vertices_52) then 11 else
  if p.val = (true, vertices_148) then 12 else
  if p.val = (true, vertices_276) then 13 else
  if p.val = (true, vertices_304) then 14 else
  if p.val = (true, vertices_208) then 15 else
  if p.val = (true, vertices_400) then 16 else
  0
cert_priority
cert_nodeAtPriority_33 417 14 22 262 518 266 82 530 770 140 268 52 148 276 304 208 400 587 198 805 233 905 625
cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 3 4 8 566 22 3
cert_row_2 1 0 1 5 6 198
cert_row_4 2 1 2 3 6 7 412 140 2
cert_row_4 3 3 4 5 6 7 496 112 3
cert_rows
cert_pivot_2 8 0 1 3
cert_heightProof 4
cert_coverFacet 0 206
cert_cover_5 0 1 0 1 2 5 14 206 3
cert_coverFacet 1 270
cert_cover_2 1 1 0 2 7 14 270 3
cert_coverFacet 2 566
cert_cover_5 2 0 0 1 3 4 22 566 3
cert_coverFacet 3 214
cert_cover_5 3 1 0 1 3 5 22 214 3
cert_coverFacet 4 774
cert_cover_2 4 1 0 7 8 262 774 3
cert_coverFacet 5 778
cert_cover_2 5 2 0 7 8 266 778 3
cert_coverFacet 6 594
cert_cover_2 6 3 0 5 8 82 594 3
cert_coverFacet 7 412
cert_cover_5 7 2 1 2 3 6 140 412 2
cert_coverFacet 8 308
cert_cover_2 8 3 1 4 7 52 308 3
cert_coverFacet 9 496
cert_cover_5 9 3 3 4 5 6 112 496 3
cert_coveringFacets_5
cert_coveringProof
cert_certificate 4 10
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0359

end
end BundlePart14

section BundlePart15
/- Source: ProjectionCertificates/R_m16e10q1_0360.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0360

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [835, 781, 341, 149, 677, 721, 558, 314, 778, 370, 738, 172, 396, 404, 248, 408, 21, 133, 261, 517, 81, 145, 321, 577, 641, 769, 42, 266, 522, 306, 98, 546, 322, 578, 770, 44, 140, 268, 524, 148, 276, 164, 548, 388, 56, 152, 280, 168, 392, 776, 112, 208, 336, 400, 224, 672, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_835, vertices_781, vertices_341, vertices_149, vertices_677, vertices_721, vertices_558, vertices_314, vertices_778, vertices_370, vertices_738, vertices_172, vertices_396, vertices_404, vertices_248, vertices_408] (by decide +kernel)
  polygons := literalFinset [vertices_21, vertices_133, vertices_261, vertices_517, vertices_81, vertices_145, vertices_321, vertices_577, vertices_641, vertices_769, vertices_42, vertices_266, vertices_522, vertices_306, vertices_98, vertices_546, vertices_322, vertices_578, vertices_770, vertices_44, vertices_140, vertices_268, vertices_524, vertices_148, vertices_276, vertices_164, vertices_548, vertices_388, vertices_56, vertices_152, vertices_280, vertices_168, vertices_392, vertices_776, vertices_112, vertices_208, vertices_336, vertices_400, vertices_224, vertices_672, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_835), (false, vertices_781), (false, vertices_341), (false, vertices_149), (false, vertices_677), (false, vertices_721), (true, vertices_42), (true, vertices_266), (true, vertices_522), (true, vertices_306), (true, vertices_98), (true, vertices_546), (true, vertices_44), (true, vertices_140), (true, vertices_388), (true, vertices_56), (true, vertices_152), (true, vertices_280), (true, vertices_168), (true, vertices_392), (true, vertices_112), (true, vertices_400), (true, vertices_224)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 17 20 24 25 27 28 29 30 31
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_835) then 18 else
  if p.val = (false, vertices_781) then 21 else
  if p.val = (false, vertices_341) then 22 else
  if p.val = (false, vertices_149) then 0 else
  if p.val = (false, vertices_677) then 23 else
  if p.val = (false, vertices_721) then 26 else
  if p.val = (true, vertices_42) then 1 else
  if p.val = (true, vertices_266) then 2 else
  if p.val = (true, vertices_522) then 3 else
  if p.val = (true, vertices_306) then 19 else
  if p.val = (true, vertices_98) then 4 else
  if p.val = (true, vertices_546) then 5 else
  if p.val = (true, vertices_44) then 6 else
  if p.val = (true, vertices_140) then 7 else
  if p.val = (true, vertices_388) then 8 else
  if p.val = (true, vertices_56) then 9 else
  if p.val = (true, vertices_152) then 10 else
  if p.val = (true, vertices_280) then 11 else
  if p.val = (true, vertices_168) then 12 else
  if p.val = (true, vertices_392) then 13 else
  if p.val = (true, vertices_112) then 14 else
  if p.val = (true, vertices_400) then 15 else
  if p.val = (true, vertices_224) then 16 else
  0
cert_priority
cert_nodeAtPriority_45 149 42 266 522 98 546 44 140 388 56 152 280 168 392 112 400 224 835 306 781 341 677 721
cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 3 4 7 306
cert_row_4 1 0 1 2 4 8 558 42 1
cert_row_4 2 0 4 5 6 8 738 98 3
cert_row_4 3 2 3 4 5 6 248 56 3
cert_rows
cert_pivot_2 7 1 0 2
cert_heightProof 4
cert_coverFacet 0 558
cert_cover_5 0 1 0 1 2 4 42 558 1
cert_coverFacet 1 314
cert_cover_5 1 0 0 2 3 4 42 314 2
cert_coverFacet 2 778
cert_cover_2 2 2 0 7 8 266 778 3
cert_coverFacet 3 370
cert_cover_5 3 0 0 3 4 5 306 370 3
cert_coverFacet 4 738
cert_cover_5 4 2 0 4 5 6 98 738 3
cert_coverFacet 5 172
cert_cover_2 5 2 1 4 6 44 172 3
cert_coverFacet 6 396
cert_cover_2 6 2 1 6 7 140 396 3
cert_coverFacet 7 404
cert_cover_2 7 3 1 6 7 148 404 3
cert_coverFacet 8 248
cert_cover_5 8 3 2 3 4 5 56 248 3
cert_coverFacet 9 408
cert_cover_2 9 3 2 6 7 152 408 3
cert_coveringFacets_5
cert_coveringProof
cert_certificate 4 10
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0360

end
end BundlePart15

section BundlePart16
/- Source: ProjectionCertificates/R_m16e10q1_0361.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0361

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [675, 653, 269, 341, 613, 361, 169, 598, 666, 466, 482, 610, 780, 788, 440, 792, 13, 69, 261, 517, 41, 137, 265, 97, 161, 545, 321, 641, 82, 146, 530, 98, 162, 546, 450, 578, 642, 268, 524, 84, 276, 532, 580, 772, 152, 280, 536, 168, 296, 648, 776, 336, 400, 784, 352, 608, 416]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_675, vertices_653, vertices_269, vertices_341, vertices_613, vertices_361, vertices_169, vertices_598, vertices_666, vertices_466, vertices_482, vertices_610, vertices_780, vertices_788, vertices_440, vertices_792] (by decide +kernel)
  polygons := literalFinset [vertices_13, vertices_69, vertices_261, vertices_517, vertices_41, vertices_137, vertices_265, vertices_97, vertices_161, vertices_545, vertices_321, vertices_641, vertices_82, vertices_146, vertices_530, vertices_98, vertices_162, vertices_546, vertices_450, vertices_578, vertices_642, vertices_268, vertices_524, vertices_84, vertices_276, vertices_532, vertices_580, vertices_772, vertices_152, vertices_280, vertices_536, vertices_168, vertices_296, vertices_648, vertices_776, vertices_336, vertices_400, vertices_784, vertices_352, vertices_608, vertices_416] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_675), (false, vertices_653), (false, vertices_269), (false, vertices_341), (false, vertices_613), (false, vertices_361), (false, vertices_169), (true, vertices_82), (true, vertices_146), (true, vertices_530), (true, vertices_98), (true, vertices_450), (true, vertices_578), (true, vertices_532), (true, vertices_772), (true, vertices_152), (true, vertices_280), (true, vertices_536), (true, vertices_776), (true, vertices_400), (true, vertices_784), (true, vertices_416)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 16 19 23 25 26 27 28 29 30
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_675) then 17 else
  if p.val = (false, vertices_653) then 20 else
  if p.val = (false, vertices_269) then 0 else
  if p.val = (false, vertices_341) then 21 else
  if p.val = (false, vertices_613) then 22 else
  if p.val = (false, vertices_361) then 24 else
  if p.val = (false, vertices_169) then 1 else
  if p.val = (true, vertices_82) then 2 else
  if p.val = (true, vertices_146) then 3 else
  if p.val = (true, vertices_530) then 4 else
  if p.val = (true, vertices_98) then 5 else
  if p.val = (true, vertices_450) then 18 else
  if p.val = (true, vertices_578) then 6 else
  if p.val = (true, vertices_532) then 7 else
  if p.val = (true, vertices_772) then 8 else
  if p.val = (true, vertices_152) then 9 else
  if p.val = (true, vertices_280) then 10 else
  if p.val = (true, vertices_536) then 11 else
  if p.val = (true, vertices_776) then 12 else
  if p.val = (true, vertices_400) then 13 else
  if p.val = (true, vertices_784) then 14 else
  if p.val = (true, vertices_416) then 15 else
  0
cert_priority
cert_nodeAtPriority_5 0 269 1 169 82 146 530 98 578 532 772 152 280 536 776 400 784 416 675 450 653 341 613 361
cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 3 5 8 598 82 1
cert_row_2 1 0 5 6 7 450
cert_row_4 2 0 2 3 6 8 666 146 1
cert_row_4 3 2 3 4 6 7 440 152 2
cert_rows
cert_pivot_2 1 5 0 2
cert_heightProof 4
cert_coverFacet 0 598
cert_cover_5 0 0 0 1 3 5 82 598 1
cert_coverFacet 1 666
cert_cover_5 1 2 0 2 3 6 146 666 1
cert_coverFacet 2 466
cert_cover_5 2 1 0 3 5 6 82 466 3
cert_coverFacet 3 482
cert_cover_5 3 1 0 4 5 6 98 482 3
cert_coverFacet 4 610
cert_cover_2 4 4 0 5 8 98 610 3
cert_coverFacet 5 780
cert_cover_2 5 2 1 7 8 268 780 3
cert_coverFacet 6 788
cert_cover_2 6 3 1 7 8 276 788 3
cert_coverFacet 7 440
cert_cover_5 7 3 2 3 4 6 152 440 2
cert_coverFacet 8 792
cert_cover_2 8 3 2 7 8 280 792 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0361

end
end BundlePart16

section BundlePart17
/- Source: ProjectionCertificates/R_m16e10q1_0362.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0362

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [835, 149, 789, 709, 185, 369, 225, 782, 122, 346, 554, 738, 684, 396, 404, 408, 21, 133, 517, 49, 145, 273, 97, 161, 193, 321, 577, 769, 90, 42, 266, 522, 98, 546, 322, 578, 770, 140, 268, 524, 148, 276, 388, 644, 772, 56, 152, 280, 168, 552, 392, 112, 336, 400, 224, 672, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_835, vertices_149, vertices_789, vertices_709, vertices_185, vertices_369, vertices_225, vertices_782, vertices_122, vertices_346, vertices_554, vertices_738, vertices_684, vertices_396, vertices_404, vertices_408] (by decide +kernel)
  polygons := literalFinset [vertices_21, vertices_133, vertices_517, vertices_49, vertices_145, vertices_273, vertices_97, vertices_161, vertices_193, vertices_321, vertices_577, vertices_769, vertices_90, vertices_42, vertices_266, vertices_522, vertices_98, vertices_546, vertices_322, vertices_578, vertices_770, vertices_140, vertices_268, vertices_524, vertices_148, vertices_276, vertices_388, vertices_644, vertices_772, vertices_56, vertices_152, vertices_280, vertices_168, vertices_552, vertices_392, vertices_112, vertices_336, vertices_400, vertices_224, vertices_672, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_835), (false, vertices_149), (false, vertices_789), (false, vertices_709), (false, vertices_185), (false, vertices_369), (false, vertices_225), (true, vertices_90), (true, vertices_42), (true, vertices_266), (true, vertices_522), (true, vertices_98), (true, vertices_546), (true, vertices_140), (true, vertices_268), (true, vertices_524), (true, vertices_388), (true, vertices_280), (true, vertices_552), (true, vertices_392), (true, vertices_400), (true, vertices_672)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 16 19 22 24 26 27 28 29 30
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_835) then 17 else
  if p.val = (false, vertices_149) then 0 else
  if p.val = (false, vertices_789) then 20 else
  if p.val = (false, vertices_709) then 21 else
  if p.val = (false, vertices_185) then 23 else
  if p.val = (false, vertices_369) then 25 else
  if p.val = (false, vertices_225) then 1 else
  if p.val = (true, vertices_90) then 18 else
  if p.val = (true, vertices_42) then 2 else
  if p.val = (true, vertices_266) then 3 else
  if p.val = (true, vertices_522) then 4 else
  if p.val = (true, vertices_98) then 5 else
  if p.val = (true, vertices_546) then 6 else
  if p.val = (true, vertices_140) then 7 else
  if p.val = (true, vertices_268) then 8 else
  if p.val = (true, vertices_524) then 9 else
  if p.val = (true, vertices_388) then 10 else
  if p.val = (true, vertices_280) then 11 else
  if p.val = (true, vertices_552) then 12 else
  if p.val = (true, vertices_392) then 13 else
  if p.val = (true, vertices_400) then 14 else
  if p.val = (true, vertices_672) then 15 else
  0
cert_priority
cert_nodeAtPriority_50 1 149 0 225 42 266 522 98 546 140 268 524 388 280 552 392 400 672 835 90 789 709 185 369
cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 2 3 5 90
cert_row_4 1 0 1 2 7 8 782 266 1
cert_row_4 2 0 4 5 6 8 738 98 3
cert_row_4 3 1 2 4 6 8 684 140 2
cert_rows
cert_pivot_2 3 7 0 1
cert_heightProof 4
cert_coverFacet 0 782
cert_cover_5 0 1 0 1 2 7 266 782 1
cert_coverFacet 1 122
cert_cover_5 1 0 0 2 3 4 90 122 3
cert_coverFacet 2 346
cert_cover_5 2 0 0 2 3 7 90 346 3
cert_coverFacet 3 554
cert_cover_2 3 2 0 4 8 42 554 3
cert_coverFacet 4 738
cert_cover_5 4 2 0 4 5 6 98 738 3
cert_coverFacet 5 684
cert_cover_5 5 3 1 2 4 6 140 684 2
cert_coverFacet 6 396
cert_cover_2 6 2 1 6 7 140 396 3
cert_coverFacet 7 404
cert_cover_2 7 3 1 6 7 148 404 3
cert_coverFacet 8 408
cert_cover_2 8 3 2 6 7 152 408 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0362

end
end BundlePart17

section BundlePart18
/- Source: ProjectionCertificates/R_m16e10q1_0363.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0363

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [835, 557, 53, 789, 369, 737, 782, 218, 346, 682, 706, 172, 396, 244, 404, 408, 21, 37, 517, 49, 273, 97, 545, 321, 577, 769, 90, 138, 266, 522, 194, 322, 578, 642, 770, 44, 140, 268, 524, 52, 148, 276, 164, 388, 772, 152, 280, 168, 552, 392, 112, 208, 336, 400, 224, 672, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_835, vertices_557, vertices_53, vertices_789, vertices_369, vertices_737, vertices_782, vertices_218, vertices_346, vertices_682, vertices_706, vertices_172, vertices_396, vertices_244, vertices_404, vertices_408] (by decide +kernel)
  polygons := literalFinset [vertices_21, vertices_37, vertices_517, vertices_49, vertices_273, vertices_97, vertices_545, vertices_321, vertices_577, vertices_769, vertices_90, vertices_138, vertices_266, vertices_522, vertices_194, vertices_322, vertices_578, vertices_642, vertices_770, vertices_44, vertices_140, vertices_268, vertices_524, vertices_52, vertices_148, vertices_276, vertices_164, vertices_388, vertices_772, vertices_152, vertices_280, vertices_168, vertices_552, vertices_392, vertices_112, vertices_208, vertices_336, vertices_400, vertices_224, vertices_672, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_835), (false, vertices_557), (false, vertices_53), (false, vertices_789), (false, vertices_369), (false, vertices_737), (true, vertices_90), (true, vertices_138), (true, vertices_266), (true, vertices_522), (true, vertices_194), (true, vertices_642), (true, vertices_140), (true, vertices_268), (true, vertices_148), (true, vertices_164), (true, vertices_388), (true, vertices_152), (true, vertices_280), (true, vertices_168), (true, vertices_392), (true, vertices_208), (true, vertices_400)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 17 20 23 24 26 28 29 30 31
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_835) then 18 else
  if p.val = (false, vertices_557) then 21 else
  if p.val = (false, vertices_53) then 0 else
  if p.val = (false, vertices_789) then 22 else
  if p.val = (false, vertices_369) then 25 else
  if p.val = (false, vertices_737) then 27 else
  if p.val = (true, vertices_90) then 19 else
  if p.val = (true, vertices_138) then 1 else
  if p.val = (true, vertices_266) then 2 else
  if p.val = (true, vertices_522) then 3 else
  if p.val = (true, vertices_194) then 4 else
  if p.val = (true, vertices_642) then 5 else
  if p.val = (true, vertices_140) then 6 else
  if p.val = (true, vertices_268) then 7 else
  if p.val = (true, vertices_148) then 8 else
  if p.val = (true, vertices_164) then 9 else
  if p.val = (true, vertices_388) then 10 else
  if p.val = (true, vertices_152) then 11 else
  if p.val = (true, vertices_280) then 12 else
  if p.val = (true, vertices_168) then 13 else
  if p.val = (true, vertices_392) then 14 else
  if p.val = (true, vertices_208) then 15 else
  if p.val = (true, vertices_400) then 16 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_53), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_138), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_266), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_522), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_194), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_642), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_140), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_268), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_148), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_164), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_388), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_152), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_280), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_168), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_392), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_208), by decide +kernel⟩
  | 16 => Sum.inr ⟨(true, vertices_400), by decide +kernel⟩
  | 17 => Sum.inl 0
  | 18 => Sum.inr ⟨(false, vertices_835), by decide +kernel⟩
  | 19 => Sum.inr ⟨(true, vertices_90), by decide +kernel⟩
  | 20 => Sum.inl 1
  | 21 => Sum.inr ⟨(false, vertices_557), by decide +kernel⟩
  | 22 => Sum.inr ⟨(false, vertices_789), by decide +kernel⟩
  | 23 => Sum.inl 2
  | 24 => Sum.inl 3
  | 25 => Sum.inr ⟨(false, vertices_369), by decide +kernel⟩
  | 26 => Sum.inl 4
  | 27 => Sum.inr ⟨(false, vertices_737), by decide +kernel⟩
  | 28 => Sum.inl 5
  | 29 => Sum.inl 6
  | 30 => Sum.inl 7
  | 31 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 2 7 8 782 266 1
cert_row_4 1 0 2 4 6 8 682 138 2
cert_row_2 2 0 2 3 5 90
cert_row_4 3 1 3 4 5 6 244 52 3
cert_rows
cert_pivot_2 7 8 0 1
cert_heightProof 4
cert_coverFacet 0 782
cert_cover_5 0 0 0 1 2 7 266 782 1
cert_coverFacet 1 218
cert_cover_5 1 2 0 2 3 6 90 218 3
cert_coverFacet 2 346
cert_cover_5 2 2 0 2 3 7 90 346 3
cert_coverFacet 3 682
cert_cover_5 3 1 0 2 4 6 138 682 2
cert_coverFacet 4 706
cert_cover_2 4 5 0 6 8 194 706 3
cert_coverFacet 5 172
cert_cover_2 5 2 1 4 6 44 172 3
cert_coverFacet 6 396
cert_cover_2 6 2 1 6 7 140 396 3
cert_coverFacet 7 244
cert_cover_5 7 3 1 3 4 5 52 244 3
cert_coverFacet 8 404
cert_cover_2 8 3 1 6 7 148 404 3
cert_coverFacet 9 408
cert_cover_2 9 3 2 6 7 152 408 3
cert_coveringFacets_5
cert_coveringProof
cert_certificate 4 10
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0363

end
end BundlePart18

section BundlePart19
/- Source: ProjectionCertificates/R_m16e10q1_0364.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0364

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [675, 653, 269, 341, 197, 809, 481, 710, 58, 602, 554, 434, 466, 316, 540, 596, 13, 69, 133, 261, 265, 521, 161, 289, 545, 193, 321, 641, 26, 42, 522, 50, 82, 402, 162, 546, 194, 578, 642, 28, 268, 524, 84, 276, 532, 196, 580, 644, 56, 536, 296, 552, 304, 336, 592, 416, 448]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_675, vertices_653, vertices_269, vertices_341, vertices_197, vertices_809, vertices_481, vertices_710, vertices_58, vertices_602, vertices_554, vertices_434, vertices_466, vertices_316, vertices_540, vertices_596] (by decide +kernel)
  polygons := literalFinset [vertices_13, vertices_69, vertices_133, vertices_261, vertices_265, vertices_521, vertices_161, vertices_289, vertices_545, vertices_193, vertices_321, vertices_641, vertices_26, vertices_42, vertices_522, vertices_50, vertices_82, vertices_402, vertices_162, vertices_546, vertices_194, vertices_578, vertices_642, vertices_28, vertices_268, vertices_524, vertices_84, vertices_276, vertices_532, vertices_196, vertices_580, vertices_644, vertices_56, vertices_536, vertices_296, vertices_552, vertices_304, vertices_336, vertices_592, vertices_416, vertices_448] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_675), (false, vertices_653), (false, vertices_269), (false, vertices_341), (false, vertices_197), (false, vertices_809), (false, vertices_481), (true, vertices_26), (true, vertices_42), (true, vertices_522), (true, vertices_50), (true, vertices_82), (true, vertices_402), (true, vertices_194), (true, vertices_578), (true, vertices_28), (true, vertices_532), (true, vertices_580), (true, vertices_56), (true, vertices_536), (true, vertices_304), (true, vertices_592)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 16 19 22 24 25 27 28 29 30
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_675) then 17 else
  if p.val = (false, vertices_653) then 20 else
  if p.val = (false, vertices_269) then 0 else
  if p.val = (false, vertices_341) then 21 else
  if p.val = (false, vertices_197) then 1 else
  if p.val = (false, vertices_809) then 23 else
  if p.val = (false, vertices_481) then 26 else
  if p.val = (true, vertices_26) then 2 else
  if p.val = (true, vertices_42) then 3 else
  if p.val = (true, vertices_522) then 4 else
  if p.val = (true, vertices_50) then 5 else
  if p.val = (true, vertices_82) then 6 else
  if p.val = (true, vertices_402) then 18 else
  if p.val = (true, vertices_194) then 7 else
  if p.val = (true, vertices_578) then 8 else
  if p.val = (true, vertices_28) then 9 else
  if p.val = (true, vertices_532) then 10 else
  if p.val = (true, vertices_580) then 11 else
  if p.val = (true, vertices_56) then 12 else
  if p.val = (true, vertices_536) then 13 else
  if p.val = (true, vertices_304) then 14 else
  if p.val = (true, vertices_592) then 15 else
  0
cert_priority
cert_nodeAtPriority_24 1 269 0 197 26 42 522 50 82 194 578 28 532 580 56 536 304 592 675 402 653 341 809 481
cert_priority_injective
cert_incidenceProof
cert_row_4 0 1 2 3 4 7 316 28 3
cert_row_2 1 0 3 6 7 402
cert_row_4 2 0 1 5 6 8 710 194 1
cert_row_4 3 0 2 3 5 8 602 26 3
cert_rows
cert_pivot_2 4 7 1 0
cert_heightProof 4
cert_coverFacet 0 710
cert_cover_5 0 2 0 1 5 6 194 710 1
cert_coverFacet 1 58
cert_cover_2 1 2 0 3 4 26 58 3
cert_coverFacet 2 602
cert_cover_5 2 3 0 2 3 5 26 602 3
cert_coverFacet 3 554
cert_cover_2 3 2 0 4 8 42 554 3
cert_coverFacet 4 434
cert_cover_5 4 1 0 3 4 6 50 434 3
cert_coverFacet 5 466
cert_cover_5 5 1 0 3 5 6 82 466 3
cert_coverFacet 6 316
cert_cover_5 6 0 1 2 3 4 28 316 3
cert_coverFacet 7 540
cert_cover_2 7 2 1 3 8 28 540 3
cert_coverFacet 8 596
cert_cover_2 8 3 1 5 8 84 596 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0364

end
end BundlePart19

section BundlePart20
/- Source: ProjectionCertificates/R_m16e10q1_0365.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0365

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [107, 661, 425, 713, 369, 593, 401, 206, 270, 710, 774, 298, 626, 802, 412, 820, 41, 73, 137, 81, 145, 273, 529, 97, 289, 577, 385, 641, 14, 198, 262, 518, 42, 74, 266, 98, 290, 546, 578, 770, 140, 268, 148, 276, 532, 644, 772, 296, 200, 392, 112, 304, 560, 592, 400, 800, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_107, vertices_661, vertices_425, vertices_713, vertices_369, vertices_593, vertices_401, vertices_206, vertices_270, vertices_710, vertices_774, vertices_298, vertices_626, vertices_802, vertices_412, vertices_820] (by decide +kernel)
  polygons := literalFinset [vertices_41, vertices_73, vertices_137, vertices_81, vertices_145, vertices_273, vertices_529, vertices_97, vertices_289, vertices_577, vertices_385, vertices_641, vertices_14, vertices_198, vertices_262, vertices_518, vertices_42, vertices_74, vertices_266, vertices_98, vertices_290, vertices_546, vertices_578, vertices_770, vertices_140, vertices_268, vertices_148, vertices_276, vertices_532, vertices_644, vertices_772, vertices_296, vertices_200, vertices_392, vertices_112, vertices_304, vertices_560, vertices_592, vertices_400, vertices_800, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_107), (false, vertices_661), (false, vertices_425), (false, vertices_713), (false, vertices_369), (false, vertices_593), (false, vertices_401), (true, vertices_14), (true, vertices_198), (true, vertices_262), (true, vertices_518), (true, vertices_266), (true, vertices_290), (true, vertices_546), (true, vertices_578), (true, vertices_770), (true, vertices_140), (true, vertices_268), (true, vertices_276), (true, vertices_772), (true, vertices_560), (true, vertices_800)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 16 19 21 24 26 27 28 29 30
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_107) then 17 else
  if p.val = (false, vertices_661) then 20 else
  if p.val = (false, vertices_425) then 22 else
  if p.val = (false, vertices_713) then 23 else
  if p.val = (false, vertices_369) then 25 else
  if p.val = (false, vertices_593) then 0 else
  if p.val = (false, vertices_401) then 1 else
  if p.val = (true, vertices_14) then 2 else
  if p.val = (true, vertices_198) then 18 else
  if p.val = (true, vertices_262) then 3 else
  if p.val = (true, vertices_518) then 4 else
  if p.val = (true, vertices_266) then 5 else
  if p.val = (true, vertices_290) then 6 else
  if p.val = (true, vertices_546) then 7 else
  if p.val = (true, vertices_578) then 8 else
  if p.val = (true, vertices_770) then 9 else
  if p.val = (true, vertices_140) then 10 else
  if p.val = (true, vertices_268) then 11 else
  if p.val = (true, vertices_276) then 12 else
  if p.val = (true, vertices_772) then 13 else
  if p.val = (true, vertices_560) then 14 else
  if p.val = (true, vertices_800) then 15 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_593), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_401), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_14), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_262), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_518), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_266), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_290), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_546), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_578), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_770), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_140), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_268), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_276), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_772), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_560), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_800), by decide +kernel⟩
  | 16 => Sum.inl 0
  | 17 => Sum.inr ⟨(false, vertices_107), by decide +kernel⟩
  | 18 => Sum.inr ⟨(true, vertices_198), by decide +kernel⟩
  | 19 => Sum.inl 1
  | 20 => Sum.inr ⟨(false, vertices_661), by decide +kernel⟩
  | 21 => Sum.inl 2
  | 22 => Sum.inr ⟨(false, vertices_425), by decide +kernel⟩
  | 23 => Sum.inr ⟨(false, vertices_713), by decide +kernel⟩
  | 24 => Sum.inl 3
  | 25 => Sum.inr ⟨(false, vertices_369), by decide +kernel⟩
  | 26 => Sum.inl 4
  | 27 => Sum.inl 5
  | 28 => Sum.inl 6
  | 29 => Sum.inl 7
  | 30 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 1 2 3 6 7 412 140 2
cert_row_2 1 0 1 5 6 198
cert_row_4 2 0 3 4 5 8 626 98 1
cert_row_4 3 1 3 4 7 8 820 276 2
cert_rows
cert_pivot_2 2 6 0 1
cert_heightProof 4
cert_coverFacet 0 206
cert_cover_5 0 1 0 1 2 5 14 206 3
cert_coverFacet 1 270
cert_cover_2 1 1 0 2 7 14 270 3
cert_coverFacet 2 710
cert_cover_5 2 1 0 1 5 8 198 710 3
cert_coverFacet 3 774
cert_cover_2 3 1 0 7 8 262 774 3
cert_coverFacet 4 298
cert_cover_2 4 2 0 4 7 42 298 3
cert_coverFacet 5 626
cert_cover_5 5 2 0 3 4 5 98 626 1
cert_coverFacet 6 802
cert_cover_2 6 4 0 7 8 290 802 3
cert_coverFacet 7 412
cert_cover_5 7 0 1 2 3 6 140 412 2
cert_coverFacet 8 820
cert_cover_5 8 3 1 3 4 7 276 820 2
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0365

end
end BundlePart20

section BundlePart21
/- Source: ProjectionCertificates/R_m16e10q1_0366.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0366

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [775, 211, 339, 675, 809, 481, 278, 534, 666, 220, 540, 108, 300, 780, 372, 744, 83, 131, 259, 515, 161, 289, 545, 193, 321, 769, 22, 262, 518, 146, 274, 530, 642, 28, 44, 76, 268, 524, 84, 276, 532, 100, 292, 772, 152, 536, 104, 296, 552, 200, 648, 776, 208, 336, 224, 352, 672]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_775, vertices_211, vertices_339, vertices_675, vertices_809, vertices_481, vertices_278, vertices_534, vertices_666, vertices_220, vertices_540, vertices_108, vertices_300, vertices_780, vertices_372, vertices_744] (by decide +kernel)
  polygons := literalFinset [vertices_83, vertices_131, vertices_259, vertices_515, vertices_161, vertices_289, vertices_545, vertices_193, vertices_321, vertices_769, vertices_22, vertices_262, vertices_518, vertices_146, vertices_274, vertices_530, vertices_642, vertices_28, vertices_44, vertices_76, vertices_268, vertices_524, vertices_84, vertices_276, vertices_532, vertices_100, vertices_292, vertices_772, vertices_152, vertices_536, vertices_104, vertices_296, vertices_552, vertices_200, vertices_648, vertices_776, vertices_208, vertices_336, vertices_224, vertices_352, vertices_672] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_775), (false, vertices_211), (false, vertices_339), (false, vertices_675), (false, vertices_809), (false, vertices_481), (true, vertices_22), (true, vertices_530), (true, vertices_28), (true, vertices_44), (true, vertices_76), (true, vertices_268), (true, vertices_524), (true, vertices_84), (true, vertices_276), (true, vertices_532), (true, vertices_100), (true, vertices_292), (true, vertices_152), (true, vertices_536), (true, vertices_104), (true, vertices_200), (true, vertices_648)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 19 17 23 25 26 28 29 30 31
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_775) then 18 else
  if p.val = (false, vertices_211) then 20 else
  if p.val = (false, vertices_339) then 21 else
  if p.val = (false, vertices_675) then 22 else
  if p.val = (false, vertices_809) then 24 else
  if p.val = (false, vertices_481) then 27 else
  if p.val = (true, vertices_22) then 0 else
  if p.val = (true, vertices_530) then 1 else
  if p.val = (true, vertices_28) then 2 else
  if p.val = (true, vertices_44) then 3 else
  if p.val = (true, vertices_76) then 4 else
  if p.val = (true, vertices_268) then 5 else
  if p.val = (true, vertices_524) then 6 else
  if p.val = (true, vertices_84) then 7 else
  if p.val = (true, vertices_276) then 8 else
  if p.val = (true, vertices_532) then 9 else
  if p.val = (true, vertices_100) then 10 else
  if p.val = (true, vertices_292) then 11 else
  if p.val = (true, vertices_152) then 12 else
  if p.val = (true, vertices_536) then 13 else
  if p.val = (true, vertices_104) then 14 else
  if p.val = (true, vertices_200) then 15 else
  if p.val = (true, vertices_648) then 16 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_22), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_530), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_28), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_44), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_76), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_268), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_524), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_84), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_276), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_532), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_100), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_292), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_152), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_536), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_104), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_200), by decide +kernel⟩
  | 16 => Sum.inr ⟨(true, vertices_648), by decide +kernel⟩
  | 17 => Sum.inl 1
  | 18 => Sum.inr ⟨(false, vertices_775), by decide +kernel⟩
  | 19 => Sum.inl 0
  | 20 => Sum.inr ⟨(false, vertices_211), by decide +kernel⟩
  | 21 => Sum.inr ⟨(false, vertices_339), by decide +kernel⟩
  | 22 => Sum.inr ⟨(false, vertices_675), by decide +kernel⟩
  | 23 => Sum.inl 2
  | 24 => Sum.inr ⟨(false, vertices_809), by decide +kernel⟩
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
cert_row_4 0 0 2 3 6 8 666 146 1
cert_row_4 1 1 3 4 5 7 372 84 2
cert_row_4 2 1 2 3 5 6 220 28 3
cert_row_4 3 2 4 5 6 8 744 104 3
cert_rows
cert_pivot_2 0 7 1 2
cert_heightProof 4
cert_coverFacet 0 278
cert_cover_2 0 1 0 3 7 22 278 3
cert_coverFacet 1 534
cert_cover_2 1 1 0 3 8 22 534 3
cert_coverFacet 2 666
cert_cover_5 2 0 0 2 3 6 146 666 1
cert_coverFacet 3 220
cert_cover_5 3 2 1 2 3 5 28 220 3
cert_coverFacet 4 540
cert_cover_2 4 2 1 3 8 28 540 3
cert_coverFacet 5 108
cert_cover_2 5 2 1 4 5 44 108 3
cert_coverFacet 6 300
cert_cover_2 6 2 1 4 7 44 300 3
cert_coverFacet 7 780
cert_cover_2 7 2 1 7 8 268 780 3
cert_coverFacet 8 372
cert_cover_5 8 1 1 3 4 5 84 372 2
cert_coverFacet 9 744
cert_cover_5 9 3 2 4 5 6 104 744 3
cert_coveringFacets_5
cert_coveringProof
cert_certificate 4 10
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0366

end
end BundlePart21

section BundlePart22
/- Source: ProjectionCertificates/R_m16e10q1_0367.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0367

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [155, 651, 557, 121, 721, 865, 302, 526, 406, 710, 282, 804, 452, 836, 312, 496, 139, 25, 41, 521, 81, 145, 97, 545, 577, 641, 14, 134, 262, 518, 26, 266, 522, 146, 274, 642, 44, 524, 292, 548, 196, 324, 580, 388, 772, 56, 280, 296, 112, 304, 208, 400, 352, 800, 448, 704, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_155, vertices_651, vertices_557, vertices_121, vertices_721, vertices_865, vertices_302, vertices_526, vertices_406, vertices_710, vertices_282, vertices_804, vertices_452, vertices_836, vertices_312, vertices_496] (by decide +kernel)
  polygons := literalFinset [vertices_139, vertices_25, vertices_41, vertices_521, vertices_81, vertices_145, vertices_97, vertices_545, vertices_577, vertices_641, vertices_14, vertices_134, vertices_262, vertices_518, vertices_26, vertices_266, vertices_522, vertices_146, vertices_274, vertices_642, vertices_44, vertices_524, vertices_292, vertices_548, vertices_196, vertices_324, vertices_580, vertices_388, vertices_772, vertices_56, vertices_280, vertices_296, vertices_112, vertices_304, vertices_208, vertices_400, vertices_352, vertices_800, vertices_448, vertices_704, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_155), (false, vertices_651), (false, vertices_557), (false, vertices_121), (false, vertices_721), (false, vertices_865), (true, vertices_14), (true, vertices_134), (true, vertices_262), (true, vertices_518), (true, vertices_266), (true, vertices_274), (true, vertices_292), (true, vertices_196), (true, vertices_324), (true, vertices_580), (true, vertices_388), (true, vertices_772), (true, vertices_280), (true, vertices_296), (true, vertices_304), (true, vertices_400), (true, vertices_448)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 17 20 22 24 26 28 29 30 31
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_155) then 18 else
  if p.val = (false, vertices_651) then 19 else
  if p.val = (false, vertices_557) then 21 else
  if p.val = (false, vertices_121) then 23 else
  if p.val = (false, vertices_721) then 25 else
  if p.val = (false, vertices_865) then 27 else
  if p.val = (true, vertices_14) then 0 else
  if p.val = (true, vertices_134) then 1 else
  if p.val = (true, vertices_262) then 2 else
  if p.val = (true, vertices_518) then 3 else
  if p.val = (true, vertices_266) then 4 else
  if p.val = (true, vertices_274) then 5 else
  if p.val = (true, vertices_292) then 6 else
  if p.val = (true, vertices_196) then 7 else
  if p.val = (true, vertices_324) then 8 else
  if p.val = (true, vertices_580) then 9 else
  if p.val = (true, vertices_388) then 10 else
  if p.val = (true, vertices_772) then 11 else
  if p.val = (true, vertices_280) then 12 else
  if p.val = (true, vertices_296) then 13 else
  if p.val = (true, vertices_304) then 14 else
  if p.val = (true, vertices_400) then 15 else
  if p.val = (true, vertices_448) then 16 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_14), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_134), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_262), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_518), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_266), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_274), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_292), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_196), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_324), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_580), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_388), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_772), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_280), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_296), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_304), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_400), by decide +kernel⟩
  | 16 => Sum.inr ⟨(true, vertices_448), by decide +kernel⟩
  | 17 => Sum.inl 0
  | 18 => Sum.inr ⟨(false, vertices_155), by decide +kernel⟩
  | 19 => Sum.inr ⟨(false, vertices_651), by decide +kernel⟩
  | 20 => Sum.inl 1
  | 21 => Sum.inr ⟨(false, vertices_557), by decide +kernel⟩
  | 22 => Sum.inl 2
  | 23 => Sum.inr ⟨(false, vertices_121), by decide +kernel⟩
  | 24 => Sum.inl 3
  | 25 => Sum.inr ⟨(false, vertices_721), by decide +kernel⟩
  | 26 => Sum.inl 4
  | 27 => Sum.inr ⟨(false, vertices_865), by decide +kernel⟩
  | 28 => Sum.inl 5
  | 29 => Sum.inl 6
  | 30 => Sum.inl 7
  | 31 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 2 4 7 302 14 3
cert_row_4 1 0 1 5 6 8 710 134 2
cert_row_4 2 0 1 3 6 7 406 134 2
cert_row_4 3 3 4 5 6 7 496 112 3
cert_rows
cert_pivot_2 2 8 0 3
cert_heightProof 4
cert_coverFacet 0 302
cert_cover_5 0 0 0 1 2 4 14 302 3
cert_coverFacet 1 526
cert_cover_2 1 1 0 2 8 14 526 3
cert_coverFacet 2 406
cert_cover_5 2 2 0 1 3 6 134 406 2
cert_coverFacet 3 710
cert_cover_5 3 1 0 1 5 6 134 710 2
cert_coverFacet 4 282
cert_cover_2 4 2 0 3 7 26 282 3
cert_coverFacet 5 804
cert_cover_2 5 4 1 7 8 292 804 3
cert_coverFacet 6 452
cert_cover_2 6 5 1 6 7 196 452 3
cert_coverFacet 7 836
cert_cover_2 7 5 1 7 8 324 836 3
cert_coverFacet 8 312
cert_cover_2 8 3 2 4 7 56 312 3
cert_coverFacet 9 496
cert_cover_5 9 3 3 4 5 6 112 496 3
cert_coveringFacets_5
cert_coveringProof
cert_certificate 4 10
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0367

end
end BundlePart22

section BundlePart23
/- Source: ProjectionCertificates/R_m16e10q1_0368.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0368

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [899, 557, 77, 453, 773, 121, 737, 406, 810, 626, 306, 722, 220, 284, 780, 312, 13, 69, 261, 517, 41, 73, 97, 545, 193, 385, 641, 769, 50, 594, 146, 274, 290, 546, 386, 642, 770, 28, 76, 268, 524, 148, 276, 196, 388, 772, 56, 88, 280, 296, 552, 776, 112, 304, 208, 608, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_899, vertices_557, vertices_77, vertices_453, vertices_773, vertices_121, vertices_737, vertices_406, vertices_810, vertices_626, vertices_306, vertices_722, vertices_220, vertices_284, vertices_780, vertices_312] (by decide +kernel)
  polygons := literalFinset [vertices_13, vertices_69, vertices_261, vertices_517, vertices_41, vertices_73, vertices_97, vertices_545, vertices_193, vertices_385, vertices_641, vertices_769, vertices_50, vertices_594, vertices_146, vertices_274, vertices_290, vertices_546, vertices_386, vertices_642, vertices_770, vertices_28, vertices_76, vertices_268, vertices_524, vertices_148, vertices_276, vertices_196, vertices_388, vertices_772, vertices_56, vertices_88, vertices_280, vertices_296, vertices_552, vertices_776, vertices_112, vertices_304, vertices_208, vertices_608, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_899), (false, vertices_557), (false, vertices_77), (false, vertices_453), (false, vertices_773), (false, vertices_121), (false, vertices_737), (true, vertices_50), (true, vertices_594), (true, vertices_146), (true, vertices_274), (true, vertices_290), (true, vertices_546), (true, vertices_28), (true, vertices_268), (true, vertices_148), (true, vertices_276), (true, vertices_280), (true, vertices_296), (true, vertices_776), (true, vertices_304), (true, vertices_208)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 16 19 22 24 25 27 28 29 30
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_899) then 17 else
  if p.val = (false, vertices_557) then 20 else
  if p.val = (false, vertices_77) then 0 else
  if p.val = (false, vertices_453) then 21 else
  if p.val = (false, vertices_773) then 1 else
  if p.val = (false, vertices_121) then 23 else
  if p.val = (false, vertices_737) then 26 else
  if p.val = (true, vertices_50) then 2 else
  if p.val = (true, vertices_594) then 18 else
  if p.val = (true, vertices_146) then 3 else
  if p.val = (true, vertices_274) then 4 else
  if p.val = (true, vertices_290) then 5 else
  if p.val = (true, vertices_546) then 6 else
  if p.val = (true, vertices_28) then 7 else
  if p.val = (true, vertices_268) then 8 else
  if p.val = (true, vertices_148) then 9 else
  if p.val = (true, vertices_276) then 10 else
  if p.val = (true, vertices_280) then 11 else
  if p.val = (true, vertices_296) then 12 else
  if p.val = (true, vertices_776) then 13 else
  if p.val = (true, vertices_304) then 14 else
  if p.val = (true, vertices_208) then 15 else
  0
cert_priority
cert_nodeAtPriority_24 1 77 0 773 50 146 274 290 546 28 268 148 276 280 296 776 304 208 899 594 557 453 121 737
cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 2 4 7 8 810 290 1
cert_row_2 1 0 3 5 8 594
cert_row_4 2 0 1 3 6 7 406 146 1
cert_row_4 3 1 2 3 5 6 220 28 3
cert_rows
cert_pivot_2 4 8 0 1
cert_heightProof 4
cert_coverFacet 0 406
cert_cover_5 0 2 0 1 3 6 146 406 1
cert_coverFacet 1 810
cert_cover_5 1 0 0 2 4 7 290 810 1
cert_coverFacet 2 626
cert_cover_5 2 1 0 3 4 5 50 626 3
cert_coverFacet 3 306
cert_cover_2 3 3 0 4 7 50 306 3
cert_coverFacet 4 722
cert_cover_5 4 1 0 3 5 6 594 722 3
cert_coverFacet 5 220
cert_cover_5 5 3 1 2 3 5 28 220 3
cert_coverFacet 6 284
cert_cover_2 6 2 1 3 7 28 284 3
cert_coverFacet 7 780
cert_cover_2 7 2 1 7 8 268 780 3
cert_coverFacet 8 312
cert_cover_2 8 3 2 4 7 56 312 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0368

end
end BundlePart23

section BundlePart24
/- Source: ProjectionCertificates/R_m16e10q1_0369.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0369

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [651, 789, 357, 709, 217, 537, 337, 302, 614, 774, 186, 778, 738, 312, 792, 496, 69, 261, 517, 25, 137, 521, 81, 273, 529, 193, 321, 641, 38, 262, 518, 42, 138, 266, 522, 610, 162, 642, 770, 100, 292, 580, 772, 56, 152, 280, 536, 296, 776, 176, 304, 208, 336, 784, 224, 352, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_651, vertices_789, vertices_357, vertices_709, vertices_217, vertices_537, vertices_337, vertices_302, vertices_614, vertices_774, vertices_186, vertices_778, vertices_738, vertices_312, vertices_792, vertices_496] (by decide +kernel)
  polygons := literalFinset [vertices_69, vertices_261, vertices_517, vertices_25, vertices_137, vertices_521, vertices_81, vertices_273, vertices_529, vertices_193, vertices_321, vertices_641, vertices_38, vertices_262, vertices_518, vertices_42, vertices_138, vertices_266, vertices_522, vertices_610, vertices_162, vertices_642, vertices_770, vertices_100, vertices_292, vertices_580, vertices_772, vertices_56, vertices_152, vertices_280, vertices_536, vertices_296, vertices_776, vertices_176, vertices_304, vertices_208, vertices_336, vertices_784, vertices_224, vertices_352, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_651), (false, vertices_789), (false, vertices_357), (false, vertices_709), (false, vertices_217), (false, vertices_537), (false, vertices_337), (true, vertices_38), (true, vertices_262), (true, vertices_518), (true, vertices_42), (true, vertices_266), (true, vertices_610), (true, vertices_162), (true, vertices_770), (true, vertices_56), (true, vertices_280), (true, vertices_296), (true, vertices_776), (true, vertices_176), (true, vertices_304), (true, vertices_224)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 16 19 23 25 26 27 28 29 30
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_651) then 17 else
  if p.val = (false, vertices_789) then 20 else
  if p.val = (false, vertices_357) then 21 else
  if p.val = (false, vertices_709) then 22 else
  if p.val = (false, vertices_217) then 24 else
  if p.val = (false, vertices_537) then 0 else
  if p.val = (false, vertices_337) then 1 else
  if p.val = (true, vertices_38) then 2 else
  if p.val = (true, vertices_262) then 3 else
  if p.val = (true, vertices_518) then 4 else
  if p.val = (true, vertices_42) then 5 else
  if p.val = (true, vertices_266) then 6 else
  if p.val = (true, vertices_610) then 18 else
  if p.val = (true, vertices_162) then 7 else
  if p.val = (true, vertices_770) then 8 else
  if p.val = (true, vertices_56) then 9 else
  if p.val = (true, vertices_280) then 10 else
  if p.val = (true, vertices_296) then 11 else
  if p.val = (true, vertices_776) then 12 else
  if p.val = (true, vertices_176) then 13 else
  if p.val = (true, vertices_304) then 14 else
  if p.val = (true, vertices_224) then 15 else
  0
cert_priority
cert_nodeAtPriority_5 0 537 1 337 38 262 518 42 266 162 770 56 280 296 776 176 304 224 651 610 789 357 709 217
cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 4 5 8 610
cert_row_4 1 0 1 2 4 7 302 38 2
cert_row_4 2 0 2 3 4 6 186 42 2
cert_row_4 3 3 4 5 6 7 496 176 2
cert_rows
cert_pivot_2 8 1 0 3
cert_heightProof 4
cert_coverFacet 0 302
cert_cover_5 0 1 0 1 2 4 38 302 2
cert_coverFacet 1 614
cert_cover_5 1 0 0 1 4 5 38 614 3
cert_coverFacet 2 774
cert_cover_2 2 1 0 7 8 262 774 3
cert_coverFacet 3 186
cert_cover_5 3 2 0 2 3 4 42 186 2
cert_coverFacet 4 778
cert_cover_2 4 2 0 7 8 266 778 3
cert_coverFacet 5 738
cert_cover_5 5 0 0 4 5 6 610 738 3
cert_coverFacet 6 312
cert_cover_2 6 3 2 4 7 56 312 3
cert_coverFacet 7 792
cert_cover_2 7 3 2 7 8 280 792 3
cert_coverFacet 8 496
cert_cover_5 8 3 3 4 5 6 176 496 2
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0369

end
end BundlePart24

section BundlePart25
/- Source: ProjectionCertificates/R_m16e10q1_0370.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0370

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [899, 93, 341, 665, 841, 433, 454, 618, 690, 226, 834, 572, 108, 308, 228, 420, 85, 25, 73, 521, 145, 273, 321, 385, 641, 769, 98, 162, 546, 194, 322, 578, 386, 642, 770, 28, 44, 76, 52, 276, 100, 164, 292, 196, 324, 388, 536, 104, 552, 584, 176, 304, 560, 656, 224, 416, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_899, vertices_93, vertices_341, vertices_665, vertices_841, vertices_433, vertices_454, vertices_618, vertices_690, vertices_226, vertices_834, vertices_572, vertices_108, vertices_308, vertices_228, vertices_420] (by decide +kernel)
  polygons := literalFinset [vertices_85, vertices_25, vertices_73, vertices_521, vertices_145, vertices_273, vertices_321, vertices_385, vertices_641, vertices_769, vertices_98, vertices_162, vertices_546, vertices_194, vertices_322, vertices_578, vertices_386, vertices_642, vertices_770, vertices_28, vertices_44, vertices_76, vertices_52, vertices_276, vertices_100, vertices_164, vertices_292, vertices_196, vertices_324, vertices_388, vertices_536, vertices_104, vertices_552, vertices_584, vertices_176, vertices_304, vertices_560, vertices_656, vertices_224, vertices_416, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_899), (false, vertices_93), (false, vertices_341), (false, vertices_665), (false, vertices_841), (false, vertices_433), (true, vertices_98), (true, vertices_162), (true, vertices_546), (true, vertices_194), (true, vertices_322), (true, vertices_578), (true, vertices_44), (true, vertices_52), (true, vertices_100), (true, vertices_164), (true, vertices_292), (true, vertices_196), (true, vertices_388), (true, vertices_104), (true, vertices_552), (true, vertices_560), (true, vertices_224)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 17 19 22 25 27 28 29 30 31
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_899) then 18 else
  if p.val = (false, vertices_93) then 20 else
  if p.val = (false, vertices_341) then 21 else
  if p.val = (false, vertices_665) then 23 else
  if p.val = (false, vertices_841) then 24 else
  if p.val = (false, vertices_433) then 26 else
  if p.val = (true, vertices_98) then 0 else
  if p.val = (true, vertices_162) then 1 else
  if p.val = (true, vertices_546) then 2 else
  if p.val = (true, vertices_194) then 3 else
  if p.val = (true, vertices_322) then 4 else
  if p.val = (true, vertices_578) then 5 else
  if p.val = (true, vertices_44) then 6 else
  if p.val = (true, vertices_52) then 7 else
  if p.val = (true, vertices_100) then 8 else
  if p.val = (true, vertices_164) then 9 else
  if p.val = (true, vertices_292) then 10 else
  if p.val = (true, vertices_196) then 11 else
  if p.val = (true, vertices_388) then 12 else
  if p.val = (true, vertices_104) then 13 else
  if p.val = (true, vertices_552) then 14 else
  if p.val = (true, vertices_560) then 15 else
  if p.val = (true, vertices_224) then 16 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_98), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_162), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_546), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_194), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_322), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_578), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_44), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_52), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_100), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_164), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_292), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_196), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_388), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_104), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_552), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_560), by decide +kernel⟩
  | 16 => Sum.inr ⟨(true, vertices_224), by decide +kernel⟩
  | 17 => Sum.inl 0
  | 18 => Sum.inr ⟨(false, vertices_899), by decide +kernel⟩
  | 19 => Sum.inl 1
  | 20 => Sum.inr ⟨(false, vertices_93), by decide +kernel⟩
  | 21 => Sum.inr ⟨(false, vertices_341), by decide +kernel⟩
  | 22 => Sum.inl 2
  | 23 => Sum.inr ⟨(false, vertices_665), by decide +kernel⟩
  | 24 => Sum.inr ⟨(false, vertices_841), by decide +kernel⟩
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
cert_row_4 0 0 1 5 6 7 454 194 1
cert_row_4 1 0 2 4 5 8 618 98 1
cert_row_4 2 0 3 4 6 8 690 162 1
cert_row_4 3 1 2 3 4 8 572 28 3
cert_rows
cert_pivot_2 7 5 0 1
cert_heightProof 4
cert_coverFacet 0 454
cert_cover_5 0 0 0 1 5 6 194 454 1
cert_coverFacet 1 618
cert_cover_5 1 1 0 2 4 5 98 618 1
cert_coverFacet 2 690
cert_cover_5 2 2 0 3 4 6 162 690 1
cert_coverFacet 3 226
cert_cover_2 3 4 0 5 6 98 226 3
cert_coverFacet 4 834
cert_cover_2 4 5 0 7 8 322 834 3
cert_coverFacet 5 572
cert_cover_5 5 3 1 2 3 4 28 572 3
cert_coverFacet 6 108
cert_cover_2 6 2 1 4 5 44 108 3
cert_coverFacet 7 308
cert_cover_2 7 3 1 4 7 52 308 3
cert_coverFacet 8 228
cert_cover_2 8 4 1 5 6 100 228 3
cert_coverFacet 9 420
cert_cover_2 9 4 1 6 7 164 420 3
cert_coveringFacets_5
cert_coveringProof
cert_certificate 4 10
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0370

end
end BundlePart25

section BundlePart26
/- Source: ProjectionCertificates/R_m16e10q1_0371.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0371

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [651, 307, 147, 835, 589, 457, 401, 806, 178, 674, 124, 684, 308, 852, 248, 464, 19, 131, 259, 515, 73, 137, 521, 145, 273, 321, 577, 385, 50, 146, 162, 290, 546, 642, 770, 44, 76, 524, 52, 84, 276, 292, 548, 580, 772, 120, 168, 200, 648, 176, 304, 208, 336, 400, 672, 448, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_651, vertices_307, vertices_147, vertices_835, vertices_589, vertices_457, vertices_401, vertices_806, vertices_178, vertices_674, vertices_124, vertices_684, vertices_308, vertices_852, vertices_248, vertices_464] (by decide +kernel)
  polygons := literalFinset [vertices_19, vertices_131, vertices_259, vertices_515, vertices_73, vertices_137, vertices_521, vertices_145, vertices_273, vertices_321, vertices_577, vertices_385, vertices_50, vertices_146, vertices_162, vertices_290, vertices_546, vertices_642, vertices_770, vertices_44, vertices_76, vertices_524, vertices_52, vertices_84, vertices_276, vertices_292, vertices_548, vertices_580, vertices_772, vertices_120, vertices_168, vertices_200, vertices_648, vertices_176, vertices_304, vertices_208, vertices_336, vertices_400, vertices_672, vertices_448, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_651), (false, vertices_307), (false, vertices_147), (false, vertices_835), (false, vertices_589), (false, vertices_457), (false, vertices_401), (true, vertices_162), (true, vertices_546), (true, vertices_44), (true, vertices_52), (true, vertices_84), (true, vertices_276), (true, vertices_292), (true, vertices_548), (true, vertices_772), (true, vertices_120), (true, vertices_168), (true, vertices_176), (true, vertices_208), (true, vertices_336), (true, vertices_672)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 16 20 22 25 26 27 28 29 30
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_651) then 17 else
  if p.val = (false, vertices_307) then 18 else
  if p.val = (false, vertices_147) then 0 else
  if p.val = (false, vertices_835) then 19 else
  if p.val = (false, vertices_589) then 21 else
  if p.val = (false, vertices_457) then 23 else
  if p.val = (false, vertices_401) then 1 else
  if p.val = (true, vertices_162) then 2 else
  if p.val = (true, vertices_546) then 3 else
  if p.val = (true, vertices_44) then 4 else
  if p.val = (true, vertices_52) then 5 else
  if p.val = (true, vertices_84) then 6 else
  if p.val = (true, vertices_276) then 7 else
  if p.val = (true, vertices_292) then 8 else
  if p.val = (true, vertices_548) then 9 else
  if p.val = (true, vertices_772) then 10 else
  if p.val = (true, vertices_120) then 24 else
  if p.val = (true, vertices_168) then 11 else
  if p.val = (true, vertices_176) then 12 else
  if p.val = (true, vertices_208) then 13 else
  if p.val = (true, vertices_336) then 14 else
  if p.val = (true, vertices_672) then 15 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_147), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_401), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_162), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_546), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_44), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_52), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_84), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_276), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_292), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_548), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_772), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_168), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_176), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_208), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_336), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_672), by decide +kernel⟩
  | 16 => Sum.inl 0
  | 17 => Sum.inr ⟨(false, vertices_651), by decide +kernel⟩
  | 18 => Sum.inr ⟨(false, vertices_307), by decide +kernel⟩
  | 19 => Sum.inr ⟨(false, vertices_835), by decide +kernel⟩
  | 20 => Sum.inl 1
  | 21 => Sum.inr ⟨(false, vertices_589), by decide +kernel⟩
  | 22 => Sum.inl 2
  | 23 => Sum.inr ⟨(false, vertices_457), by decide +kernel⟩
  | 24 => Sum.inr ⟨(true, vertices_120), by decide +kernel⟩
  | 25 => Sum.inl 3
  | 26 => Sum.inl 4
  | 27 => Sum.inl 5
  | 28 => Sum.inl 6
  | 29 => Sum.inl 7
  | 30 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 4 7 8 806 290 1
cert_row_4 1 1 2 4 6 8 684 44 3
cert_row_2 2 2 3 4 5 120
cert_row_4 3 1 3 5 7 8 852 84 3
cert_rows
cert_pivot_2 0 6 2 1
cert_heightProof 4
cert_coverFacet 0 806
cert_cover_5 0 0 0 1 4 7 290 806 1
cert_coverFacet 1 178
cert_cover_2 1 3 0 4 6 50 178 3
cert_coverFacet 2 674
cert_cover_2 2 4 0 6 8 162 674 3
cert_coverFacet 3 124
cert_cover_5 3 2 1 2 3 4 44 124 2
cert_coverFacet 4 684
cert_cover_5 4 1 1 2 4 6 44 684 3
cert_coverFacet 5 308
cert_cover_2 5 3 1 4 7 52 308 3
cert_coverFacet 6 852
cert_cover_5 6 3 1 3 5 7 84 852 3
cert_coverFacet 7 248
cert_cover_5 7 2 2 3 4 6 120 248 3
cert_coverFacet 8 464
cert_cover_2 8 5 3 6 7 208 464 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0371

end
end BundlePart26

section BundlePart27
/- Source: ProjectionCertificates/R_m16e10q1_0372.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0372

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [395, 677, 313, 665, 561, 481, 94, 142, 230, 282, 850, 450, 604, 652, 868, 816, 25, 137, 265, 49, 529, 161, 289, 545, 385, 641, 14, 70, 134, 26, 138, 266, 82, 274, 194, 322, 386, 92, 140, 524, 100, 164, 548, 580, 644, 280, 536, 648, 304, 560, 592, 784, 224, 352, 800, 448, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_395, vertices_677, vertices_313, vertices_665, vertices_561, vertices_481, vertices_94, vertices_142, vertices_230, vertices_282, vertices_850, vertices_450, vertices_604, vertices_652, vertices_868, vertices_816] (by decide +kernel)
  polygons := literalFinset [vertices_25, vertices_137, vertices_265, vertices_49, vertices_529, vertices_161, vertices_289, vertices_545, vertices_385, vertices_641, vertices_14, vertices_70, vertices_134, vertices_26, vertices_138, vertices_266, vertices_82, vertices_274, vertices_194, vertices_322, vertices_386, vertices_92, vertices_140, vertices_524, vertices_100, vertices_164, vertices_548, vertices_580, vertices_644, vertices_280, vertices_536, vertices_648, vertices_304, vertices_560, vertices_592, vertices_784, vertices_224, vertices_352, vertices_800, vertices_448, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_395), (false, vertices_677), (false, vertices_313), (false, vertices_665), (false, vertices_561), (false, vertices_481), (true, vertices_14), (true, vertices_70), (true, vertices_134), (true, vertices_26), (true, vertices_82), (true, vertices_274), (true, vertices_194), (true, vertices_322), (true, vertices_92), (true, vertices_140), (true, vertices_524), (true, vertices_100), (true, vertices_580), (true, vertices_592), (true, vertices_784), (true, vertices_800), (true, vertices_832)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 17 19 22 25 26 28 29 30 31
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_395) then 18 else
  if p.val = (false, vertices_677) then 20 else
  if p.val = (false, vertices_313) then 23 else
  if p.val = (false, vertices_665) then 24 else
  if p.val = (false, vertices_561) then 0 else
  if p.val = (false, vertices_481) then 27 else
  if p.val = (true, vertices_14) then 1 else
  if p.val = (true, vertices_70) then 2 else
  if p.val = (true, vertices_134) then 3 else
  if p.val = (true, vertices_26) then 4 else
  if p.val = (true, vertices_82) then 5 else
  if p.val = (true, vertices_274) then 6 else
  if p.val = (true, vertices_194) then 7 else
  if p.val = (true, vertices_322) then 8 else
  if p.val = (true, vertices_92) then 21 else
  if p.val = (true, vertices_140) then 9 else
  if p.val = (true, vertices_524) then 10 else
  if p.val = (true, vertices_100) then 11 else
  if p.val = (true, vertices_580) then 12 else
  if p.val = (true, vertices_592) then 13 else
  if p.val = (true, vertices_784) then 14 else
  if p.val = (true, vertices_800) then 15 else
  if p.val = (true, vertices_832) then 16 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_561), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_14), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_70), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_134), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_26), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_82), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_274), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_194), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_322), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_140), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_524), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_100), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_580), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_592), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_784), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_800), by decide +kernel⟩
  | 16 => Sum.inr ⟨(true, vertices_832), by decide +kernel⟩
  | 17 => Sum.inl 0
  | 18 => Sum.inr ⟨(false, vertices_395), by decide +kernel⟩
  | 19 => Sum.inl 1
  | 20 => Sum.inr ⟨(false, vertices_677), by decide +kernel⟩
  | 21 => Sum.inr ⟨(true, vertices_92), by decide +kernel⟩
  | 22 => Sum.inl 2
  | 23 => Sum.inr ⟨(false, vertices_313), by decide +kernel⟩
  | 24 => Sum.inr ⟨(false, vertices_665), by decide +kernel⟩
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
cert_row_2 0 1 2 3 5 92
cert_row_4 1 0 1 4 5 6 230 70 2
cert_row_4 2 0 3 5 7 8 850 82 3
cert_row_4 3 1 4 5 7 8 868 100 3
cert_rows
cert_pivot_2 2 6 0 1
cert_heightProof 4
cert_coverFacet 0 94
cert_cover_5 0 0 0 1 2 3 14 94 3
cert_coverFacet 1 142
cert_cover_2 1 1 0 2 6 14 142 3
cert_coverFacet 2 230
cert_cover_5 2 1 0 1 4 5 70 230 2
cert_coverFacet 3 282
cert_cover_2 3 2 0 3 7 26 282 3
cert_coverFacet 4 850
cert_cover_5 4 2 0 3 5 7 82 850 3
cert_coverFacet 5 450
cert_cover_2 5 5 0 6 7 194 450 3
cert_coverFacet 6 604
cert_cover_5 6 0 1 2 3 8 92 604 3
cert_coverFacet 7 652
cert_cover_2 7 2 1 6 8 140 652 3
cert_coverFacet 8 868
cert_cover_5 8 3 1 4 5 7 100 868 3
cert_coverFacet 9 816
cert_cover_2 9 4 3 7 8 304 816 3
cert_coveringFacets_5
cert_coveringProof
cert_certificate 4 10
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0372

end
end BundlePart27

section BundlePart28
/- Source: ProjectionCertificates/R_m16e10q1_0373.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0373

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [787, 837, 345, 665, 201, 737, 158, 174, 278, 614, 774, 690, 284, 300, 356, 488, 25, 73, 137, 273, 529, 193, 321, 577, 641, 769, 142, 22, 38, 262, 518, 146, 274, 530, 162, 546, 770, 28, 44, 268, 276, 100, 292, 324, 580, 772, 152, 280, 168, 296, 200, 328, 656, 224, 352, 608, 672]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_787, vertices_837, vertices_345, vertices_665, vertices_201, vertices_737, vertices_158, vertices_174, vertices_278, vertices_614, vertices_774, vertices_690, vertices_284, vertices_300, vertices_356, vertices_488] (by decide +kernel)
  polygons := literalFinset [vertices_25, vertices_73, vertices_137, vertices_273, vertices_529, vertices_193, vertices_321, vertices_577, vertices_641, vertices_769, vertices_142, vertices_22, vertices_38, vertices_262, vertices_518, vertices_146, vertices_274, vertices_530, vertices_162, vertices_546, vertices_770, vertices_28, vertices_44, vertices_268, vertices_276, vertices_100, vertices_292, vertices_324, vertices_580, vertices_772, vertices_152, vertices_280, vertices_168, vertices_296, vertices_200, vertices_328, vertices_656, vertices_224, vertices_352, vertices_608, vertices_672] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_787), (false, vertices_837), (false, vertices_345), (false, vertices_665), (false, vertices_201), (false, vertices_737), (true, vertices_142), (true, vertices_22), (true, vertices_38), (true, vertices_262), (true, vertices_518), (true, vertices_146), (true, vertices_162), (true, vertices_546), (true, vertices_28), (true, vertices_44), (true, vertices_268), (true, vertices_276), (true, vertices_100), (true, vertices_292), (true, vertices_168), (true, vertices_296), (true, vertices_352)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 17 20 22 25 26 28 29 30 31
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_787) then 18 else
  if p.val = (false, vertices_837) then 21 else
  if p.val = (false, vertices_345) then 23 else
  if p.val = (false, vertices_665) then 24 else
  if p.val = (false, vertices_201) then 0 else
  if p.val = (false, vertices_737) then 27 else
  if p.val = (true, vertices_142) then 19 else
  if p.val = (true, vertices_22) then 1 else
  if p.val = (true, vertices_38) then 2 else
  if p.val = (true, vertices_262) then 3 else
  if p.val = (true, vertices_518) then 4 else
  if p.val = (true, vertices_146) then 5 else
  if p.val = (true, vertices_162) then 6 else
  if p.val = (true, vertices_546) then 7 else
  if p.val = (true, vertices_28) then 8 else
  if p.val = (true, vertices_44) then 9 else
  if p.val = (true, vertices_268) then 10 else
  if p.val = (true, vertices_276) then 11 else
  if p.val = (true, vertices_100) then 12 else
  if p.val = (true, vertices_292) then 13 else
  if p.val = (true, vertices_168) then 14 else
  if p.val = (true, vertices_296) then 15 else
  if p.val = (true, vertices_352) then 16 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_201), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_22), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_38), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_262), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_518), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_146), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_162), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_546), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_28), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_44), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_268), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_276), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_100), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_292), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_168), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_296), by decide +kernel⟩
  | 16 => Sum.inr ⟨(true, vertices_352), by decide +kernel⟩
  | 17 => Sum.inl 0
  | 18 => Sum.inr ⟨(false, vertices_787), by decide +kernel⟩
  | 19 => Sum.inr ⟨(true, vertices_142), by decide +kernel⟩
  | 20 => Sum.inl 1
  | 21 => Sum.inr ⟨(false, vertices_837), by decide +kernel⟩
  | 22 => Sum.inl 2
  | 23 => Sum.inr ⟨(false, vertices_345), by decide +kernel⟩
  | 24 => Sum.inr ⟨(false, vertices_665), by decide +kernel⟩
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
cert_row_4 0 0 3 4 6 8 690 146 2
cert_row_4 1 0 1 4 5 8 614 38 3
cert_row_2 2 0 1 2 6 142
cert_row_4 3 2 4 5 6 7 488 168 2
cert_rows
cert_pivot_2 3 8 0 2
cert_heightProof 4
cert_coverFacet 0 158
cert_cover_5 0 2 0 1 2 3 142 158 3
cert_coverFacet 1 174
cert_cover_5 1 2 0 1 2 4 142 174 3
cert_coverFacet 2 278
cert_cover_2 2 1 0 3 7 22 278 3
cert_coverFacet 3 614
cert_cover_5 3 1 0 1 4 5 38 614 3
cert_coverFacet 4 774
cert_cover_2 4 1 0 7 8 262 774 3
cert_coverFacet 5 690
cert_cover_5 5 0 0 3 4 6 146 690 2
cert_coverFacet 6 284
cert_cover_2 6 2 1 3 7 28 284 3
cert_coverFacet 7 300
cert_cover_2 7 2 1 4 7 44 300 3
cert_coverFacet 8 356
cert_cover_2 8 4 1 5 7 100 356 3
cert_coverFacet 9 488
cert_cover_5 9 3 2 4 5 6 168 488 2
cert_coveringFacets_5
cert_coveringProof
cert_certificate 4 10
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0373

end
end BundlePart28

section BundlePart29
/- Source: ProjectionCertificates/R_m16e10q1_0374.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0374

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [803, 677, 793, 361, 713, 225, 566, 86, 422, 454, 346, 786, 668, 212, 216, 480, 73, 265, 521, 97, 161, 289, 545, 193, 641, 769, 22, 38, 70, 390, 82, 274, 530, 290, 546, 322, 770, 84, 148, 532, 164, 548, 196, 644, 88, 152, 280, 536, 200, 328, 648, 208, 784, 224, 352, 416, 448]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_803, vertices_677, vertices_793, vertices_361, vertices_713, vertices_225, vertices_566, vertices_86, vertices_422, vertices_454, vertices_346, vertices_786, vertices_668, vertices_212, vertices_216, vertices_480] (by decide +kernel)
  polygons := literalFinset [vertices_73, vertices_265, vertices_521, vertices_97, vertices_161, vertices_289, vertices_545, vertices_193, vertices_641, vertices_769, vertices_22, vertices_38, vertices_70, vertices_390, vertices_82, vertices_274, vertices_530, vertices_290, vertices_546, vertices_322, vertices_770, vertices_84, vertices_148, vertices_532, vertices_164, vertices_548, vertices_196, vertices_644, vertices_88, vertices_152, vertices_280, vertices_536, vertices_200, vertices_328, vertices_648, vertices_208, vertices_784, vertices_224, vertices_352, vertices_416, vertices_448] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_803), (false, vertices_677), (false, vertices_793), (false, vertices_361), (false, vertices_713), (false, vertices_225), (true, vertices_22), (true, vertices_38), (true, vertices_70), (true, vertices_390), (true, vertices_82), (true, vertices_274), (true, vertices_530), (true, vertices_322), (true, vertices_84), (true, vertices_148), (true, vertices_532), (true, vertices_196), (true, vertices_88), (true, vertices_152), (true, vertices_208), (true, vertices_416), (true, vertices_448)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 17 20 22 26 27 28 29 30 31
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_803) then 18 else
  if p.val = (false, vertices_677) then 21 else
  if p.val = (false, vertices_793) then 23 else
  if p.val = (false, vertices_361) then 24 else
  if p.val = (false, vertices_713) then 25 else
  if p.val = (false, vertices_225) then 0 else
  if p.val = (true, vertices_22) then 1 else
  if p.val = (true, vertices_38) then 2 else
  if p.val = (true, vertices_70) then 3 else
  if p.val = (true, vertices_390) then 19 else
  if p.val = (true, vertices_82) then 4 else
  if p.val = (true, vertices_274) then 5 else
  if p.val = (true, vertices_530) then 6 else
  if p.val = (true, vertices_322) then 7 else
  if p.val = (true, vertices_84) then 8 else
  if p.val = (true, vertices_148) then 9 else
  if p.val = (true, vertices_532) then 10 else
  if p.val = (true, vertices_196) then 11 else
  if p.val = (true, vertices_88) then 12 else
  if p.val = (true, vertices_152) then 13 else
  if p.val = (true, vertices_208) then 14 else
  if p.val = (true, vertices_416) then 15 else
  if p.val = (true, vertices_448) then 16 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_225), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_22), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_38), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_70), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_82), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_274), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_530), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_322), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_84), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_148), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_532), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_196), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_88), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_152), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_208), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_416), by decide +kernel⟩
  | 16 => Sum.inr ⟨(true, vertices_448), by decide +kernel⟩
  | 17 => Sum.inl 0
  | 18 => Sum.inr ⟨(false, vertices_803), by decide +kernel⟩
  | 19 => Sum.inr ⟨(true, vertices_390), by decide +kernel⟩
  | 20 => Sum.inl 1
  | 21 => Sum.inr ⟨(false, vertices_677), by decide +kernel⟩
  | 22 => Sum.inl 2
  | 23 => Sum.inr ⟨(false, vertices_793), by decide +kernel⟩
  | 24 => Sum.inr ⟨(false, vertices_361), by decide +kernel⟩
  | 25 => Sum.inr ⟨(false, vertices_713), by decide +kernel⟩
  | 26 => Sum.inl 3
  | 27 => Sum.inl 4
  | 28 => Sum.inl 5
  | 29 => Sum.inl 6
  | 30 => Sum.inl 7
  | 31 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 3 4 8 566 22 3
cert_row_4 1 0 2 3 5 7 346 82 1
cert_row_2 2 0 1 6 7 390
cert_row_4 3 1 2 3 6 8 668 148 1
cert_rows
cert_pivot_2 4 5 0 1
cert_heightProof 4
cert_coverFacet 0 566
cert_cover_5 0 0 0 1 3 4 22 566 3
cert_coverFacet 1 86
cert_cover_2 1 1 0 3 5 22 86 3
cert_coverFacet 2 422
cert_cover_5 2 2 0 1 4 6 38 422 3
cert_coverFacet 3 454
cert_cover_5 3 2 0 1 5 6 70 454 3
cert_coverFacet 4 346
cert_cover_5 4 1 0 2 3 5 82 346 1
cert_coverFacet 5 786
cert_cover_2 5 3 0 7 8 274 786 3
cert_coverFacet 6 668
cert_cover_5 6 3 1 2 3 6 148 668 1
cert_coverFacet 7 212
cert_cover_2 7 3 1 5 6 84 212 3
cert_coverFacet 8 216
cert_cover_2 8 3 2 5 6 88 216 3
cert_coverFacet 9 480
cert_cover_2 9 5 4 6 7 224 480 3
cert_coveringFacets_5
cert_coveringProof
cert_certificate 4 10
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0374

end
end BundlePart29

-- Public target certificates; internal witness data stays private.
namespace Nonrational.TerminalVerification
open Papers.RationalityTen.ChirotopeDensity.FiniteProjection
open Nonrational.TerminalData
set_option maxRecDepth 100000
set_option maxHeartbeats 0

public theorem projection_4233 : Certifies 4233 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0345.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_4234 : Certifies 4234 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0346.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_4235 : Certifies 4235 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0347.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_4236 : Certifies 4236 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0348.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_4237 : Certifies 4237 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0349.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_4238 : Certifies 4238 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0350.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_4239 : Certifies 4239 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0351.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_4240 : Certifies 4240 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0352.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_4241 : Certifies 4241 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0353.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_4242 : Certifies 4242 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0354.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_4243 : Certifies 4243 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0355.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_4244 : Certifies 4244 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0356.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_4245 : Certifies 4245 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0357.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_4246 : Certifies 4246 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0358.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_4247 : Certifies 4247 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0359.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_4248 : Certifies 4248 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0360.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_4249 : Certifies 4249 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0361.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_4250 : Certifies 4250 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0362.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_4251 : Certifies 4251 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0363.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_4252 : Certifies 4252 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0364.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_4253 : Certifies 4253 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0365.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_4254 : Certifies 4254 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0366.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_4255 : Certifies 4255 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0367.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_4256 : Certifies 4256 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0368.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_4257 : Certifies 4257 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0369.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_4258 : Certifies 4258 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0370.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_4259 : Certifies 4259 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0371.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_4260 : Certifies 4260 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0372.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_4261 : Certifies 4261 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0373.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_4262 : Certifies 4262 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0374.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem certified_B140 (j : Fin 30) :
    Certifies (4233 + j.val) := by
  fin_cases j
  · exact projection_4233
  · exact projection_4234
  · exact projection_4235
  · exact projection_4236
  · exact projection_4237
  · exact projection_4238
  · exact projection_4239
  · exact projection_4240
  · exact projection_4241
  · exact projection_4242
  · exact projection_4243
  · exact projection_4244
  · exact projection_4245
  · exact projection_4246
  · exact projection_4247
  · exact projection_4248
  · exact projection_4249
  · exact projection_4250
  · exact projection_4251
  · exact projection_4252
  · exact projection_4253
  · exact projection_4254
  · exact projection_4255
  · exact projection_4256
  · exact projection_4257
  · exact projection_4258
  · exact projection_4259
  · exact projection_4260
  · exact projection_4261
  · exact projection_4262

end Nonrational.TerminalVerification
-- Explicit facial frame witnesses, with lexical vector tracking.
