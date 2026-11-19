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
/- Source: ProjectionCertificates/R_m16e10q1_0284.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0284

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [651, 339, 147, 803, 357, 625, 657, 158, 286, 778, 428, 724, 340, 228, 744, 808, 19, 131, 259, 515, 81, 145, 529, 97, 289, 545, 321, 641, 30, 138, 266, 522, 146, 274, 770, 140, 268, 84, 148, 276, 100, 164, 292, 196, 324, 168, 296, 552, 648, 776, 336, 592, 656, 224, 608, 800, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_651, vertices_339, vertices_147, vertices_803, vertices_357, vertices_625, vertices_657, vertices_158, vertices_286, vertices_778, vertices_428, vertices_724, vertices_340, vertices_228, vertices_744, vertices_808] (by decide +kernel)
  polygons := literalFinset [vertices_19, vertices_131, vertices_259, vertices_515, vertices_81, vertices_145, vertices_529, vertices_97, vertices_289, vertices_545, vertices_321, vertices_641, vertices_30, vertices_138, vertices_266, vertices_522, vertices_146, vertices_274, vertices_770, vertices_140, vertices_268, vertices_84, vertices_148, vertices_276, vertices_100, vertices_164, vertices_292, vertices_196, vertices_324, vertices_168, vertices_296, vertices_552, vertices_648, vertices_776, vertices_336, vertices_592, vertices_656, vertices_224, vertices_608, vertices_800, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_651), (false, vertices_339), (false, vertices_147), (false, vertices_803), (false, vertices_357), (false, vertices_625), (false, vertices_657), (true, vertices_30), (true, vertices_266), (true, vertices_140), (true, vertices_268), (true, vertices_84), (true, vertices_148), (true, vertices_276), (true, vertices_164), (true, vertices_196), (true, vertices_168), (true, vertices_296), (true, vertices_552), (true, vertices_776), (true, vertices_224), (true, vertices_704)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 19 16 23 24 26 27 28 29 30
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_651) then 20 else
  if p.val = (false, vertices_339) then 21 else
  if p.val = (false, vertices_147) then 0 else
  if p.val = (false, vertices_803) then 22 else
  if p.val = (false, vertices_357) then 17 else
  if p.val = (false, vertices_625) then 25 else
  if p.val = (false, vertices_657) then 1 else
  if p.val = (true, vertices_30) then 18 else
  if p.val = (true, vertices_266) then 2 else
  if p.val = (true, vertices_140) then 3 else
  if p.val = (true, vertices_268) then 4 else
  if p.val = (true, vertices_84) then 5 else
  if p.val = (true, vertices_148) then 6 else
  if p.val = (true, vertices_276) then 7 else
  if p.val = (true, vertices_164) then 8 else
  if p.val = (true, vertices_196) then 9 else
  if p.val = (true, vertices_168) then 10 else
  if p.val = (true, vertices_296) then 11 else
  if p.val = (true, vertices_552) then 12 else
  if p.val = (true, vertices_776) then 13 else
  if p.val = (true, vertices_224) then 14 else
  if p.val = (true, vertices_704) then 15 else
  0
cert_priority
cert_nodeAtPriority_21 1 147 0 657 266 140 268 84 148 276 164 196 168 296 552 776 224 704 357 30 651 339 803 625
cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 1 2 3 30
cert_row_4 1 1 2 4 6 7 428 140 2
cert_row_4 2 1 3 5 6 8 724 84 3
cert_row_4 3 2 4 5 6 8 744 168 2
cert_rows
cert_pivot_2 0 7 1 2
cert_heightProof 4
cert_coverFacet 0 158
cert_cover_5 0 0 0 1 2 6 30 158 3
cert_coverFacet 1 286
cert_cover_5 1 0 0 1 2 7 30 286 3
cert_coverFacet 2 778
cert_cover_2 2 2 0 7 8 266 778 3
cert_coverFacet 3 428
cert_cover_5 3 1 1 2 4 6 140 428 2
cert_coverFacet 4 724
cert_cover_5 4 2 1 3 5 6 84 724 3
cert_coverFacet 5 340
cert_cover_2 5 3 1 5 7 84 340 3
cert_coverFacet 6 228
cert_cover_2 6 4 1 5 6 100 228 3
cert_coverFacet 7 744
cert_cover_5 7 3 2 4 5 6 168 744 2
cert_coverFacet 8 808
cert_cover_2 8 4 2 7 8 296 808 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0284

end
end BundlePart0

section BundlePart1
/- Source: ProjectionCertificates/R_m16e10q1_0285.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0285

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [787, 653, 901, 569, 425, 369, 206, 406, 582, 774, 626, 210, 620, 232, 464, 480, 645, 41, 137, 521, 49, 273, 529, 289, 385, 769, 70, 134, 262, 518, 82, 146, 274, 530, 194, 578, 770, 76, 140, 524, 580, 388, 772, 104, 168, 552, 200, 112, 560, 208, 336, 400, 224, 352, 608, 416, 448]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_787, vertices_653, vertices_901, vertices_569, vertices_425, vertices_369, vertices_206, vertices_406, vertices_582, vertices_774, vertices_626, vertices_210, vertices_620, vertices_232, vertices_464, vertices_480] (by decide +kernel)
  polygons := literalFinset [vertices_645, vertices_41, vertices_137, vertices_521, vertices_49, vertices_273, vertices_529, vertices_289, vertices_385, vertices_769, vertices_70, vertices_134, vertices_262, vertices_518, vertices_82, vertices_146, vertices_274, vertices_530, vertices_194, vertices_578, vertices_770, vertices_76, vertices_140, vertices_524, vertices_580, vertices_388, vertices_772, vertices_104, vertices_168, vertices_552, vertices_200, vertices_112, vertices_560, vertices_208, vertices_336, vertices_400, vertices_224, vertices_352, vertices_608, vertices_416, vertices_448] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_787), (false, vertices_653), (false, vertices_901), (false, vertices_569), (false, vertices_425), (false, vertices_369), (true, vertices_70), (true, vertices_134), (true, vertices_262), (true, vertices_518), (true, vertices_82), (true, vertices_146), (true, vertices_194), (true, vertices_578), (true, vertices_76), (true, vertices_580), (true, vertices_104), (true, vertices_200), (true, vertices_208), (true, vertices_400), (true, vertices_224), (true, vertices_608), (true, vertices_448)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 17 19 22 25 27 28 29 30 31
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_787) then 18 else
  if p.val = (false, vertices_653) then 20 else
  if p.val = (false, vertices_901) then 21 else
  if p.val = (false, vertices_569) then 23 else
  if p.val = (false, vertices_425) then 24 else
  if p.val = (false, vertices_369) then 26 else
  if p.val = (true, vertices_70) then 0 else
  if p.val = (true, vertices_134) then 1 else
  if p.val = (true, vertices_262) then 2 else
  if p.val = (true, vertices_518) then 3 else
  if p.val = (true, vertices_82) then 4 else
  if p.val = (true, vertices_146) then 5 else
  if p.val = (true, vertices_194) then 6 else
  if p.val = (true, vertices_578) then 7 else
  if p.val = (true, vertices_76) then 8 else
  if p.val = (true, vertices_580) then 9 else
  if p.val = (true, vertices_104) then 10 else
  if p.val = (true, vertices_200) then 11 else
  if p.val = (true, vertices_208) then 12 else
  if p.val = (true, vertices_400) then 13 else
  if p.val = (true, vertices_224) then 14 else
  if p.val = (true, vertices_608) then 15 else
  if p.val = (true, vertices_448) then 16 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_70), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_134), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_262), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_518), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_82), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_146), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_194), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_578), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_76), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_580), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_104), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_200), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_208), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_400), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_224), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_608), by decide +kernel⟩
  | 16 => Sum.inr ⟨(true, vertices_448), by decide +kernel⟩
  | 17 => Sum.inl 0
  | 18 => Sum.inr ⟨(false, vertices_787), by decide +kernel⟩
  | 19 => Sum.inl 1
  | 20 => Sum.inr ⟨(false, vertices_653), by decide +kernel⟩
  | 21 => Sum.inr ⟨(false, vertices_901), by decide +kernel⟩
  | 22 => Sum.inl 2
  | 23 => Sum.inr ⟨(false, vertices_569), by decide +kernel⟩
  | 24 => Sum.inr ⟨(false, vertices_425), by decide +kernel⟩
  | 25 => Sum.inl 3
  | 26 => Sum.inr ⟨(false, vertices_369), by decide +kernel⟩
  | 27 => Sum.inl 4
  | 28 => Sum.inl 5
  | 29 => Sum.inl 6
  | 30 => Sum.inl 7
  | 31 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 3 6 7 406 134 2
cert_row_4 1 0 1 2 5 6 206 70 2
cert_row_4 2 0 3 4 5 8 626 82 2
cert_row_4 3 1 2 4 5 8 620 76 2
cert_rows
cert_pivot_2 7 6 0 1
cert_heightProof 4
cert_coverFacet 0 206
cert_cover_5 0 1 0 1 2 5 70 206 2
cert_coverFacet 1 406
cert_cover_5 1 0 0 1 3 6 134 406 2
cert_coverFacet 2 582
cert_cover_2 2 1 0 5 8 70 582 3
cert_coverFacet 3 774
cert_cover_2 3 1 0 7 8 262 774 3
cert_coverFacet 4 626
cert_cover_5 4 2 0 3 4 5 82 626 2
cert_coverFacet 5 210
cert_cover_2 5 3 0 5 6 82 210 3
cert_coverFacet 6 620
cert_cover_5 6 3 1 2 4 5 76 620 2
cert_coverFacet 7 232
cert_cover_2 7 4 2 5 6 104 232 3
cert_coverFacet 8 464
cert_cover_2 8 5 3 6 7 208 464 3
cert_coverFacet 9 480
cert_cover_2 9 5 4 6 7 224 480 3
cert_coveringFacets_5
cert_coveringProof
cert_certificate 4 10
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0285

end
end BundlePart1

section BundlePart2
/- Source: ProjectionCertificates/R_m16e10q1_0286.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0286

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [775, 555, 403, 163, 341, 661, 673, 234, 394, 778, 364, 812, 596, 612, 472, 752, 35, 131, 259, 515, 21, 261, 517, 145, 273, 161, 545, 641, 42, 138, 266, 522, 162, 386, 770, 300, 84, 532, 100, 548, 324, 580, 772, 104, 552, 200, 328, 392, 776, 208, 336, 592, 400, 656, 224, 608, 672]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_775, vertices_555, vertices_403, vertices_163, vertices_341, vertices_661, vertices_673, vertices_234, vertices_394, vertices_778, vertices_364, vertices_812, vertices_596, vertices_612, vertices_472, vertices_752] (by decide +kernel)
  polygons := literalFinset [vertices_35, vertices_131, vertices_259, vertices_515, vertices_21, vertices_261, vertices_517, vertices_145, vertices_273, vertices_161, vertices_545, vertices_641, vertices_42, vertices_138, vertices_266, vertices_522, vertices_162, vertices_386, vertices_770, vertices_300, vertices_84, vertices_532, vertices_100, vertices_548, vertices_324, vertices_580, vertices_772, vertices_104, vertices_552, vertices_200, vertices_328, vertices_392, vertices_776, vertices_208, vertices_336, vertices_592, vertices_400, vertices_656, vertices_224, vertices_608, vertices_672] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_775), (false, vertices_555), (false, vertices_403), (false, vertices_163), (false, vertices_341), (false, vertices_661), (false, vertices_673), (true, vertices_138), (true, vertices_266), (true, vertices_300), (true, vertices_100), (true, vertices_548), (true, vertices_580), (true, vertices_104), (true, vertices_200), (true, vertices_328), (true, vertices_392), (true, vertices_776), (true, vertices_208), (true, vertices_592), (true, vertices_224), (true, vertices_608)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 16 20 24 25 26 27 28 29 30
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_775) then 17 else
  if p.val = (false, vertices_555) then 18 else
  if p.val = (false, vertices_403) then 19 else
  if p.val = (false, vertices_163) then 0 else
  if p.val = (false, vertices_341) then 21 else
  if p.val = (false, vertices_661) then 22 else
  if p.val = (false, vertices_673) then 1 else
  if p.val = (true, vertices_138) then 2 else
  if p.val = (true, vertices_266) then 3 else
  if p.val = (true, vertices_300) then 23 else
  if p.val = (true, vertices_100) then 4 else
  if p.val = (true, vertices_548) then 5 else
  if p.val = (true, vertices_580) then 6 else
  if p.val = (true, vertices_104) then 7 else
  if p.val = (true, vertices_200) then 8 else
  if p.val = (true, vertices_328) then 9 else
  if p.val = (true, vertices_392) then 10 else
  if p.val = (true, vertices_776) then 11 else
  if p.val = (true, vertices_208) then 12 else
  if p.val = (true, vertices_592) then 13 else
  if p.val = (true, vertices_224) then 14 else
  if p.val = (true, vertices_608) then 15 else
  0
cert_priority
cert_nodeAtPriority_6 163 673 138 266 100 548 580 104 200 328 392 776 208 592 224 608 775 555 403 341 661 300
cert_priority_injective
cert_incidenceProof
cert_row_2 0 1 2 4 7 300
cert_row_4 1 0 2 4 5 6 234 42 3
cert_row_4 2 2 3 5 6 7 472 200 1
cert_row_4 3 3 4 5 6 8 752 208 1
cert_rows
cert_pivot_2 1 0 2 3
cert_heightProof 4
cert_coverFacet 0 234
cert_cover_5 0 1 0 2 4 5 42 234 3
cert_coverFacet 1 394
cert_cover_2 1 2 0 6 7 138 394 3
cert_coverFacet 2 778
cert_cover_2 2 2 0 7 8 266 778 3
cert_coverFacet 3 364
cert_cover_5 3 0 1 2 4 5 300 364 3
cert_coverFacet 4 812
cert_cover_5 4 0 1 2 4 8 300 812 3
cert_coverFacet 5 596
cert_cover_2 5 3 1 5 8 84 596 3
cert_coverFacet 6 612
cert_cover_2 6 4 1 5 8 100 612 3
cert_coverFacet 7 472
cert_cover_5 7 2 2 3 5 6 200 472 1
cert_coverFacet 8 752
cert_cover_5 8 3 3 4 5 6 208 752 1
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0286

end
end BundlePart2

section BundlePart3
/- Source: ProjectionCertificates/R_m16e10q1_0287.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0287

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [211, 611, 899, 805, 361, 465, 662, 602, 156, 540, 620, 172, 420, 900, 440, 344, 67, 131, 515, 209, 97, 289, 545, 321, 385, 769, 82, 146, 530, 578, 642, 28, 44, 140, 524, 148, 532, 164, 292, 548, 388, 644, 772, 88, 152, 280, 536, 104, 168, 296, 328, 584, 336, 400, 608, 416, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_211, vertices_611, vertices_899, vertices_805, vertices_361, vertices_465, vertices_662, vertices_602, vertices_156, vertices_540, vertices_620, vertices_172, vertices_420, vertices_900, vertices_440, vertices_344] (by decide +kernel)
  polygons := literalFinset [vertices_67, vertices_131, vertices_515, vertices_209, vertices_97, vertices_289, vertices_545, vertices_321, vertices_385, vertices_769, vertices_82, vertices_146, vertices_530, vertices_578, vertices_642, vertices_28, vertices_44, vertices_140, vertices_524, vertices_148, vertices_532, vertices_164, vertices_292, vertices_548, vertices_388, vertices_644, vertices_772, vertices_88, vertices_152, vertices_280, vertices_536, vertices_104, vertices_168, vertices_296, vertices_328, vertices_584, vertices_336, vertices_400, vertices_608, vertices_416, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_211), (false, vertices_611), (false, vertices_899), (false, vertices_805), (false, vertices_361), (false, vertices_465), (true, vertices_530), (true, vertices_28), (true, vertices_44), (true, vertices_140), (true, vertices_524), (true, vertices_148), (true, vertices_532), (true, vertices_164), (true, vertices_388), (true, vertices_644), (true, vertices_88), (true, vertices_152), (true, vertices_280), (true, vertices_536), (true, vertices_168), (true, vertices_584), (true, vertices_416)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 17 20 22 24 27 28 29 30 31
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_211) then 25 else
  if p.val = (false, vertices_611) then 18 else
  if p.val = (false, vertices_899) then 19 else
  if p.val = (false, vertices_805) then 21 else
  if p.val = (false, vertices_361) then 23 else
  if p.val = (false, vertices_465) then 26 else
  if p.val = (true, vertices_530) then 0 else
  if p.val = (true, vertices_28) then 1 else
  if p.val = (true, vertices_44) then 2 else
  if p.val = (true, vertices_140) then 3 else
  if p.val = (true, vertices_524) then 4 else
  if p.val = (true, vertices_148) then 5 else
  if p.val = (true, vertices_532) then 6 else
  if p.val = (true, vertices_164) then 7 else
  if p.val = (true, vertices_388) then 8 else
  if p.val = (true, vertices_644) then 9 else
  if p.val = (true, vertices_88) then 10 else
  if p.val = (true, vertices_152) then 11 else
  if p.val = (true, vertices_280) then 12 else
  if p.val = (true, vertices_536) then 13 else
  if p.val = (true, vertices_168) then 14 else
  if p.val = (true, vertices_584) then 15 else
  if p.val = (true, vertices_416) then 16 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_530), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_28), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_44), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_140), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_524), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_148), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_532), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_164), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_388), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_644), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_88), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_152), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_280), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_536), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_168), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_584), by decide +kernel⟩
  | 16 => Sum.inr ⟨(true, vertices_416), by decide +kernel⟩
  | 17 => Sum.inl 0
  | 18 => Sum.inr ⟨(false, vertices_611), by decide +kernel⟩
  | 19 => Sum.inr ⟨(false, vertices_899), by decide +kernel⟩
  | 20 => Sum.inl 1
  | 21 => Sum.inr ⟨(false, vertices_805), by decide +kernel⟩
  | 22 => Sum.inl 2
  | 23 => Sum.inr ⟨(false, vertices_361), by decide +kernel⟩
  | 24 => Sum.inl 3
  | 25 => Sum.inr ⟨(false, vertices_211), by decide +kernel⟩
  | 26 => Sum.inr ⟨(false, vertices_465), by decide +kernel⟩
  | 27 => Sum.inl 4
  | 28 => Sum.inl 5
  | 29 => Sum.inl 6
  | 30 => Sum.inl 7
  | 31 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 2 3 4 6 7 440 152 2
cert_row_4 1 0 1 3 6 8 662 146 1
cert_row_4 2 0 2 3 5 8 602 82 1
cert_row_4 3 1 2 4 5 8 620 44 3
cert_rows
cert_pivot_2 7 6 0 1
cert_heightProof 4
cert_coverFacet 0 662
cert_cover_5 0 1 0 1 3 6 146 662 1
cert_coverFacet 1 602
cert_cover_5 1 2 0 2 3 5 82 602 1
cert_coverFacet 2 156
cert_cover_2 2 2 1 3 6 28 156 3
cert_coverFacet 3 540
cert_cover_2 3 2 1 3 8 28 540 3
cert_coverFacet 4 620
cert_cover_5 4 3 1 2 4 5 44 620 3
cert_coverFacet 5 172
cert_cover_2 5 2 1 4 6 44 172 3
cert_coverFacet 6 420
cert_cover_2 6 4 1 6 7 164 420 3
cert_coverFacet 7 900
cert_cover_2 7 6 1 7 8 388 900 3
cert_coverFacet 8 440
cert_cover_5 8 0 2 3 4 6 152 440 2
cert_coverFacet 9 344
cert_cover_2 9 3 2 5 7 88 344 3
cert_coveringFacets_5
cert_coveringProof
cert_certificate 4 10
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0287

end
end BundlePart3

section BundlePart4
/- Source: ProjectionCertificates/R_m16e10q1_0288.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0288

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [651, 179, 787, 781, 345, 201, 241, 678, 626, 428, 652, 852, 356, 612, 456, 480, 19, 131, 515, 73, 137, 265, 521, 177, 81, 273, 193, 769, 50, 530, 162, 546, 642, 140, 268, 524, 100, 164, 292, 548, 324, 580, 644, 772, 200, 328, 392, 648, 112, 336, 592, 784, 224, 352, 608, 416, 448]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_651, vertices_179, vertices_787, vertices_781, vertices_345, vertices_201, vertices_241, vertices_678, vertices_626, vertices_428, vertices_652, vertices_852, vertices_356, vertices_612, vertices_456, vertices_480] (by decide +kernel)
  polygons := literalFinset [vertices_19, vertices_131, vertices_515, vertices_73, vertices_137, vertices_265, vertices_521, vertices_177, vertices_81, vertices_273, vertices_193, vertices_769, vertices_50, vertices_530, vertices_162, vertices_546, vertices_642, vertices_140, vertices_268, vertices_524, vertices_100, vertices_164, vertices_292, vertices_548, vertices_324, vertices_580, vertices_644, vertices_772, vertices_200, vertices_328, vertices_392, vertices_648, vertices_112, vertices_336, vertices_592, vertices_784, vertices_224, vertices_352, vertices_608, vertices_416, vertices_448] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_651), (false, vertices_179), (false, vertices_787), (false, vertices_781), (false, vertices_345), (false, vertices_201), (false, vertices_241), (true, vertices_546), (true, vertices_140), (true, vertices_100), (true, vertices_164), (true, vertices_292), (true, vertices_548), (true, vertices_324), (true, vertices_580), (true, vertices_644), (true, vertices_392), (true, vertices_592), (true, vertices_352), (true, vertices_608), (true, vertices_416), (true, vertices_448)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 16 19 21 23 26 27 28 29 30
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_651) then 17 else
  if p.val = (false, vertices_179) then 24 else
  if p.val = (false, vertices_787) then 18 else
  if p.val = (false, vertices_781) then 20 else
  if p.val = (false, vertices_345) then 22 else
  if p.val = (false, vertices_201) then 0 else
  if p.val = (false, vertices_241) then 25 else
  if p.val = (true, vertices_546) then 1 else
  if p.val = (true, vertices_140) then 2 else
  if p.val = (true, vertices_100) then 3 else
  if p.val = (true, vertices_164) then 4 else
  if p.val = (true, vertices_292) then 5 else
  if p.val = (true, vertices_548) then 6 else
  if p.val = (true, vertices_324) then 7 else
  if p.val = (true, vertices_580) then 8 else
  if p.val = (true, vertices_644) then 9 else
  if p.val = (true, vertices_392) then 10 else
  if p.val = (true, vertices_592) then 11 else
  if p.val = (true, vertices_352) then 12 else
  if p.val = (true, vertices_608) then 13 else
  if p.val = (true, vertices_416) then 14 else
  if p.val = (true, vertices_448) then 15 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_201), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_546), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_140), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_100), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_164), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_292), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_548), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_324), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_580), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_644), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_392), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_592), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_352), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_608), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_416), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_448), by decide +kernel⟩
  | 16 => Sum.inl 0
  | 17 => Sum.inr ⟨(false, vertices_651), by decide +kernel⟩
  | 18 => Sum.inr ⟨(false, vertices_787), by decide +kernel⟩
  | 19 => Sum.inl 1
  | 20 => Sum.inr ⟨(false, vertices_781), by decide +kernel⟩
  | 21 => Sum.inl 2
  | 22 => Sum.inr ⟨(false, vertices_345), by decide +kernel⟩
  | 23 => Sum.inl 3
  | 24 => Sum.inr ⟨(false, vertices_179), by decide +kernel⟩
  | 25 => Sum.inr ⟨(false, vertices_241), by decide +kernel⟩
  | 26 => Sum.inl 4
  | 27 => Sum.inl 5
  | 28 => Sum.inl 6
  | 29 => Sum.inl 7
  | 30 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 1 2 4 6 7 428 140 2
cert_row_4 1 0 1 4 6 8 678 162 1
cert_row_4 2 0 3 4 5 8 626 50 3
cert_row_4 3 1 3 5 7 8 852 324 1
cert_rows
cert_pivot_2 2 6 0 1
cert_heightProof 4
cert_coverFacet 0 678
cert_cover_5 0 1 0 1 4 6 162 678 1
cert_coverFacet 1 626
cert_cover_5 1 2 0 3 4 5 50 626 3
cert_coverFacet 2 428
cert_cover_5 2 0 1 2 4 6 140 428 2
cert_coverFacet 3 652
cert_cover_2 3 2 1 6 8 140 652 3
cert_coverFacet 4 852
cert_cover_5 4 3 1 3 5 7 324 852 1
cert_coverFacet 5 356
cert_cover_2 5 4 1 5 7 100 356 3
cert_coverFacet 6 612
cert_cover_2 6 4 1 5 8 100 612 3
cert_coverFacet 7 456
cert_cover_2 7 5 2 6 7 200 456 3
cert_coverFacet 8 480
cert_cover_2 8 5 4 6 7 224 480 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0288

end
end BundlePart4

section BundlePart5
/- Source: ProjectionCertificates/R_m16e10q1_0289.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0289

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [787, 653, 901, 569, 425, 369, 590, 406, 198, 774, 626, 210, 236, 616, 464, 480, 645, 41, 137, 521, 49, 273, 529, 289, 385, 769, 70, 134, 262, 518, 82, 146, 274, 530, 194, 578, 770, 76, 140, 524, 196, 388, 772, 104, 168, 552, 584, 112, 560, 208, 336, 400, 224, 352, 608, 416, 448]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_787, vertices_653, vertices_901, vertices_569, vertices_425, vertices_369, vertices_590, vertices_406, vertices_198, vertices_774, vertices_626, vertices_210, vertices_236, vertices_616, vertices_464, vertices_480] (by decide +kernel)
  polygons := literalFinset [vertices_645, vertices_41, vertices_137, vertices_521, vertices_49, vertices_273, vertices_529, vertices_289, vertices_385, vertices_769, vertices_70, vertices_134, vertices_262, vertices_518, vertices_82, vertices_146, vertices_274, vertices_530, vertices_194, vertices_578, vertices_770, vertices_76, vertices_140, vertices_524, vertices_196, vertices_388, vertices_772, vertices_104, vertices_168, vertices_552, vertices_584, vertices_112, vertices_560, vertices_208, vertices_336, vertices_400, vertices_224, vertices_352, vertices_608, vertices_416, vertices_448] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_787), (false, vertices_653), (false, vertices_901), (false, vertices_569), (false, vertices_425), (false, vertices_369), (true, vertices_70), (true, vertices_134), (true, vertices_262), (true, vertices_518), (true, vertices_82), (true, vertices_146), (true, vertices_194), (true, vertices_578), (true, vertices_76), (true, vertices_196), (true, vertices_104), (true, vertices_584), (true, vertices_208), (true, vertices_400), (true, vertices_224), (true, vertices_608), (true, vertices_448)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 17 19 22 25 27 28 29 30 31
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_787) then 18 else
  if p.val = (false, vertices_653) then 20 else
  if p.val = (false, vertices_901) then 21 else
  if p.val = (false, vertices_569) then 23 else
  if p.val = (false, vertices_425) then 24 else
  if p.val = (false, vertices_369) then 26 else
  if p.val = (true, vertices_70) then 0 else
  if p.val = (true, vertices_134) then 1 else
  if p.val = (true, vertices_262) then 2 else
  if p.val = (true, vertices_518) then 3 else
  if p.val = (true, vertices_82) then 4 else
  if p.val = (true, vertices_146) then 5 else
  if p.val = (true, vertices_194) then 6 else
  if p.val = (true, vertices_578) then 7 else
  if p.val = (true, vertices_76) then 8 else
  if p.val = (true, vertices_196) then 9 else
  if p.val = (true, vertices_104) then 10 else
  if p.val = (true, vertices_584) then 11 else
  if p.val = (true, vertices_208) then 12 else
  if p.val = (true, vertices_400) then 13 else
  if p.val = (true, vertices_224) then 14 else
  if p.val = (true, vertices_608) then 15 else
  if p.val = (true, vertices_448) then 16 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_70), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_134), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_262), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_518), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_82), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_146), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_194), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_578), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_76), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_196), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_104), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_584), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_208), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_400), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_224), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_608), by decide +kernel⟩
  | 16 => Sum.inr ⟨(true, vertices_448), by decide +kernel⟩
  | 17 => Sum.inl 0
  | 18 => Sum.inr ⟨(false, vertices_787), by decide +kernel⟩
  | 19 => Sum.inl 1
  | 20 => Sum.inr ⟨(false, vertices_653), by decide +kernel⟩
  | 21 => Sum.inr ⟨(false, vertices_901), by decide +kernel⟩
  | 22 => Sum.inl 2
  | 23 => Sum.inr ⟨(false, vertices_569), by decide +kernel⟩
  | 24 => Sum.inr ⟨(false, vertices_425), by decide +kernel⟩
  | 25 => Sum.inl 3
  | 26 => Sum.inr ⟨(false, vertices_369), by decide +kernel⟩
  | 27 => Sum.inl 4
  | 28 => Sum.inl 5
  | 29 => Sum.inl 6
  | 30 => Sum.inl 7
  | 31 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 3 6 7 406 134 2
cert_row_4 1 0 3 4 5 8 626 82 2
cert_row_4 2 0 1 2 5 8 590 70 2
cert_row_4 3 1 2 4 5 6 236 76 2
cert_rows
cert_pivot_2 7 3 0 1
cert_heightProof 4
cert_coverFacet 0 590
cert_cover_5 0 2 0 1 2 5 70 590 2
cert_coverFacet 1 406
cert_cover_5 1 0 0 1 3 6 134 406 2
cert_coverFacet 2 198
cert_cover_2 2 1 0 5 6 70 198 3
cert_coverFacet 3 774
cert_cover_2 3 1 0 7 8 262 774 3
cert_coverFacet 4 626
cert_cover_5 4 1 0 3 4 5 82 626 2
cert_coverFacet 5 210
cert_cover_2 5 3 0 5 6 82 210 3
cert_coverFacet 6 236
cert_cover_5 6 3 1 2 4 5 76 236 2
cert_coverFacet 7 616
cert_cover_2 7 4 2 5 8 104 616 3
cert_coverFacet 8 464
cert_cover_2 8 5 3 6 7 208 464 3
cert_coverFacet 9 480
cert_cover_2 9 5 4 6 7 224 480 3
cert_coveringFacets_5
cert_coveringProof
cert_certificate 4 10
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0289

end
end BundlePart5

section BundlePart6
/- Source: ProjectionCertificates/R_m16e10q1_0290.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0290

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [899, 109, 781, 181, 645, 457, 225, 662, 842, 434, 338, 594, 572, 632, 368, 480, 13, 37, 133, 517, 73, 265, 97, 161, 193, 385, 641, 769, 82, 146, 274, 530, 322, 578, 386, 642, 770, 44, 524, 52, 148, 532, 644, 568, 104, 328, 584, 776, 112, 176, 304, 336, 592, 224, 352, 416, 448]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_899, vertices_109, vertices_781, vertices_181, vertices_645, vertices_457, vertices_225, vertices_662, vertices_842, vertices_434, vertices_338, vertices_594, vertices_572, vertices_632, vertices_368, vertices_480] (by decide +kernel)
  polygons := literalFinset [vertices_13, vertices_37, vertices_133, vertices_517, vertices_73, vertices_265, vertices_97, vertices_161, vertices_193, vertices_385, vertices_641, vertices_769, vertices_82, vertices_146, vertices_274, vertices_530, vertices_322, vertices_578, vertices_386, vertices_642, vertices_770, vertices_44, vertices_524, vertices_52, vertices_148, vertices_532, vertices_644, vertices_568, vertices_104, vertices_328, vertices_584, vertices_776, vertices_112, vertices_176, vertices_304, vertices_336, vertices_592, vertices_224, vertices_352, vertices_416, vertices_448] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_899), (false, vertices_109), (false, vertices_781), (false, vertices_181), (false, vertices_645), (false, vertices_457), (false, vertices_225), (true, vertices_82), (true, vertices_146), (true, vertices_274), (true, vertices_530), (true, vertices_322), (true, vertices_578), (true, vertices_532), (true, vertices_568), (true, vertices_584), (true, vertices_112), (true, vertices_304), (true, vertices_336), (true, vertices_592), (true, vertices_352), (true, vertices_416)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 16 18 22 25 26 27 28 29 30
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_899) then 17 else
  if p.val = (false, vertices_109) then 19 else
  if p.val = (false, vertices_781) then 20 else
  if p.val = (false, vertices_181) then 21 else
  if p.val = (false, vertices_645) then 0 else
  if p.val = (false, vertices_457) then 23 else
  if p.val = (false, vertices_225) then 1 else
  if p.val = (true, vertices_82) then 2 else
  if p.val = (true, vertices_146) then 3 else
  if p.val = (true, vertices_274) then 4 else
  if p.val = (true, vertices_530) then 5 else
  if p.val = (true, vertices_322) then 6 else
  if p.val = (true, vertices_578) then 7 else
  if p.val = (true, vertices_532) then 8 else
  if p.val = (true, vertices_568) then 24 else
  if p.val = (true, vertices_584) then 9 else
  if p.val = (true, vertices_112) then 10 else
  if p.val = (true, vertices_304) then 11 else
  if p.val = (true, vertices_336) then 12 else
  if p.val = (true, vertices_592) then 13 else
  if p.val = (true, vertices_352) then 14 else
  if p.val = (true, vertices_416) then 15 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_645), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_225), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_82), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_146), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_274), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_530), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_322), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_578), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_532), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_584), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_112), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_304), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_336), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_592), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_352), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_416), by decide +kernel⟩
  | 16 => Sum.inl 0
  | 17 => Sum.inr ⟨(false, vertices_899), by decide +kernel⟩
  | 18 => Sum.inl 1
  | 19 => Sum.inr ⟨(false, vertices_109), by decide +kernel⟩
  | 20 => Sum.inr ⟨(false, vertices_781), by decide +kernel⟩
  | 21 => Sum.inr ⟨(false, vertices_181), by decide +kernel⟩
  | 22 => Sum.inl 2
  | 23 => Sum.inr ⟨(false, vertices_457), by decide +kernel⟩
  | 24 => Sum.inr ⟨(true, vertices_568), by decide +kernel⟩
  | 25 => Sum.inl 3
  | 26 => Sum.inl 4
  | 27 => Sum.inl 5
  | 28 => Sum.inl 6
  | 29 => Sum.inl 7
  | 30 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 3 6 8 662 146 1
cert_row_4 1 0 2 5 7 8 842 322 1
cert_row_2 2 2 3 4 8 568
cert_row_4 3 0 3 4 6 7 434 146 2
cert_rows
cert_pivot_2 1 5 2 0
cert_heightProof 4
cert_coverFacet 0 662
cert_cover_5 0 0 0 1 3 6 146 662 1
cert_coverFacet 1 842
cert_cover_5 1 1 0 2 5 7 322 842 1
cert_coverFacet 2 434
cert_cover_5 2 3 0 3 4 6 146 434 2
cert_coverFacet 3 338
cert_cover_2 3 3 0 5 7 82 338 3
cert_coverFacet 4 594
cert_cover_2 4 3 0 5 8 82 594 3
cert_coverFacet 5 572
cert_cover_5 5 2 1 2 3 4 44 572 2
cert_coverFacet 6 632
cert_cover_5 6 2 2 3 4 5 568 632 3
cert_coverFacet 7 368
cert_cover_2 7 4 3 5 7 112 368 3
cert_coverFacet 8 480
cert_cover_2 8 5 4 6 7 224 480 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0290

end
end BundlePart6

section BundlePart7
/- Source: ProjectionCertificates/R_m16e10q1_0291.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0291

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [59, 283, 803, 405, 689, 961, 110, 458, 610, 834, 60, 284, 716, 396, 628, 660, 27, 35, 259, 49, 145, 273, 545, 385, 641, 769, 42, 74, 266, 98, 546, 322, 578, 770, 28, 44, 76, 140, 268, 52, 148, 276, 532, 100, 580, 388, 644, 56, 280, 200, 392, 560, 656, 608, 448, 704, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_59, vertices_283, vertices_803, vertices_405, vertices_689, vertices_961, vertices_110, vertices_458, vertices_610, vertices_834, vertices_60, vertices_284, vertices_716, vertices_396, vertices_628, vertices_660] (by decide +kernel)
  polygons := literalFinset [vertices_27, vertices_35, vertices_259, vertices_49, vertices_145, vertices_273, vertices_545, vertices_385, vertices_641, vertices_769, vertices_42, vertices_74, vertices_266, vertices_98, vertices_546, vertices_322, vertices_578, vertices_770, vertices_28, vertices_44, vertices_76, vertices_140, vertices_268, vertices_52, vertices_148, vertices_276, vertices_532, vertices_100, vertices_580, vertices_388, vertices_644, vertices_56, vertices_280, vertices_200, vertices_392, vertices_560, vertices_656, vertices_608, vertices_448, vertices_704, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_59), (false, vertices_283), (false, vertices_803), (false, vertices_405), (false, vertices_689), (false, vertices_961), (true, vertices_74), (true, vertices_98), (true, vertices_322), (true, vertices_578), (true, vertices_28), (true, vertices_44), (true, vertices_76), (true, vertices_140), (true, vertices_268), (true, vertices_52), (true, vertices_532), (true, vertices_100), (true, vertices_580), (true, vertices_644), (true, vertices_200), (true, vertices_392), (true, vertices_608)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 17 21 23 24 26 27 29 30 31
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_59) then 18 else
  if p.val = (false, vertices_283) then 19 else
  if p.val = (false, vertices_803) then 20 else
  if p.val = (false, vertices_405) then 22 else
  if p.val = (false, vertices_689) then 25 else
  if p.val = (false, vertices_961) then 28 else
  if p.val = (true, vertices_74) then 0 else
  if p.val = (true, vertices_98) then 1 else
  if p.val = (true, vertices_322) then 2 else
  if p.val = (true, vertices_578) then 3 else
  if p.val = (true, vertices_28) then 4 else
  if p.val = (true, vertices_44) then 5 else
  if p.val = (true, vertices_76) then 6 else
  if p.val = (true, vertices_140) then 7 else
  if p.val = (true, vertices_268) then 8 else
  if p.val = (true, vertices_52) then 9 else
  if p.val = (true, vertices_532) then 10 else
  if p.val = (true, vertices_100) then 11 else
  if p.val = (true, vertices_580) then 12 else
  if p.val = (true, vertices_644) then 13 else
  if p.val = (true, vertices_200) then 14 else
  if p.val = (true, vertices_392) then 15 else
  if p.val = (true, vertices_608) then 16 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_74), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_98), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_322), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_578), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_28), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_44), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_76), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_140), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_268), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_52), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_532), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_100), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_580), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_644), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_200), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_392), by decide +kernel⟩
  | 16 => Sum.inr ⟨(true, vertices_608), by decide +kernel⟩
  | 17 => Sum.inl 0
  | 18 => Sum.inr ⟨(false, vertices_59), by decide +kernel⟩
  | 19 => Sum.inr ⟨(false, vertices_283), by decide +kernel⟩
  | 20 => Sum.inr ⟨(false, vertices_803), by decide +kernel⟩
  | 21 => Sum.inl 1
  | 22 => Sum.inr ⟨(false, vertices_405), by decide +kernel⟩
  | 23 => Sum.inl 2
  | 24 => Sum.inl 3
  | 25 => Sum.inr ⟨(false, vertices_689), by decide +kernel⟩
  | 26 => Sum.inl 4
  | 27 => Sum.inl 5
  | 28 => Sum.inr ⟨(false, vertices_961), by decide +kernel⟩
  | 29 => Sum.inl 6
  | 30 => Sum.inl 7
  | 31 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 2 5 6 7 458 74 3
cert_row_4 1 0 1 2 4 5 110 42 1
cert_row_4 2 1 2 5 6 8 716 76 3
cert_row_4 3 1 3 4 5 8 628 52 3
cert_rows
cert_pivot_2 7 0 2 1
cert_heightProof 4
cert_coverFacet 0 110
cert_cover_5 0 1 0 1 2 4 42 110 1
cert_coverFacet 1 458
cert_cover_5 1 0 0 2 5 6 74 458 3
cert_coverFacet 2 610
cert_cover_2 2 4 0 5 8 98 610 3
cert_coverFacet 3 834
cert_cover_2 3 5 0 7 8 322 834 3
cert_coverFacet 4 60
cert_cover_2 4 2 1 3 4 28 60 3
cert_coverFacet 5 284
cert_cover_2 5 2 1 3 7 28 284 3
cert_coverFacet 6 716
cert_cover_5 6 2 1 2 5 6 76 716 3
cert_coverFacet 7 396
cert_cover_2 7 2 1 6 7 140 396 3
cert_coverFacet 8 628
cert_cover_5 8 3 1 3 4 5 52 628 3
cert_coverFacet 9 660
cert_cover_2 9 3 1 6 8 148 660 3
cert_coveringFacets_5
cert_coveringProof
cert_certificate 4 10
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0291

end
end BundlePart7

section BundlePart8
/- Source: ProjectionCertificates/R_m16e10q1_0292.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0292

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [659, 557, 357, 709, 217, 537, 105, 310, 566, 774, 410, 962, 836, 312, 568, 488, 37, 69, 517, 25, 41, 73, 521, 145, 529, 97, 193, 641, 54, 262, 518, 146, 274, 530, 386, 642, 770, 292, 548, 324, 580, 772, 56, 152, 280, 536, 104, 296, 552, 200, 392, 304, 560, 352, 448, 704, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_659, vertices_557, vertices_357, vertices_709, vertices_217, vertices_537, vertices_105, vertices_310, vertices_566, vertices_774, vertices_410, vertices_962, vertices_836, vertices_312, vertices_568, vertices_488] (by decide +kernel)
  polygons := literalFinset [vertices_37, vertices_69, vertices_517, vertices_25, vertices_41, vertices_73, vertices_521, vertices_145, vertices_529, vertices_97, vertices_193, vertices_641, vertices_54, vertices_262, vertices_518, vertices_146, vertices_274, vertices_530, vertices_386, vertices_642, vertices_770, vertices_292, vertices_548, vertices_324, vertices_580, vertices_772, vertices_56, vertices_152, vertices_280, vertices_536, vertices_104, vertices_296, vertices_552, vertices_200, vertices_392, vertices_304, vertices_560, vertices_352, vertices_448, vertices_704, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_659), (false, vertices_557), (false, vertices_357), (false, vertices_709), (false, vertices_217), (false, vertices_537), (false, vertices_105), (true, vertices_54), (true, vertices_262), (true, vertices_518), (true, vertices_274), (true, vertices_386), (true, vertices_770), (true, vertices_772), (true, vertices_56), (true, vertices_280), (true, vertices_296), (true, vertices_392), (true, vertices_304), (true, vertices_560), (true, vertices_448), (true, vertices_832)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 16 19 23 25 26 27 28 29 30
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_659) then 17 else
  if p.val = (false, vertices_557) then 20 else
  if p.val = (false, vertices_357) then 21 else
  if p.val = (false, vertices_709) then 22 else
  if p.val = (false, vertices_217) then 24 else
  if p.val = (false, vertices_537) then 0 else
  if p.val = (false, vertices_105) then 1 else
  if p.val = (true, vertices_54) then 18 else
  if p.val = (true, vertices_262) then 2 else
  if p.val = (true, vertices_518) then 3 else
  if p.val = (true, vertices_274) then 4 else
  if p.val = (true, vertices_386) then 5 else
  if p.val = (true, vertices_770) then 6 else
  if p.val = (true, vertices_772) then 7 else
  if p.val = (true, vertices_56) then 8 else
  if p.val = (true, vertices_280) then 9 else
  if p.val = (true, vertices_296) then 10 else
  if p.val = (true, vertices_392) then 11 else
  if p.val = (true, vertices_304) then 12 else
  if p.val = (true, vertices_560) then 13 else
  if p.val = (true, vertices_448) then 14 else
  if p.val = (true, vertices_832) then 15 else
  0
cert_priority
cert_nodeAtPriority_5 0 537 1 105 262 518 274 386 770 772 56 280 296 392 304 560 448 832 659 54 557 357 709 217
cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 1 3 4 54
cert_row_4 1 0 2 3 6 7 410 146 1
cert_row_4 2 0 5 6 7 8 962 386 1
cert_row_4 3 2 4 5 6 7 488 104 3
cert_rows
cert_pivot_2 1 3 0 2
cert_heightProof 4
cert_coverFacet 0 310
cert_cover_5 0 0 0 1 3 7 54 310 3
cert_coverFacet 1 566
cert_cover_5 1 0 0 1 3 8 54 566 3
cert_coverFacet 2 774
cert_cover_2 2 1 0 7 8 262 774 3
cert_coverFacet 3 410
cert_cover_5 3 1 0 2 3 6 146 410 1
cert_coverFacet 4 962
cert_cover_5 4 2 0 5 6 7 386 962 1
cert_coverFacet 5 836
cert_cover_2 5 5 1 7 8 324 836 3
cert_coverFacet 6 312
cert_cover_2 6 3 2 4 7 56 312 3
cert_coverFacet 7 568
cert_cover_2 7 3 2 4 8 56 568 3
cert_coverFacet 8 488
cert_cover_5 8 3 2 4 5 6 104 488 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0292

end
end BundlePart8

section BundlePart9
/- Source: ProjectionCertificates/R_m16e10q1_0293.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0293

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [107, 355, 789, 569, 841, 433, 206, 682, 466, 418, 588, 652, 692, 212, 340, 836, 99, 41, 73, 521, 49, 273, 529, 289, 321, 769, 42, 74, 138, 162, 290, 194, 322, 386, 76, 140, 524, 84, 148, 276, 532, 196, 324, 580, 644, 772, 552, 584, 648, 176, 560, 208, 336, 400, 416, 672, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_107, vertices_355, vertices_789, vertices_569, vertices_841, vertices_433, vertices_206, vertices_682, vertices_466, vertices_418, vertices_588, vertices_652, vertices_692, vertices_212, vertices_340, vertices_836] (by decide +kernel)
  polygons := literalFinset [vertices_99, vertices_41, vertices_73, vertices_521, vertices_49, vertices_273, vertices_529, vertices_289, vertices_321, vertices_769, vertices_42, vertices_74, vertices_138, vertices_162, vertices_290, vertices_194, vertices_322, vertices_386, vertices_76, vertices_140, vertices_524, vertices_84, vertices_148, vertices_276, vertices_532, vertices_196, vertices_324, vertices_580, vertices_644, vertices_772, vertices_552, vertices_584, vertices_648, vertices_176, vertices_560, vertices_208, vertices_336, vertices_400, vertices_416, vertices_672, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_107), (false, vertices_355), (false, vertices_789), (false, vertices_569), (false, vertices_841), (false, vertices_433), (true, vertices_138), (true, vertices_162), (true, vertices_194), (true, vertices_386), (true, vertices_76), (true, vertices_140), (true, vertices_524), (true, vertices_84), (true, vertices_148), (true, vertices_196), (true, vertices_324), (true, vertices_580), (true, vertices_644), (true, vertices_648), (true, vertices_208), (true, vertices_336), (true, vertices_672)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 17 20 22 25 27 28 29 30 31
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_107) then 18 else
  if p.val = (false, vertices_355) then 19 else
  if p.val = (false, vertices_789) then 21 else
  if p.val = (false, vertices_569) then 23 else
  if p.val = (false, vertices_841) then 24 else
  if p.val = (false, vertices_433) then 26 else
  if p.val = (true, vertices_138) then 0 else
  if p.val = (true, vertices_162) then 1 else
  if p.val = (true, vertices_194) then 2 else
  if p.val = (true, vertices_386) then 3 else
  if p.val = (true, vertices_76) then 4 else
  if p.val = (true, vertices_140) then 5 else
  if p.val = (true, vertices_524) then 6 else
  if p.val = (true, vertices_84) then 7 else
  if p.val = (true, vertices_148) then 8 else
  if p.val = (true, vertices_196) then 9 else
  if p.val = (true, vertices_324) then 10 else
  if p.val = (true, vertices_580) then 11 else
  if p.val = (true, vertices_644) then 12 else
  if p.val = (true, vertices_648) then 13 else
  if p.val = (true, vertices_208) then 14 else
  if p.val = (true, vertices_336) then 15 else
  if p.val = (true, vertices_672) then 16 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_138), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_162), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_194), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_386), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_76), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_140), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_524), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_84), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_148), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_196), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_324), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_580), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_644), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_648), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_208), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_336), by decide +kernel⟩
  | 16 => Sum.inr ⟨(true, vertices_672), by decide +kernel⟩
  | 17 => Sum.inl 0
  | 18 => Sum.inr ⟨(false, vertices_107), by decide +kernel⟩
  | 19 => Sum.inr ⟨(false, vertices_355), by decide +kernel⟩
  | 20 => Sum.inl 1
  | 21 => Sum.inr ⟨(false, vertices_789), by decide +kernel⟩
  | 22 => Sum.inl 2
  | 23 => Sum.inr ⟨(false, vertices_569), by decide +kernel⟩
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
cert_row_4 0 0 3 5 6 7 466 194 1
cert_row_4 1 0 1 2 5 6 206 74 1
cert_row_4 2 0 2 4 6 8 682 42 3
cert_row_4 3 1 3 4 6 8 692 148 2
cert_rows
cert_pivot_2 7 5 0 1
cert_heightProof 4
cert_coverFacet 0 206
cert_cover_5 0 1 0 1 2 5 74 206 1
cert_coverFacet 1 682
cert_cover_5 1 2 0 2 4 6 42 682 3
cert_coverFacet 2 466
cert_cover_5 2 0 0 3 5 6 194 466 1
cert_coverFacet 3 418
cert_cover_2 3 4 0 6 7 162 418 3
cert_coverFacet 4 588
cert_cover_2 4 2 1 5 8 76 588 3
cert_coverFacet 5 652
cert_cover_2 5 2 1 6 8 140 652 3
cert_coverFacet 6 692
cert_cover_5 6 3 1 3 4 6 148 692 2
cert_coverFacet 7 212
cert_cover_2 7 3 1 5 6 84 212 3
cert_coverFacet 8 340
cert_cover_2 8 3 1 5 7 84 340 3
cert_coverFacet 9 836
cert_cover_2 9 5 1 7 8 324 836 3
cert_coveringFacets_5
cert_coveringProof
cert_certificate 4 10
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0293

end
end BundlePart9

section BundlePart10
/- Source: ProjectionCertificates/R_m16e10q1_0294.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0294

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [787, 557, 277, 533, 357, 233, 841, 406, 218, 602, 482, 834, 692, 420, 664, 680, 21, 37, 261, 517, 41, 73, 521, 273, 529, 97, 321, 769, 90, 146, 274, 530, 194, 322, 578, 386, 770, 148, 276, 532, 164, 292, 548, 388, 152, 536, 168, 552, 200, 584, 648, 656, 224, 352, 416, 672, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_787, vertices_557, vertices_277, vertices_533, vertices_357, vertices_233, vertices_841, vertices_406, vertices_218, vertices_602, vertices_482, vertices_834, vertices_692, vertices_420, vertices_664, vertices_680] (by decide +kernel)
  polygons := literalFinset [vertices_21, vertices_37, vertices_261, vertices_517, vertices_41, vertices_73, vertices_521, vertices_273, vertices_529, vertices_97, vertices_321, vertices_769, vertices_90, vertices_146, vertices_274, vertices_530, vertices_194, vertices_322, vertices_578, vertices_386, vertices_770, vertices_148, vertices_276, vertices_532, vertices_164, vertices_292, vertices_548, vertices_388, vertices_152, vertices_536, vertices_168, vertices_552, vertices_200, vertices_584, vertices_648, vertices_656, vertices_224, vertices_352, vertices_416, vertices_672, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_787), (false, vertices_557), (false, vertices_277), (false, vertices_533), (false, vertices_357), (false, vertices_233), (false, vertices_841), (true, vertices_90), (true, vertices_146), (true, vertices_194), (true, vertices_322), (true, vertices_578), (true, vertices_386), (true, vertices_148), (true, vertices_164), (true, vertices_388), (true, vertices_152), (true, vertices_536), (true, vertices_648), (true, vertices_656), (true, vertices_416), (true, vertices_672)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 16 19 22 25 26 27 28 29 30
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_787) then 17 else
  if p.val = (false, vertices_557) then 20 else
  if p.val = (false, vertices_277) then 0 else
  if p.val = (false, vertices_533) then 1 else
  if p.val = (false, vertices_357) then 21 else
  if p.val = (false, vertices_233) then 23 else
  if p.val = (false, vertices_841) then 24 else
  if p.val = (true, vertices_90) then 18 else
  if p.val = (true, vertices_146) then 2 else
  if p.val = (true, vertices_194) then 3 else
  if p.val = (true, vertices_322) then 4 else
  if p.val = (true, vertices_578) then 5 else
  if p.val = (true, vertices_386) then 6 else
  if p.val = (true, vertices_148) then 7 else
  if p.val = (true, vertices_164) then 8 else
  if p.val = (true, vertices_388) then 9 else
  if p.val = (true, vertices_152) then 10 else
  if p.val = (true, vertices_536) then 11 else
  if p.val = (true, vertices_648) then 12 else
  if p.val = (true, vertices_656) then 13 else
  if p.val = (true, vertices_416) then 14 else
  if p.val = (true, vertices_672) then 15 else
  0
cert_priority
cert_nodeAtPriority_39 0 277 1 533 146 194 322 578 386 148 164 388 152 536 648 656 416 672 787 90 557 357 233 841
cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 2 3 5 90
cert_row_4 1 0 4 5 6 7 482 194 1
cert_row_4 2 0 1 3 6 7 406 146 1
cert_row_4 3 1 3 4 6 8 692 148 2
cert_rows
cert_pivot_2 2 5 0 1
cert_heightProof 4
cert_coverFacet 0 406
cert_cover_5 0 2 0 1 3 6 146 406 1
cert_coverFacet 1 218
cert_cover_5 1 0 0 2 3 6 90 218 3
cert_coverFacet 2 602
cert_cover_5 2 0 0 2 3 8 90 602 3
cert_coverFacet 3 482
cert_cover_5 3 1 0 4 5 6 194 482 1
cert_coverFacet 4 834
cert_cover_2 4 5 0 7 8 322 834 3
cert_coverFacet 5 692
cert_cover_5 5 3 1 3 4 6 148 692 2
cert_coverFacet 6 420
cert_cover_2 6 4 1 6 7 164 420 3
cert_coverFacet 7 664
cert_cover_2 7 3 2 6 8 152 664 3
cert_coverFacet 8 680
cert_cover_2 8 4 2 6 8 168 680 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0294

end
end BundlePart10

section BundlePart11
/- Source: ProjectionCertificates/R_m16e10q1_0295.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0295

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [179, 403, 803, 453, 841, 737, 62, 346, 554, 778, 92, 556, 716, 692, 340, 404, 147, 35, 259, 161, 545, 193, 321, 577, 385, 769, 26, 42, 266, 522, 50, 274, 546, 770, 28, 44, 76, 524, 52, 84, 148, 276, 548, 196, 324, 388, 644, 88, 552, 328, 584, 776, 176, 336, 400, 672, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_179, vertices_403, vertices_803, vertices_453, vertices_841, vertices_737, vertices_62, vertices_346, vertices_554, vertices_778, vertices_92, vertices_556, vertices_716, vertices_692, vertices_340, vertices_404] (by decide +kernel)
  polygons := literalFinset [vertices_147, vertices_35, vertices_259, vertices_161, vertices_545, vertices_193, vertices_321, vertices_577, vertices_385, vertices_769, vertices_26, vertices_42, vertices_266, vertices_522, vertices_50, vertices_274, vertices_546, vertices_770, vertices_28, vertices_44, vertices_76, vertices_524, vertices_52, vertices_84, vertices_148, vertices_276, vertices_548, vertices_196, vertices_324, vertices_388, vertices_644, vertices_88, vertices_552, vertices_328, vertices_584, vertices_776, vertices_176, vertices_336, vertices_400, vertices_672, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_179), (false, vertices_403), (false, vertices_803), (false, vertices_453), (false, vertices_841), (false, vertices_737), (true, vertices_26), (true, vertices_42), (true, vertices_266), (true, vertices_522), (true, vertices_28), (true, vertices_44), (true, vertices_76), (true, vertices_524), (true, vertices_52), (true, vertices_84), (true, vertices_148), (true, vertices_276), (true, vertices_548), (true, vertices_644), (true, vertices_88), (true, vertices_552), (true, vertices_336)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 17 21 23 25 26 28 29 30 31
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_179) then 18 else
  if p.val = (false, vertices_403) then 19 else
  if p.val = (false, vertices_803) then 20 else
  if p.val = (false, vertices_453) then 22 else
  if p.val = (false, vertices_841) then 24 else
  if p.val = (false, vertices_737) then 27 else
  if p.val = (true, vertices_26) then 0 else
  if p.val = (true, vertices_42) then 1 else
  if p.val = (true, vertices_266) then 2 else
  if p.val = (true, vertices_522) then 3 else
  if p.val = (true, vertices_28) then 4 else
  if p.val = (true, vertices_44) then 5 else
  if p.val = (true, vertices_76) then 6 else
  if p.val = (true, vertices_524) then 7 else
  if p.val = (true, vertices_52) then 8 else
  if p.val = (true, vertices_84) then 9 else
  if p.val = (true, vertices_148) then 10 else
  if p.val = (true, vertices_276) then 11 else
  if p.val = (true, vertices_548) then 12 else
  if p.val = (true, vertices_644) then 13 else
  if p.val = (true, vertices_88) then 14 else
  if p.val = (true, vertices_552) then 15 else
  if p.val = (true, vertices_336) then 16 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_26), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_42), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_266), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_522), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_28), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_44), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_76), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_524), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_52), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_84), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_148), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_276), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_548), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_644), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_88), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_552), by decide +kernel⟩
  | 16 => Sum.inr ⟨(true, vertices_336), by decide +kernel⟩
  | 17 => Sum.inl 0
  | 18 => Sum.inr ⟨(false, vertices_179), by decide +kernel⟩
  | 19 => Sum.inr ⟨(false, vertices_403), by decide +kernel⟩
  | 20 => Sum.inr ⟨(false, vertices_803), by decide +kernel⟩
  | 21 => Sum.inl 1
  | 22 => Sum.inr ⟨(false, vertices_453), by decide +kernel⟩
  | 23 => Sum.inl 2
  | 24 => Sum.inr ⟨(false, vertices_841), by decide +kernel⟩
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
cert_row_4 0 0 2 3 5 7 346 26 3
cert_row_4 1 0 1 2 3 4 62 26 1
cert_row_4 2 1 2 5 6 8 716 76 3
cert_row_4 3 1 3 4 6 8 692 52 3
cert_rows
cert_pivot_2 7 0 2 1
cert_heightProof 4
cert_coverFacet 0 62
cert_cover_5 0 1 0 1 2 3 26 62 1
cert_coverFacet 1 346
cert_cover_5 1 0 0 2 3 5 26 346 3
cert_coverFacet 2 554
cert_cover_2 2 2 0 4 8 42 554 3
cert_coverFacet 3 778
cert_cover_2 3 2 0 7 8 266 778 3
cert_coverFacet 4 92
cert_cover_2 4 2 1 3 5 28 92 3
cert_coverFacet 5 556
cert_cover_2 5 2 1 4 8 44 556 3
cert_coverFacet 6 716
cert_cover_5 6 2 1 2 5 6 76 716 3
cert_coverFacet 7 692
cert_cover_5 7 3 1 3 4 6 52 692 3
cert_coverFacet 8 340
cert_cover_2 8 3 1 5 7 84 340 3
cert_coverFacet 9 404
cert_cover_2 9 3 1 6 7 148 404 3
cert_coveringFacets_5
cert_coveringProof
cert_certificate 4 10
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0295

end
end BundlePart11

section BundlePart12
/- Source: ProjectionCertificates/R_m16e10q1_0296.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0296

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [803, 93, 789, 613, 345, 481, 662, 314, 154, 170, 786, 738, 156, 716, 424, 456, 21, 69, 517, 89, 273, 97, 289, 545, 321, 769, 26, 42, 138, 146, 274, 530, 162, 290, 546, 642, 770, 28, 76, 140, 148, 532, 580, 644, 152, 280, 168, 296, 200, 328, 392, 784, 224, 608, 416, 448, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_803, vertices_93, vertices_789, vertices_613, vertices_345, vertices_481, vertices_662, vertices_314, vertices_154, vertices_170, vertices_786, vertices_738, vertices_156, vertices_716, vertices_424, vertices_456] (by decide +kernel)
  polygons := literalFinset [vertices_21, vertices_69, vertices_517, vertices_89, vertices_273, vertices_97, vertices_289, vertices_545, vertices_321, vertices_769, vertices_26, vertices_42, vertices_138, vertices_146, vertices_274, vertices_530, vertices_162, vertices_290, vertices_546, vertices_642, vertices_770, vertices_28, vertices_76, vertices_140, vertices_148, vertices_532, vertices_580, vertices_644, vertices_152, vertices_280, vertices_168, vertices_296, vertices_200, vertices_328, vertices_392, vertices_784, vertices_224, vertices_608, vertices_416, vertices_448, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_803), (false, vertices_93), (false, vertices_789), (false, vertices_613), (false, vertices_345), (false, vertices_481), (true, vertices_26), (true, vertices_42), (true, vertices_138), (true, vertices_146), (true, vertices_274), (true, vertices_530), (true, vertices_162), (true, vertices_642), (true, vertices_140), (true, vertices_148), (true, vertices_644), (true, vertices_152), (true, vertices_168), (true, vertices_296), (true, vertices_200), (true, vertices_392), (true, vertices_704)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 17 19 22 25 26 28 29 30 31
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_803) then 18 else
  if p.val = (false, vertices_93) then 23 else
  if p.val = (false, vertices_789) then 20 else
  if p.val = (false, vertices_613) then 21 else
  if p.val = (false, vertices_345) then 24 else
  if p.val = (false, vertices_481) then 27 else
  if p.val = (true, vertices_26) then 0 else
  if p.val = (true, vertices_42) then 1 else
  if p.val = (true, vertices_138) then 2 else
  if p.val = (true, vertices_146) then 3 else
  if p.val = (true, vertices_274) then 4 else
  if p.val = (true, vertices_530) then 5 else
  if p.val = (true, vertices_162) then 6 else
  if p.val = (true, vertices_642) then 7 else
  if p.val = (true, vertices_140) then 8 else
  if p.val = (true, vertices_148) then 9 else
  if p.val = (true, vertices_644) then 10 else
  if p.val = (true, vertices_152) then 11 else
  if p.val = (true, vertices_168) then 12 else
  if p.val = (true, vertices_296) then 13 else
  if p.val = (true, vertices_200) then 14 else
  if p.val = (true, vertices_392) then 15 else
  if p.val = (true, vertices_704) then 16 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_26), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_42), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_138), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_146), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_274), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_530), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_162), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_642), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_140), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_148), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_644), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_152), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_168), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_296), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_200), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_392), by decide +kernel⟩
  | 16 => Sum.inr ⟨(true, vertices_704), by decide +kernel⟩
  | 17 => Sum.inl 0
  | 18 => Sum.inr ⟨(false, vertices_803), by decide +kernel⟩
  | 19 => Sum.inl 1
  | 20 => Sum.inr ⟨(false, vertices_789), by decide +kernel⟩
  | 21 => Sum.inr ⟨(false, vertices_613), by decide +kernel⟩
  | 22 => Sum.inl 2
  | 23 => Sum.inr ⟨(false, vertices_93), by decide +kernel⟩
  | 24 => Sum.inr ⟨(false, vertices_345), by decide +kernel⟩
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
cert_row_4 0 0 2 3 4 7 314 26 3
cert_row_4 1 0 1 3 6 8 662 146 1
cert_row_4 2 0 4 5 6 8 738 162 2
cert_row_4 3 1 2 5 6 8 716 76 3
cert_rows
cert_pivot_2 7 3 0 1
cert_heightProof 4
cert_coverFacet 0 662
cert_cover_5 0 1 0 1 3 6 146 662 1
cert_coverFacet 1 314
cert_cover_5 1 0 0 2 3 4 26 314 3
cert_coverFacet 2 154
cert_cover_2 2 2 0 3 6 26 154 3
cert_coverFacet 3 170
cert_cover_2 3 2 0 4 6 42 170 3
cert_coverFacet 4 786
cert_cover_2 4 3 0 7 8 274 786 3
cert_coverFacet 5 738
cert_cover_5 5 2 0 4 5 6 162 738 2
cert_coverFacet 6 156
cert_cover_2 6 2 1 3 6 28 156 3
cert_coverFacet 7 716
cert_cover_5 7 3 1 2 5 6 76 716 3
cert_coverFacet 8 424
cert_cover_2 8 4 2 6 7 168 424 3
cert_coverFacet 9 456
cert_cover_2 9 5 2 6 7 200 456 3
cert_coveringFacets_5
cert_coveringProof
cert_certificate 4 10
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0296

end
end BundlePart12

section BundlePart13
/- Source: ProjectionCertificates/R_m16e10q1_0297.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0297

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [899, 93, 653, 117, 165, 793, 433, 454, 714, 818, 354, 610, 204, 356, 420, 632, 13, 85, 37, 133, 25, 521, 49, 273, 161, 385, 641, 769, 98, 290, 546, 194, 322, 578, 386, 642, 770, 76, 140, 100, 164, 292, 196, 324, 388, 88, 536, 200, 584, 648, 112, 304, 560, 784, 352, 608, 416]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_899, vertices_93, vertices_653, vertices_117, vertices_165, vertices_793, vertices_433, vertices_454, vertices_714, vertices_818, vertices_354, vertices_610, vertices_204, vertices_356, vertices_420, vertices_632] (by decide +kernel)
  polygons := literalFinset [vertices_13, vertices_85, vertices_37, vertices_133, vertices_25, vertices_521, vertices_49, vertices_273, vertices_161, vertices_385, vertices_641, vertices_769, vertices_98, vertices_290, vertices_546, vertices_194, vertices_322, vertices_578, vertices_386, vertices_642, vertices_770, vertices_76, vertices_140, vertices_100, vertices_164, vertices_292, vertices_196, vertices_324, vertices_388, vertices_88, vertices_536, vertices_200, vertices_584, vertices_648, vertices_112, vertices_304, vertices_560, vertices_784, vertices_352, vertices_608, vertices_416] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_899), (false, vertices_93), (false, vertices_653), (false, vertices_117), (false, vertices_165), (false, vertices_793), (false, vertices_433), (true, vertices_98), (true, vertices_290), (true, vertices_546), (true, vertices_194), (true, vertices_322), (true, vertices_578), (true, vertices_292), (true, vertices_196), (true, vertices_324), (true, vertices_388), (true, vertices_200), (true, vertices_584), (true, vertices_560), (true, vertices_352), (true, vertices_608)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 16 18 22 24 26 27 28 29 30
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_899) then 17 else
  if p.val = (false, vertices_93) then 19 else
  if p.val = (false, vertices_653) then 20 else
  if p.val = (false, vertices_117) then 21 else
  if p.val = (false, vertices_165) then 0 else
  if p.val = (false, vertices_793) then 23 else
  if p.val = (false, vertices_433) then 25 else
  if p.val = (true, vertices_98) then 1 else
  if p.val = (true, vertices_290) then 2 else
  if p.val = (true, vertices_546) then 3 else
  if p.val = (true, vertices_194) then 4 else
  if p.val = (true, vertices_322) then 5 else
  if p.val = (true, vertices_578) then 6 else
  if p.val = (true, vertices_292) then 7 else
  if p.val = (true, vertices_196) then 8 else
  if p.val = (true, vertices_324) then 9 else
  if p.val = (true, vertices_388) then 10 else
  if p.val = (true, vertices_200) then 11 else
  if p.val = (true, vertices_584) then 12 else
  if p.val = (true, vertices_560) then 13 else
  if p.val = (true, vertices_352) then 14 else
  if p.val = (true, vertices_608) then 15 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_165), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_98), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_290), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_546), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_194), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_322), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_578), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_292), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_196), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_324), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_388), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_200), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_584), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_560), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_352), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_608), by decide +kernel⟩
  | 16 => Sum.inl 0
  | 17 => Sum.inr ⟨(false, vertices_899), by decide +kernel⟩
  | 18 => Sum.inl 1
  | 19 => Sum.inr ⟨(false, vertices_93), by decide +kernel⟩
  | 20 => Sum.inr ⟨(false, vertices_653), by decide +kernel⟩
  | 21 => Sum.inr ⟨(false, vertices_117), by decide +kernel⟩
  | 22 => Sum.inl 2
  | 23 => Sum.inr ⟨(false, vertices_793), by decide +kernel⟩
  | 24 => Sum.inl 3
  | 25 => Sum.inr ⟨(false, vertices_433), by decide +kernel⟩
  | 26 => Sum.inl 4
  | 27 => Sum.inl 5
  | 28 => Sum.inl 6
  | 29 => Sum.inl 7
  | 30 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 5 6 7 454 194 1
cert_row_4 1 0 2 5 6 8 714 194 1
cert_row_4 2 0 3 4 7 8 818 290 1
cert_row_4 3 2 3 4 5 8 632 88 2
cert_rows
cert_pivot_2 1 6 0 2
cert_heightProof 4
cert_coverFacet 0 454
cert_cover_5 0 0 0 1 5 6 194 454 1
cert_coverFacet 1 714
cert_cover_5 1 1 0 2 5 6 194 714 1
cert_coverFacet 2 818
cert_cover_5 2 2 0 3 4 7 290 818 1
cert_coverFacet 3 354
cert_cover_2 3 4 0 5 7 98 354 3
cert_coverFacet 4 610
cert_cover_2 4 4 0 5 8 98 610 3
cert_coverFacet 5 204
cert_cover_2 5 2 1 5 6 76 204 3
cert_coverFacet 6 356
cert_cover_2 6 4 1 5 7 100 356 3
cert_coverFacet 7 420
cert_cover_2 7 4 1 6 7 164 420 3
cert_coverFacet 8 632
cert_cover_5 8 3 2 3 4 5 88 632 2
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0297

end
end BundlePart13

section BundlePart14
/- Source: ProjectionCertificates/R_m16e10q1_0298.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0298

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [283, 563, 835, 613, 57, 233, 329, 406, 662, 774, 684, 484, 836, 568, 472, 664, 19, 259, 515, 25, 41, 73, 265, 49, 97, 545, 321, 577, 150, 262, 518, 274, 530, 770, 100, 164, 548, 324, 580, 388, 644, 772, 56, 152, 280, 536, 168, 552, 200, 328, 648, 560, 400, 656, 224, 448, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_283, vertices_563, vertices_835, vertices_613, vertices_57, vertices_233, vertices_329, vertices_406, vertices_662, vertices_774, vertices_684, vertices_484, vertices_836, vertices_568, vertices_472, vertices_664] (by decide +kernel)
  polygons := literalFinset [vertices_19, vertices_259, vertices_515, vertices_25, vertices_41, vertices_73, vertices_265, vertices_49, vertices_97, vertices_545, vertices_321, vertices_577, vertices_150, vertices_262, vertices_518, vertices_274, vertices_530, vertices_770, vertices_100, vertices_164, vertices_548, vertices_324, vertices_580, vertices_388, vertices_644, vertices_772, vertices_56, vertices_152, vertices_280, vertices_536, vertices_168, vertices_552, vertices_200, vertices_328, vertices_648, vertices_560, vertices_400, vertices_656, vertices_224, vertices_448, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_283), (false, vertices_563), (false, vertices_835), (false, vertices_613), (false, vertices_57), (false, vertices_233), (false, vertices_329), (true, vertices_150), (true, vertices_262), (true, vertices_518), (true, vertices_164), (true, vertices_324), (true, vertices_388), (true, vertices_644), (true, vertices_772), (true, vertices_152), (true, vertices_536), (true, vertices_552), (true, vertices_648), (true, vertices_400), (true, vertices_656), (true, vertices_448)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 19 16 23 25 26 27 28 29 30
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_283) then 20 else
  if p.val = (false, vertices_563) then 21 else
  if p.val = (false, vertices_835) then 22 else
  if p.val = (false, vertices_613) then 17 else
  if p.val = (false, vertices_57) then 0 else
  if p.val = (false, vertices_233) then 24 else
  if p.val = (false, vertices_329) then 1 else
  if p.val = (true, vertices_150) then 18 else
  if p.val = (true, vertices_262) then 2 else
  if p.val = (true, vertices_518) then 3 else
  if p.val = (true, vertices_164) then 4 else
  if p.val = (true, vertices_324) then 5 else
  if p.val = (true, vertices_388) then 6 else
  if p.val = (true, vertices_644) then 7 else
  if p.val = (true, vertices_772) then 8 else
  if p.val = (true, vertices_152) then 9 else
  if p.val = (true, vertices_536) then 10 else
  if p.val = (true, vertices_552) then 11 else
  if p.val = (true, vertices_648) then 12 else
  if p.val = (true, vertices_400) then 13 else
  if p.val = (true, vertices_656) then 14 else
  if p.val = (true, vertices_448) then 15 else
  0
cert_priority
cert_nodeAtPriority_5 1 57 0 329 262 518 164 324 388 644 772 152 536 552 648 400 656 448 613 150 283 563 835 233
cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 1 3 6 150
cert_row_4 1 1 2 4 6 8 684 164 1
cert_row_4 2 1 4 5 6 7 484 100 3
cert_row_4 3 2 3 5 6 7 472 152 2
cert_rows
cert_pivot_2 0 8 1 2
cert_heightProof 4
cert_coverFacet 0 406
cert_cover_5 0 0 0 1 3 7 150 406 3
cert_coverFacet 1 662
cert_cover_5 1 0 0 1 3 8 150 662 3
cert_coverFacet 2 774
cert_cover_2 2 1 0 7 8 262 774 3
cert_coverFacet 3 684
cert_cover_5 3 1 1 2 4 6 164 684 1
cert_coverFacet 4 484
cert_cover_5 4 2 1 4 5 6 100 484 3
cert_coverFacet 5 836
cert_cover_2 5 5 1 7 8 324 836 3
cert_coverFacet 6 568
cert_cover_2 6 3 2 4 8 56 568 3
cert_coverFacet 7 472
cert_cover_5 7 3 2 3 5 6 152 472 2
cert_coverFacet 8 664
cert_cover_2 8 3 2 6 8 152 664 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0298

end
end BundlePart14

section BundlePart15
/- Source: ProjectionCertificates/R_m16e10q1_0299.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0299

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [803, 93, 789, 613, 345, 481, 158, 314, 170, 658, 786, 738, 716, 660, 424, 456, 21, 69, 517, 89, 273, 97, 289, 545, 321, 769, 26, 42, 138, 146, 274, 530, 162, 290, 546, 642, 770, 28, 76, 140, 148, 532, 580, 644, 280, 168, 296, 200, 328, 392, 656, 784, 224, 608, 416, 448, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_803, vertices_93, vertices_789, vertices_613, vertices_345, vertices_481, vertices_158, vertices_314, vertices_170, vertices_658, vertices_786, vertices_738, vertices_716, vertices_660, vertices_424, vertices_456] (by decide +kernel)
  polygons := literalFinset [vertices_21, vertices_69, vertices_517, vertices_89, vertices_273, vertices_97, vertices_289, vertices_545, vertices_321, vertices_769, vertices_26, vertices_42, vertices_138, vertices_146, vertices_274, vertices_530, vertices_162, vertices_290, vertices_546, vertices_642, vertices_770, vertices_28, vertices_76, vertices_140, vertices_148, vertices_532, vertices_580, vertices_644, vertices_280, vertices_168, vertices_296, vertices_200, vertices_328, vertices_392, vertices_656, vertices_784, vertices_224, vertices_608, vertices_416, vertices_448, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_803), (false, vertices_93), (false, vertices_789), (false, vertices_613), (false, vertices_345), (false, vertices_481), (true, vertices_26), (true, vertices_42), (true, vertices_138), (true, vertices_146), (true, vertices_274), (true, vertices_530), (true, vertices_162), (true, vertices_642), (true, vertices_140), (true, vertices_148), (true, vertices_644), (true, vertices_168), (true, vertices_296), (true, vertices_200), (true, vertices_392), (true, vertices_656), (true, vertices_704)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 17 19 22 25 26 28 29 30 31
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_803) then 18 else
  if p.val = (false, vertices_93) then 23 else
  if p.val = (false, vertices_789) then 20 else
  if p.val = (false, vertices_613) then 21 else
  if p.val = (false, vertices_345) then 24 else
  if p.val = (false, vertices_481) then 27 else
  if p.val = (true, vertices_26) then 0 else
  if p.val = (true, vertices_42) then 1 else
  if p.val = (true, vertices_138) then 2 else
  if p.val = (true, vertices_146) then 3 else
  if p.val = (true, vertices_274) then 4 else
  if p.val = (true, vertices_530) then 5 else
  if p.val = (true, vertices_162) then 6 else
  if p.val = (true, vertices_642) then 7 else
  if p.val = (true, vertices_140) then 8 else
  if p.val = (true, vertices_148) then 9 else
  if p.val = (true, vertices_644) then 10 else
  if p.val = (true, vertices_168) then 11 else
  if p.val = (true, vertices_296) then 12 else
  if p.val = (true, vertices_200) then 13 else
  if p.val = (true, vertices_392) then 14 else
  if p.val = (true, vertices_656) then 15 else
  if p.val = (true, vertices_704) then 16 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_26), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_42), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_138), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_146), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_274), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_530), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_162), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_642), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_140), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_148), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_644), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_168), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_296), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_200), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_392), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_656), by decide +kernel⟩
  | 16 => Sum.inr ⟨(true, vertices_704), by decide +kernel⟩
  | 17 => Sum.inl 0
  | 18 => Sum.inr ⟨(false, vertices_803), by decide +kernel⟩
  | 19 => Sum.inl 1
  | 20 => Sum.inr ⟨(false, vertices_789), by decide +kernel⟩
  | 21 => Sum.inr ⟨(false, vertices_613), by decide +kernel⟩
  | 22 => Sum.inl 2
  | 23 => Sum.inr ⟨(false, vertices_93), by decide +kernel⟩
  | 24 => Sum.inr ⟨(false, vertices_345), by decide +kernel⟩
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
cert_row_4 0 0 2 3 4 7 314 26 3
cert_row_4 1 0 1 2 3 6 158 26 1
cert_row_4 2 0 4 5 6 8 738 162 2
cert_row_4 3 1 2 5 6 8 716 76 3
cert_rows
cert_pivot_2 7 3 0 1
cert_heightProof 4
cert_coverFacet 0 158
cert_cover_5 0 1 0 1 2 3 26 158 1
cert_coverFacet 1 314
cert_cover_5 1 0 0 2 3 4 26 314 3
cert_coverFacet 2 170
cert_cover_2 2 2 0 4 6 42 170 3
cert_coverFacet 3 658
cert_cover_2 3 3 0 6 8 146 658 3
cert_coverFacet 4 786
cert_cover_2 4 3 0 7 8 274 786 3
cert_coverFacet 5 738
cert_cover_5 5 2 0 4 5 6 162 738 2
cert_coverFacet 6 716
cert_cover_5 6 3 1 2 5 6 76 716 3
cert_coverFacet 7 660
cert_cover_2 7 3 1 6 8 148 660 3
cert_coverFacet 8 424
cert_cover_2 8 4 2 6 7 168 424 3
cert_coverFacet 9 456
cert_cover_2 9 5 2 6 7 200 456 3
cert_coveringFacets_5
cert_coveringProof
cert_certificate 4 10
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0299

end
end BundlePart15

section BundlePart16
/- Source: ProjectionCertificates/R_m16e10q1_0300.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0300

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [167, 391, 803, 841, 465, 737, 46, 334, 570, 778, 60, 92, 692, 340, 404, 728, 135, 35, 259, 161, 545, 193, 321, 577, 385, 769, 14, 38, 262, 42, 266, 522, 546, 770, 28, 44, 76, 52, 84, 148, 276, 164, 324, 388, 56, 88, 536, 328, 584, 776, 560, 208, 336, 400, 656, 672, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_167, vertices_391, vertices_803, vertices_841, vertices_465, vertices_737, vertices_46, vertices_334, vertices_570, vertices_778, vertices_60, vertices_92, vertices_692, vertices_340, vertices_404, vertices_728] (by decide +kernel)
  polygons := literalFinset [vertices_135, vertices_35, vertices_259, vertices_161, vertices_545, vertices_193, vertices_321, vertices_577, vertices_385, vertices_769, vertices_14, vertices_38, vertices_262, vertices_42, vertices_266, vertices_522, vertices_546, vertices_770, vertices_28, vertices_44, vertices_76, vertices_52, vertices_84, vertices_148, vertices_276, vertices_164, vertices_324, vertices_388, vertices_56, vertices_88, vertices_536, vertices_328, vertices_584, vertices_776, vertices_560, vertices_208, vertices_336, vertices_400, vertices_656, vertices_672, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_167), (false, vertices_391), (false, vertices_803), (false, vertices_841), (false, vertices_465), (false, vertices_737), (true, vertices_14), (true, vertices_42), (true, vertices_266), (true, vertices_522), (true, vertices_28), (true, vertices_44), (true, vertices_76), (true, vertices_52), (true, vertices_84), (true, vertices_148), (true, vertices_276), (true, vertices_324), (true, vertices_56), (true, vertices_88), (true, vertices_536), (true, vertices_560), (true, vertices_656)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 17 21 22 24 26 28 29 30 31
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_167) then 18 else
  if p.val = (false, vertices_391) then 19 else
  if p.val = (false, vertices_803) then 20 else
  if p.val = (false, vertices_841) then 23 else
  if p.val = (false, vertices_465) then 25 else
  if p.val = (false, vertices_737) then 27 else
  if p.val = (true, vertices_14) then 0 else
  if p.val = (true, vertices_42) then 1 else
  if p.val = (true, vertices_266) then 2 else
  if p.val = (true, vertices_522) then 3 else
  if p.val = (true, vertices_28) then 4 else
  if p.val = (true, vertices_44) then 5 else
  if p.val = (true, vertices_76) then 6 else
  if p.val = (true, vertices_52) then 7 else
  if p.val = (true, vertices_84) then 8 else
  if p.val = (true, vertices_148) then 9 else
  if p.val = (true, vertices_276) then 10 else
  if p.val = (true, vertices_324) then 11 else
  if p.val = (true, vertices_56) then 12 else
  if p.val = (true, vertices_88) then 13 else
  if p.val = (true, vertices_536) then 14 else
  if p.val = (true, vertices_560) then 15 else
  if p.val = (true, vertices_656) then 16 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_14), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_42), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_266), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_522), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_28), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_44), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_76), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_52), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_84), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_148), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_276), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_324), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_56), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_88), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_536), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_560), by decide +kernel⟩
  | 16 => Sum.inr ⟨(true, vertices_656), by decide +kernel⟩
  | 17 => Sum.inl 0
  | 18 => Sum.inr ⟨(false, vertices_167), by decide +kernel⟩
  | 19 => Sum.inr ⟨(false, vertices_391), by decide +kernel⟩
  | 20 => Sum.inr ⟨(false, vertices_803), by decide +kernel⟩
  | 21 => Sum.inl 1
  | 22 => Sum.inl 2
  | 23 => Sum.inr ⟨(false, vertices_841), by decide +kernel⟩
  | 24 => Sum.inl 3
  | 25 => Sum.inr ⟨(false, vertices_465), by decide +kernel⟩
  | 26 => Sum.inl 4
  | 27 => Sum.inr ⟨(false, vertices_737), by decide +kernel⟩
  | 28 => Sum.inl 5
  | 29 => Sum.inl 6
  | 30 => Sum.inl 7
  | 31 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 2 5 7 334 14 3
cert_row_4 1 0 2 3 4 8 570 42 2
cert_row_4 2 1 3 4 6 8 692 52 3
cert_row_4 3 2 3 5 6 8 728 88 3
cert_rows
cert_pivot_2 7 0 1 2
cert_heightProof 4
cert_coverFacet 0 46
cert_cover_2 0 1 0 2 4 14 46 3
cert_coverFacet 1 334
cert_cover_5 1 0 0 1 2 5 14 334 3
cert_coverFacet 2 570
cert_cover_5 2 1 0 2 3 4 42 570 2
cert_coverFacet 3 778
cert_cover_2 3 2 0 7 8 266 778 3
cert_coverFacet 4 60
cert_cover_2 4 2 1 3 4 28 60 3
cert_coverFacet 5 92
cert_cover_2 5 2 1 3 5 28 92 3
cert_coverFacet 6 692
cert_cover_5 6 2 1 3 4 6 52 692 3
cert_coverFacet 7 340
cert_cover_2 7 3 1 5 7 84 340 3
cert_coverFacet 8 404
cert_cover_2 8 3 1 6 7 148 404 3
cert_coverFacet 9 728
cert_cover_5 9 3 2 3 5 6 88 728 3
cert_coveringFacets_5
cert_coveringProof
cert_certificate 4 10
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0300

end
end BundlePart16

section BundlePart17
/- Source: ProjectionCertificates/R_m16e10q1_0301.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0301

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [151, 279, 651, 803, 421, 737, 346, 154, 778, 364, 724, 340, 228, 632, 664, 808, 23, 131, 259, 515, 133, 261, 161, 289, 545, 641, 26, 138, 266, 522, 146, 274, 770, 84, 148, 276, 100, 164, 292, 196, 324, 88, 152, 536, 104, 296, 552, 328, 648, 776, 336, 592, 656, 224, 608, 800, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_151, vertices_279, vertices_651, vertices_803, vertices_421, vertices_737, vertices_346, vertices_154, vertices_778, vertices_364, vertices_724, vertices_340, vertices_228, vertices_632, vertices_664, vertices_808] (by decide +kernel)
  polygons := literalFinset [vertices_23, vertices_131, vertices_259, vertices_515, vertices_133, vertices_261, vertices_161, vertices_289, vertices_545, vertices_641, vertices_26, vertices_138, vertices_266, vertices_522, vertices_146, vertices_274, vertices_770, vertices_84, vertices_148, vertices_276, vertices_100, vertices_164, vertices_292, vertices_196, vertices_324, vertices_88, vertices_152, vertices_536, vertices_104, vertices_296, vertices_552, vertices_328, vertices_648, vertices_776, vertices_336, vertices_592, vertices_656, vertices_224, vertices_608, vertices_800, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_151), (false, vertices_279), (false, vertices_651), (false, vertices_803), (false, vertices_421), (false, vertices_737), (true, vertices_26), (true, vertices_266), (true, vertices_84), (true, vertices_100), (true, vertices_196), (true, vertices_324), (true, vertices_88), (true, vertices_152), (true, vertices_536), (true, vertices_104), (true, vertices_296), (true, vertices_552), (true, vertices_328), (true, vertices_776), (true, vertices_336), (true, vertices_592), (true, vertices_656)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 21 17 24 25 26 28 29 30 31
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_151) then 18 else
  if p.val = (false, vertices_279) then 19 else
  if p.val = (false, vertices_651) then 22 else
  if p.val = (false, vertices_803) then 23 else
  if p.val = (false, vertices_421) then 20 else
  if p.val = (false, vertices_737) then 27 else
  if p.val = (true, vertices_26) then 0 else
  if p.val = (true, vertices_266) then 1 else
  if p.val = (true, vertices_84) then 2 else
  if p.val = (true, vertices_100) then 3 else
  if p.val = (true, vertices_196) then 4 else
  if p.val = (true, vertices_324) then 5 else
  if p.val = (true, vertices_88) then 6 else
  if p.val = (true, vertices_152) then 7 else
  if p.val = (true, vertices_536) then 8 else
  if p.val = (true, vertices_104) then 9 else
  if p.val = (true, vertices_296) then 10 else
  if p.val = (true, vertices_552) then 11 else
  if p.val = (true, vertices_328) then 12 else
  if p.val = (true, vertices_776) then 13 else
  if p.val = (true, vertices_336) then 14 else
  if p.val = (true, vertices_592) then 15 else
  if p.val = (true, vertices_656) then 16 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_26), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_266), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_84), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_100), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_196), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_324), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_88), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_152), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_536), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_104), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_296), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_552), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_328), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_776), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_336), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_592), by decide +kernel⟩
  | 16 => Sum.inr ⟨(true, vertices_656), by decide +kernel⟩
  | 17 => Sum.inl 1
  | 18 => Sum.inr ⟨(false, vertices_151), by decide +kernel⟩
  | 19 => Sum.inr ⟨(false, vertices_279), by decide +kernel⟩
  | 20 => Sum.inr ⟨(false, vertices_421), by decide +kernel⟩
  | 21 => Sum.inl 0
  | 22 => Sum.inr ⟨(false, vertices_651), by decide +kernel⟩
  | 23 => Sum.inr ⟨(false, vertices_803), by decide +kernel⟩
  | 24 => Sum.inl 2
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
cert_row_4 0 0 2 3 5 7 346 26 3
cert_row_4 1 1 2 4 5 7 364 100 1
cert_row_4 2 1 3 5 6 8 724 84 3
cert_row_4 3 2 3 4 5 8 632 88 2
cert_rows
cert_pivot_2 0 7 1 2
cert_heightProof 4
cert_coverFacet 0 346
cert_cover_5 0 0 0 2 3 5 26 346 3
cert_coverFacet 1 154
cert_cover_2 1 2 0 3 6 26 154 3
cert_coverFacet 2 778
cert_cover_2 2 2 0 7 8 266 778 3
cert_coverFacet 3 364
cert_cover_5 3 1 1 2 4 5 100 364 1
cert_coverFacet 4 724
cert_cover_5 4 2 1 3 5 6 84 724 3
cert_coverFacet 5 340
cert_cover_2 5 3 1 5 7 84 340 3
cert_coverFacet 6 228
cert_cover_2 6 4 1 5 6 100 228 3
cert_coverFacet 7 632
cert_cover_5 7 3 2 3 4 5 88 632 2
cert_coverFacet 8 664
cert_cover_2 8 3 2 6 8 152 664 3
cert_coverFacet 9 808
cert_cover_2 9 4 2 7 8 296 808 3
cert_coveringFacets_5
cert_coveringProof
cert_certificate 4 10
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0301

end
end BundlePart17

section BundlePart18
/- Source: ProjectionCertificates/R_m16e10q1_0302.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0302

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [43, 331, 675, 771, 837, 185, 713, 62, 286, 806, 564, 468, 596, 408, 456, 752, 11, 35, 259, 515, 41, 73, 137, 161, 321, 577, 641, 769, 30, 38, 262, 42, 266, 546, 770, 52, 84, 276, 532, 548, 324, 580, 772, 56, 152, 280, 200, 328, 392, 176, 560, 208, 592, 400, 672, 448, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_43, vertices_331, vertices_675, vertices_771, vertices_837, vertices_185, vertices_713, vertices_62, vertices_286, vertices_806, vertices_564, vertices_468, vertices_596, vertices_408, vertices_456, vertices_752] (by decide +kernel)
  polygons := literalFinset [vertices_11, vertices_35, vertices_259, vertices_515, vertices_41, vertices_73, vertices_137, vertices_161, vertices_321, vertices_577, vertices_641, vertices_769, vertices_30, vertices_38, vertices_262, vertices_42, vertices_266, vertices_546, vertices_770, vertices_52, vertices_84, vertices_276, vertices_532, vertices_548, vertices_324, vertices_580, vertices_772, vertices_56, vertices_152, vertices_280, vertices_200, vertices_328, vertices_392, vertices_176, vertices_560, vertices_208, vertices_592, vertices_400, vertices_672, vertices_448, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_43), (false, vertices_331), (false, vertices_675), (false, vertices_771), (false, vertices_837), (false, vertices_185), (false, vertices_713), (true, vertices_30), (true, vertices_38), (true, vertices_262), (true, vertices_52), (true, vertices_84), (true, vertices_276), (true, vertices_532), (true, vertices_548), (true, vertices_280), (true, vertices_392), (true, vertices_560), (true, vertices_208), (true, vertices_592), (true, vertices_400), (true, vertices_448)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 16 20 22 25 26 27 28 29 30
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_43) then 0 else
  if p.val = (false, vertices_331) then 17 else
  if p.val = (false, vertices_675) then 18 else
  if p.val = (false, vertices_771) then 1 else
  if p.val = (false, vertices_837) then 21 else
  if p.val = (false, vertices_185) then 23 else
  if p.val = (false, vertices_713) then 24 else
  if p.val = (true, vertices_30) then 19 else
  if p.val = (true, vertices_38) then 2 else
  if p.val = (true, vertices_262) then 3 else
  if p.val = (true, vertices_52) then 4 else
  if p.val = (true, vertices_84) then 5 else
  if p.val = (true, vertices_276) then 6 else
  if p.val = (true, vertices_532) then 7 else
  if p.val = (true, vertices_548) then 8 else
  if p.val = (true, vertices_280) then 9 else
  if p.val = (true, vertices_392) then 10 else
  if p.val = (true, vertices_560) then 11 else
  if p.val = (true, vertices_208) then 12 else
  if p.val = (true, vertices_592) then 13 else
  if p.val = (true, vertices_400) then 14 else
  if p.val = (true, vertices_448) then 15 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_43), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_771), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_38), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_262), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_52), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_84), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_276), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_532), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_548), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_280), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_392), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_560), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_208), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_592), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_400), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_448), by decide +kernel⟩
  | 16 => Sum.inl 0
  | 17 => Sum.inr ⟨(false, vertices_331), by decide +kernel⟩
  | 18 => Sum.inr ⟨(false, vertices_675), by decide +kernel⟩
  | 19 => Sum.inr ⟨(true, vertices_30), by decide +kernel⟩
  | 20 => Sum.inl 1
  | 21 => Sum.inr ⟨(false, vertices_837), by decide +kernel⟩
  | 22 => Sum.inl 2
  | 23 => Sum.inr ⟨(false, vertices_185), by decide +kernel⟩
  | 24 => Sum.inr ⟨(false, vertices_713), by decide +kernel⟩
  | 25 => Sum.inl 3
  | 26 => Sum.inl 4
  | 27 => Sum.inl 5
  | 28 => Sum.inl 6
  | 29 => Sum.inl 7
  | 30 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 1 2 3 30
cert_row_4 1 0 1 4 7 8 806 38 3
cert_row_4 2 1 3 5 6 7 468 84 3
cert_row_4 3 3 4 5 6 8 752 176 2
cert_rows
cert_pivot_2 2 0 1 3
cert_heightProof 4
cert_coverFacet 0 62
cert_cover_5 0 0 0 1 2 4 30 62 3
cert_coverFacet 1 286
cert_cover_5 1 0 0 1 2 7 30 286 3
cert_coverFacet 2 806
cert_cover_5 2 1 0 1 4 7 38 806 3
cert_coverFacet 3 564
cert_cover_2 3 3 1 4 8 52 564 3
cert_coverFacet 4 468
cert_cover_5 4 2 1 3 5 6 84 468 3
cert_coverFacet 5 596
cert_cover_2 5 3 1 5 8 84 596 3
cert_coverFacet 6 408
cert_cover_2 6 3 2 6 7 152 408 3
cert_coverFacet 7 456
cert_cover_2 7 5 2 6 7 200 456 3
cert_coverFacet 8 752
cert_cover_5 8 3 3 4 5 6 176 752 2
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0302

end
end BundlePart18

section BundlePart19
/- Source: ProjectionCertificates/R_m16e10q1_0303.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0303

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [43, 331, 675, 771, 837, 233, 721, 62, 286, 806, 564, 468, 596, 696, 408, 456, 11, 35, 259, 515, 41, 73, 161, 193, 321, 577, 641, 769, 30, 38, 262, 42, 266, 546, 770, 52, 84, 276, 532, 548, 324, 580, 772, 56, 152, 280, 168, 200, 328, 392, 560, 208, 592, 400, 656, 672, 448]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_43, vertices_331, vertices_675, vertices_771, vertices_837, vertices_233, vertices_721, vertices_62, vertices_286, vertices_806, vertices_564, vertices_468, vertices_596, vertices_696, vertices_408, vertices_456] (by decide +kernel)
  polygons := literalFinset [vertices_11, vertices_35, vertices_259, vertices_515, vertices_41, vertices_73, vertices_161, vertices_193, vertices_321, vertices_577, vertices_641, vertices_769, vertices_30, vertices_38, vertices_262, vertices_42, vertices_266, vertices_546, vertices_770, vertices_52, vertices_84, vertices_276, vertices_532, vertices_548, vertices_324, vertices_580, vertices_772, vertices_56, vertices_152, vertices_280, vertices_168, vertices_200, vertices_328, vertices_392, vertices_560, vertices_208, vertices_592, vertices_400, vertices_656, vertices_672, vertices_448] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_43), (false, vertices_331), (false, vertices_675), (false, vertices_771), (false, vertices_837), (false, vertices_233), (false, vertices_721), (true, vertices_30), (true, vertices_38), (true, vertices_262), (true, vertices_52), (true, vertices_84), (true, vertices_276), (true, vertices_532), (true, vertices_548), (true, vertices_56), (true, vertices_152), (true, vertices_280), (true, vertices_392), (true, vertices_560), (true, vertices_400), (true, vertices_448)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 16 20 22 24 26 27 28 29 30
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_43) then 0 else
  if p.val = (false, vertices_331) then 17 else
  if p.val = (false, vertices_675) then 18 else
  if p.val = (false, vertices_771) then 1 else
  if p.val = (false, vertices_837) then 21 else
  if p.val = (false, vertices_233) then 23 else
  if p.val = (false, vertices_721) then 25 else
  if p.val = (true, vertices_30) then 19 else
  if p.val = (true, vertices_38) then 2 else
  if p.val = (true, vertices_262) then 3 else
  if p.val = (true, vertices_52) then 4 else
  if p.val = (true, vertices_84) then 5 else
  if p.val = (true, vertices_276) then 6 else
  if p.val = (true, vertices_532) then 7 else
  if p.val = (true, vertices_548) then 8 else
  if p.val = (true, vertices_56) then 9 else
  if p.val = (true, vertices_152) then 10 else
  if p.val = (true, vertices_280) then 11 else
  if p.val = (true, vertices_392) then 12 else
  if p.val = (true, vertices_560) then 13 else
  if p.val = (true, vertices_400) then 14 else
  if p.val = (true, vertices_448) then 15 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_43), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_771), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_38), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_262), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_52), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_84), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_276), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_532), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_548), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_56), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_152), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_280), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_392), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_560), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_400), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_448), by decide +kernel⟩
  | 16 => Sum.inl 0
  | 17 => Sum.inr ⟨(false, vertices_331), by decide +kernel⟩
  | 18 => Sum.inr ⟨(false, vertices_675), by decide +kernel⟩
  | 19 => Sum.inr ⟨(true, vertices_30), by decide +kernel⟩
  | 20 => Sum.inl 1
  | 21 => Sum.inr ⟨(false, vertices_837), by decide +kernel⟩
  | 22 => Sum.inl 2
  | 23 => Sum.inr ⟨(false, vertices_233), by decide +kernel⟩
  | 24 => Sum.inl 3
  | 25 => Sum.inr ⟨(false, vertices_721), by decide +kernel⟩
  | 26 => Sum.inl 4
  | 27 => Sum.inl 5
  | 28 => Sum.inl 6
  | 29 => Sum.inl 7
  | 30 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 1 3 5 6 7 468 84 3
cert_row_4 1 0 1 4 7 8 806 38 3
cert_row_2 2 0 1 2 3 30
cert_row_4 3 2 3 4 6 8 696 56 3
cert_rows
cert_pivot_2 5 7 0 2
cert_heightProof 4
cert_coverFacet 0 62
cert_cover_5 0 2 0 1 2 4 30 62 3
cert_coverFacet 1 286
cert_cover_5 1 2 0 1 2 7 30 286 3
cert_coverFacet 2 806
cert_cover_5 2 1 0 1 4 7 38 806 3
cert_coverFacet 3 564
cert_cover_2 3 3 1 4 8 52 564 3
cert_coverFacet 4 468
cert_cover_5 4 0 1 3 5 6 84 468 3
cert_coverFacet 5 596
cert_cover_2 5 3 1 5 8 84 596 3
cert_coverFacet 6 696
cert_cover_5 6 3 2 3 4 6 56 696 3
cert_coverFacet 7 408
cert_cover_2 7 3 2 6 7 152 408 3
cert_coverFacet 8 456
cert_cover_2 8 5 2 6 7 200 456 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0303

end
end BundlePart19

section BundlePart20
/- Source: ProjectionCertificates/R_m16e10q1_0304.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0304

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [651, 285, 541, 357, 709, 457, 614, 154, 538, 242, 818, 706, 788, 804, 440, 480, 29, 69, 261, 517, 137, 265, 521, 193, 321, 641, 26, 138, 522, 50, 146, 530, 98, 546, 194, 578, 642, 276, 532, 100, 292, 548, 580, 772, 152, 280, 536, 392, 176, 304, 784, 224, 352, 416, 800, 448, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_651, vertices_285, vertices_541, vertices_357, vertices_709, vertices_457, vertices_614, vertices_154, vertices_538, vertices_242, vertices_818, vertices_706, vertices_788, vertices_804, vertices_440, vertices_480] (by decide +kernel)
  polygons := literalFinset [vertices_29, vertices_69, vertices_261, vertices_517, vertices_137, vertices_265, vertices_521, vertices_193, vertices_321, vertices_641, vertices_26, vertices_138, vertices_522, vertices_50, vertices_146, vertices_530, vertices_98, vertices_546, vertices_194, vertices_578, vertices_642, vertices_276, vertices_532, vertices_100, vertices_292, vertices_548, vertices_580, vertices_772, vertices_152, vertices_280, vertices_536, vertices_392, vertices_176, vertices_304, vertices_784, vertices_224, vertices_352, vertices_416, vertices_800, vertices_448, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_651), (false, vertices_285), (false, vertices_541), (false, vertices_357), (false, vertices_709), (false, vertices_457), (true, vertices_26), (true, vertices_50), (true, vertices_146), (true, vertices_530), (true, vertices_98), (true, vertices_546), (true, vertices_194), (true, vertices_578), (true, vertices_548), (true, vertices_772), (true, vertices_152), (true, vertices_176), (true, vertices_304), (true, vertices_784), (true, vertices_224), (true, vertices_416), (true, vertices_800)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 17 23 19 26 27 28 29 30 31
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_651) then 18 else
  if p.val = (false, vertices_285) then 20 else
  if p.val = (false, vertices_541) then 21 else
  if p.val = (false, vertices_357) then 24 else
  if p.val = (false, vertices_709) then 25 else
  if p.val = (false, vertices_457) then 22 else
  if p.val = (true, vertices_26) then 0 else
  if p.val = (true, vertices_50) then 1 else
  if p.val = (true, vertices_146) then 2 else
  if p.val = (true, vertices_530) then 3 else
  if p.val = (true, vertices_98) then 4 else
  if p.val = (true, vertices_546) then 5 else
  if p.val = (true, vertices_194) then 6 else
  if p.val = (true, vertices_578) then 7 else
  if p.val = (true, vertices_548) then 8 else
  if p.val = (true, vertices_772) then 9 else
  if p.val = (true, vertices_152) then 10 else
  if p.val = (true, vertices_176) then 11 else
  if p.val = (true, vertices_304) then 12 else
  if p.val = (true, vertices_784) then 13 else
  if p.val = (true, vertices_224) then 14 else
  if p.val = (true, vertices_416) then 15 else
  if p.val = (true, vertices_800) then 16 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_26), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_50), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_146), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_530), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_98), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_546), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_194), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_578), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_548), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_772), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_152), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_176), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_304), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_784), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_224), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_416), by decide +kernel⟩
  | 16 => Sum.inr ⟨(true, vertices_800), by decide +kernel⟩
  | 17 => Sum.inl 0
  | 18 => Sum.inr ⟨(false, vertices_651), by decide +kernel⟩
  | 19 => Sum.inl 2
  | 20 => Sum.inr ⟨(false, vertices_285), by decide +kernel⟩
  | 21 => Sum.inr ⟨(false, vertices_541), by decide +kernel⟩
  | 22 => Sum.inr ⟨(false, vertices_457), by decide +kernel⟩
  | 23 => Sum.inl 1
  | 24 => Sum.inr ⟨(false, vertices_357), by decide +kernel⟩
  | 25 => Sum.inr ⟨(false, vertices_709), by decide +kernel⟩
  | 26 => Sum.inl 3
  | 27 => Sum.inl 4
  | 28 => Sum.inl 5
  | 29 => Sum.inl 6
  | 30 => Sum.inl 7
  | 31 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 4 5 8 614 98 1
cert_row_4 1 0 3 4 5 6 242 50 3
cert_row_4 2 0 3 4 7 8 818 50 3
cert_row_4 3 2 3 4 6 7 440 152 2
cert_rows
cert_pivot_2 1 5 0 2
cert_heightProof 4
cert_coverFacet 0 614
cert_cover_5 0 0 0 1 4 5 98 614 1
cert_coverFacet 1 154
cert_cover_2 1 2 0 3 6 26 154 3
cert_coverFacet 2 538
cert_cover_2 2 2 0 3 8 26 538 3
cert_coverFacet 3 242
cert_cover_5 3 1 0 3 4 5 50 242 3
cert_coverFacet 4 818
cert_cover_5 4 2 0 3 4 7 50 818 3
cert_coverFacet 5 706
cert_cover_2 5 5 0 6 8 194 706 3
cert_coverFacet 6 788
cert_cover_2 6 3 1 7 8 276 788 3
cert_coverFacet 7 804
cert_cover_2 7 4 1 7 8 292 804 3
cert_coverFacet 8 440
cert_cover_5 8 3 2 3 4 6 152 440 2
cert_coverFacet 9 480
cert_cover_2 9 5 4 6 7 224 480 3
cert_coveringFacets_5
cert_coveringProof
cert_certificate 4 10
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0304

end
end BundlePart20

section BundlePart21
/- Source: ProjectionCertificates/R_m16e10q1_0305.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0305

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [803, 93, 309, 613, 665, 585, 785, 422, 234, 618, 650, 914, 340, 228, 452, 472, 21, 37, 69, 25, 73, 521, 273, 529, 289, 545, 577, 769, 106, 138, 522, 162, 290, 546, 386, 642, 770, 84, 276, 100, 164, 292, 196, 324, 388, 88, 152, 200, 584, 648, 336, 400, 656, 784, 224, 608, 448]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_803, vertices_93, vertices_309, vertices_613, vertices_665, vertices_585, vertices_785, vertices_422, vertices_234, vertices_618, vertices_650, vertices_914, vertices_340, vertices_228, vertices_452, vertices_472] (by decide +kernel)
  polygons := literalFinset [vertices_21, vertices_37, vertices_69, vertices_25, vertices_73, vertices_521, vertices_273, vertices_529, vertices_289, vertices_545, vertices_577, vertices_769, vertices_106, vertices_138, vertices_522, vertices_162, vertices_290, vertices_546, vertices_386, vertices_642, vertices_770, vertices_84, vertices_276, vertices_100, vertices_164, vertices_292, vertices_196, vertices_324, vertices_388, vertices_88, vertices_152, vertices_200, vertices_584, vertices_648, vertices_336, vertices_400, vertices_656, vertices_784, vertices_224, vertices_608, vertices_448] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_803), (false, vertices_93), (false, vertices_309), (false, vertices_613), (false, vertices_665), (false, vertices_585), (false, vertices_785), (true, vertices_106), (true, vertices_138), (true, vertices_522), (true, vertices_162), (true, vertices_386), (true, vertices_642), (true, vertices_164), (true, vertices_196), (true, vertices_324), (true, vertices_388), (true, vertices_200), (true, vertices_336), (true, vertices_400), (true, vertices_224), (true, vertices_448)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 16 19 23 25 26 27 28 29 30
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_803) then 17 else
  if p.val = (false, vertices_93) then 20 else
  if p.val = (false, vertices_309) then 21 else
  if p.val = (false, vertices_613) then 22 else
  if p.val = (false, vertices_665) then 24 else
  if p.val = (false, vertices_585) then 0 else
  if p.val = (false, vertices_785) then 1 else
  if p.val = (true, vertices_106) then 18 else
  if p.val = (true, vertices_138) then 2 else
  if p.val = (true, vertices_522) then 3 else
  if p.val = (true, vertices_162) then 4 else
  if p.val = (true, vertices_386) then 5 else
  if p.val = (true, vertices_642) then 6 else
  if p.val = (true, vertices_164) then 7 else
  if p.val = (true, vertices_196) then 8 else
  if p.val = (true, vertices_324) then 9 else
  if p.val = (true, vertices_388) then 10 else
  if p.val = (true, vertices_200) then 11 else
  if p.val = (true, vertices_336) then 12 else
  if p.val = (true, vertices_400) then 13 else
  if p.val = (true, vertices_224) then 14 else
  if p.val = (true, vertices_448) then 15 else
  0
cert_priority
cert_nodeAtPriority_5 0 585 1 785 138 522 162 386 642 164 196 324 388 200 336 400 224 448 803 106 93 309 613 665
cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 4 6 7 422 162 1
cert_row_2 1 0 2 4 5 106
cert_row_4 2 0 3 6 7 8 914 386 1
cert_row_4 3 2 3 5 6 7 472 88 3
cert_rows
cert_pivot_2 1 4 0 2
cert_heightProof 4
cert_coverFacet 0 422
cert_cover_5 0 0 0 1 4 6 162 422 1
cert_coverFacet 1 234
cert_cover_5 1 1 0 2 4 6 106 234 3
cert_coverFacet 2 618
cert_cover_5 2 1 0 2 4 8 106 618 3
cert_coverFacet 3 650
cert_cover_2 3 2 0 6 8 138 650 3
cert_coverFacet 4 914
cert_cover_5 4 2 0 3 6 7 386 914 1
cert_coverFacet 5 340
cert_cover_2 5 3 1 5 7 84 340 3
cert_coverFacet 6 228
cert_cover_2 6 4 1 5 6 100 228 3
cert_coverFacet 7 452
cert_cover_2 7 5 1 6 7 196 452 3
cert_coverFacet 8 472
cert_cover_5 8 3 2 3 5 6 88 472 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0305

end
end BundlePart21

section BundlePart22
/- Source: ProjectionCertificates/R_m16e10q1_0306.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0306

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [563, 595, 341, 805, 709, 313, 654, 170, 810, 242, 706, 460, 780, 184, 408, 464, 531, 69, 261, 517, 49, 81, 273, 289, 545, 577, 42, 138, 522, 50, 82, 162, 546, 194, 578, 642, 140, 268, 524, 196, 324, 644, 772, 56, 152, 280, 168, 296, 392, 776, 176, 208, 336, 400, 800, 448, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_563, vertices_595, vertices_341, vertices_805, vertices_709, vertices_313, vertices_654, vertices_170, vertices_810, vertices_242, vertices_706, vertices_460, vertices_780, vertices_184, vertices_408, vertices_464] (by decide +kernel)
  polygons := literalFinset [vertices_531, vertices_69, vertices_261, vertices_517, vertices_49, vertices_81, vertices_273, vertices_289, vertices_545, vertices_577, vertices_42, vertices_138, vertices_522, vertices_50, vertices_82, vertices_162, vertices_546, vertices_194, vertices_578, vertices_642, vertices_140, vertices_268, vertices_524, vertices_196, vertices_324, vertices_644, vertices_772, vertices_56, vertices_152, vertices_280, vertices_168, vertices_296, vertices_392, vertices_776, vertices_176, vertices_208, vertices_336, vertices_400, vertices_800, vertices_448, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_563), (false, vertices_595), (false, vertices_341), (false, vertices_805), (false, vertices_709), (false, vertices_313), (true, vertices_42), (true, vertices_138), (true, vertices_522), (true, vertices_162), (true, vertices_194), (true, vertices_642), (true, vertices_140), (true, vertices_268), (true, vertices_524), (true, vertices_152), (true, vertices_168), (true, vertices_392), (true, vertices_776), (true, vertices_176), (true, vertices_208), (true, vertices_400), (true, vertices_448)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 17 20 24 26 27 28 29 30 31
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_563) then 18 else
  if p.val = (false, vertices_595) then 19 else
  if p.val = (false, vertices_341) then 21 else
  if p.val = (false, vertices_805) then 22 else
  if p.val = (false, vertices_709) then 23 else
  if p.val = (false, vertices_313) then 25 else
  if p.val = (true, vertices_42) then 0 else
  if p.val = (true, vertices_138) then 1 else
  if p.val = (true, vertices_522) then 2 else
  if p.val = (true, vertices_162) then 3 else
  if p.val = (true, vertices_194) then 4 else
  if p.val = (true, vertices_642) then 5 else
  if p.val = (true, vertices_140) then 6 else
  if p.val = (true, vertices_268) then 7 else
  if p.val = (true, vertices_524) then 8 else
  if p.val = (true, vertices_152) then 9 else
  if p.val = (true, vertices_168) then 10 else
  if p.val = (true, vertices_392) then 11 else
  if p.val = (true, vertices_776) then 12 else
  if p.val = (true, vertices_176) then 13 else
  if p.val = (true, vertices_208) then 14 else
  if p.val = (true, vertices_400) then 15 else
  if p.val = (true, vertices_448) then 16 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_42), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_138), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_522), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_162), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_194), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_642), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_140), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_268), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_524), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_152), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_168), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_392), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_776), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_176), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_208), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_400), by decide +kernel⟩
  | 16 => Sum.inr ⟨(true, vertices_448), by decide +kernel⟩
  | 17 => Sum.inl 0
  | 18 => Sum.inr ⟨(false, vertices_563), by decide +kernel⟩
  | 19 => Sum.inr ⟨(false, vertices_595), by decide +kernel⟩
  | 20 => Sum.inl 1
  | 21 => Sum.inr ⟨(false, vertices_341), by decide +kernel⟩
  | 22 => Sum.inr ⟨(false, vertices_805), by decide +kernel⟩
  | 23 => Sum.inr ⟨(false, vertices_709), by decide +kernel⟩
  | 24 => Sum.inl 2
  | 25 => Sum.inr ⟨(false, vertices_313), by decide +kernel⟩
  | 26 => Sum.inl 3
  | 27 => Sum.inl 4
  | 28 => Sum.inl 5
  | 29 => Sum.inl 6
  | 30 => Sum.inl 7
  | 31 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 3 4 5 6 242 50 3
cert_row_4 1 0 2 4 7 8 810 42 3
cert_row_4 2 0 1 2 6 8 654 138 1
cert_row_4 3 1 2 5 6 7 460 140 2
cert_rows
cert_pivot_2 3 4 0 1
cert_heightProof 4
cert_coverFacet 0 654
cert_cover_5 0 2 0 1 2 6 138 654 1
cert_coverFacet 1 170
cert_cover_2 1 2 0 4 6 42 170 3
cert_coverFacet 2 810
cert_cover_5 2 1 0 2 4 7 42 810 3
cert_coverFacet 3 242
cert_cover_5 3 0 0 3 4 5 50 242 3
cert_coverFacet 4 706
cert_cover_2 4 5 0 6 8 194 706 3
cert_coverFacet 5 460
cert_cover_5 5 3 1 2 5 6 140 460 2
cert_coverFacet 6 780
cert_cover_2 6 2 1 7 8 268 780 3
cert_coverFacet 7 184
cert_cover_2 7 3 2 4 6 56 184 3
cert_coverFacet 8 408
cert_cover_2 8 3 2 6 7 152 408 3
cert_coverFacet 9 464
cert_cover_2 9 5 3 6 7 208 464 3
cert_coveringFacets_5
cert_coveringProof
cert_certificate 4 10
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0306

end
end BundlePart22

section BundlePart23
/- Source: ProjectionCertificates/R_m16e10q1_0307.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0307

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [779, 563, 339, 613, 837, 241, 654, 394, 402, 658, 364, 172, 780, 692, 472, 232, 19, 259, 515, 581, 49, 81, 97, 545, 321, 769, 138, 266, 522, 146, 274, 530, 386, 642, 44, 140, 268, 524, 100, 164, 548, 324, 644, 772, 104, 168, 200, 328, 392, 776, 176, 560, 208, 336, 400, 656, 224]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_779, vertices_563, vertices_339, vertices_613, vertices_837, vertices_241, vertices_654, vertices_394, vertices_402, vertices_658, vertices_364, vertices_172, vertices_780, vertices_692, vertices_472, vertices_232] (by decide +kernel)
  polygons := literalFinset [vertices_19, vertices_259, vertices_515, vertices_581, vertices_49, vertices_81, vertices_97, vertices_545, vertices_321, vertices_769, vertices_138, vertices_266, vertices_522, vertices_146, vertices_274, vertices_530, vertices_386, vertices_642, vertices_44, vertices_140, vertices_268, vertices_524, vertices_100, vertices_164, vertices_548, vertices_324, vertices_644, vertices_772, vertices_104, vertices_168, vertices_200, vertices_328, vertices_392, vertices_776, vertices_176, vertices_560, vertices_208, vertices_336, vertices_400, vertices_656, vertices_224] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_779), (false, vertices_563), (false, vertices_339), (false, vertices_613), (false, vertices_837), (false, vertices_241), (true, vertices_138), (true, vertices_146), (true, vertices_386), (true, vertices_642), (true, vertices_44), (true, vertices_140), (true, vertices_268), (true, vertices_524), (true, vertices_164), (true, vertices_644), (true, vertices_104), (true, vertices_168), (true, vertices_200), (true, vertices_328), (true, vertices_392), (true, vertices_400), (true, vertices_656)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 17 21 24 25 27 28 29 30 31
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_779) then 18 else
  if p.val = (false, vertices_563) then 19 else
  if p.val = (false, vertices_339) then 20 else
  if p.val = (false, vertices_613) then 22 else
  if p.val = (false, vertices_837) then 23 else
  if p.val = (false, vertices_241) then 26 else
  if p.val = (true, vertices_138) then 0 else
  if p.val = (true, vertices_146) then 1 else
  if p.val = (true, vertices_386) then 2 else
  if p.val = (true, vertices_642) then 3 else
  if p.val = (true, vertices_44) then 4 else
  if p.val = (true, vertices_140) then 5 else
  if p.val = (true, vertices_268) then 6 else
  if p.val = (true, vertices_524) then 7 else
  if p.val = (true, vertices_164) then 8 else
  if p.val = (true, vertices_644) then 9 else
  if p.val = (true, vertices_104) then 10 else
  if p.val = (true, vertices_168) then 11 else
  if p.val = (true, vertices_200) then 12 else
  if p.val = (true, vertices_328) then 13 else
  if p.val = (true, vertices_392) then 14 else
  if p.val = (true, vertices_400) then 15 else
  if p.val = (true, vertices_656) then 16 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_138), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_146), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_386), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_642), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_44), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_140), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_268), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_524), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_164), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_644), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_104), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_168), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_200), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_328), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_392), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_400), by decide +kernel⟩
  | 16 => Sum.inr ⟨(true, vertices_656), by decide +kernel⟩
  | 17 => Sum.inl 0
  | 18 => Sum.inr ⟨(false, vertices_779), by decide +kernel⟩
  | 19 => Sum.inr ⟨(false, vertices_563), by decide +kernel⟩
  | 20 => Sum.inr ⟨(false, vertices_339), by decide +kernel⟩
  | 21 => Sum.inl 1
  | 22 => Sum.inr ⟨(false, vertices_613), by decide +kernel⟩
  | 23 => Sum.inr ⟨(false, vertices_837), by decide +kernel⟩
  | 24 => Sum.inl 2
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
cert_row_4 0 0 1 2 6 8 654 138 1
cert_row_4 1 1 3 4 6 8 692 164 1
cert_row_4 2 1 2 4 5 7 364 44 3
cert_row_4 3 2 3 5 6 7 472 200 1
cert_rows
cert_pivot_2 0 8 1 2
cert_heightProof 4
cert_coverFacet 0 654
cert_cover_5 0 0 0 1 2 6 138 654 1
cert_coverFacet 1 394
cert_cover_2 1 2 0 6 7 138 394 3
cert_coverFacet 2 402
cert_cover_2 2 3 0 6 7 146 402 3
cert_coverFacet 3 658
cert_cover_2 3 3 0 6 8 146 658 3
cert_coverFacet 4 364
cert_cover_5 4 2 1 2 4 5 44 364 3
cert_coverFacet 5 172
cert_cover_2 5 2 1 4 6 44 172 3
cert_coverFacet 6 780
cert_cover_2 6 2 1 7 8 268 780 3
cert_coverFacet 7 692
cert_cover_5 7 1 1 3 4 6 164 692 1
cert_coverFacet 8 472
cert_cover_5 8 3 2 3 5 6 200 472 1
cert_coverFacet 9 232
cert_cover_2 9 4 2 5 6 104 232 3
cert_coveringFacets_5
cert_coveringProof
cert_certificate 4 10
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0307

end
end BundlePart23

section BundlePart24
/- Source: ProjectionCertificates/R_m16e10q1_0308.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0308

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [647, 779, 307, 163, 205, 525, 425, 562, 786, 738, 348, 796, 628, 708, 456, 496, 35, 131, 259, 515, 13, 133, 517, 137, 265, 521, 161, 289, 50, 274, 530, 162, 546, 642, 770, 284, 76, 524, 84, 532, 196, 580, 644, 200, 328, 392, 776, 112, 304, 560, 336, 784, 224, 608, 416, 448, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_647, vertices_779, vertices_307, vertices_163, vertices_205, vertices_525, vertices_425, vertices_562, vertices_786, vertices_738, vertices_348, vertices_796, vertices_628, vertices_708, vertices_456, vertices_496] (by decide +kernel)
  polygons := literalFinset [vertices_35, vertices_131, vertices_259, vertices_515, vertices_13, vertices_133, vertices_517, vertices_137, vertices_265, vertices_521, vertices_161, vertices_289, vertices_50, vertices_274, vertices_530, vertices_162, vertices_546, vertices_642, vertices_770, vertices_284, vertices_76, vertices_524, vertices_84, vertices_532, vertices_196, vertices_580, vertices_644, vertices_200, vertices_328, vertices_392, vertices_776, vertices_112, vertices_304, vertices_560, vertices_336, vertices_784, vertices_224, vertices_608, vertices_416, vertices_448, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_647), (false, vertices_779), (false, vertices_307), (false, vertices_163), (false, vertices_205), (false, vertices_525), (false, vertices_425), (true, vertices_530), (true, vertices_546), (true, vertices_284), (true, vertices_84), (true, vertices_532), (true, vertices_580), (true, vertices_328), (true, vertices_112), (true, vertices_560), (true, vertices_336), (true, vertices_784), (true, vertices_224), (true, vertices_608), (true, vertices_448), (true, vertices_704)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 16 20 23 25 26 27 28 29 30
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_647) then 17 else
  if p.val = (false, vertices_779) then 18 else
  if p.val = (false, vertices_307) then 19 else
  if p.val = (false, vertices_163) then 0 else
  if p.val = (false, vertices_205) then 21 else
  if p.val = (false, vertices_525) then 1 else
  if p.val = (false, vertices_425) then 24 else
  if p.val = (true, vertices_530) then 2 else
  if p.val = (true, vertices_546) then 3 else
  if p.val = (true, vertices_284) then 22 else
  if p.val = (true, vertices_84) then 4 else
  if p.val = (true, vertices_532) then 5 else
  if p.val = (true, vertices_580) then 6 else
  if p.val = (true, vertices_328) then 7 else
  if p.val = (true, vertices_112) then 8 else
  if p.val = (true, vertices_560) then 9 else
  if p.val = (true, vertices_336) then 10 else
  if p.val = (true, vertices_784) then 11 else
  if p.val = (true, vertices_224) then 12 else
  if p.val = (true, vertices_608) then 13 else
  if p.val = (true, vertices_448) then 14 else
  if p.val = (true, vertices_704) then 15 else
  0
cert_priority
cert_nodeAtPriority_60 163 525 530 546 84 532 580 328 112 560 336 784 224 608 448 704 647 779 307 205 284 425
cert_priority_injective
cert_incidenceProof
cert_row_2 0 1 2 3 7 284
cert_row_4 1 0 4 5 6 8 738 162 2
cert_row_4 2 1 3 4 5 8 628 84 2
cert_row_4 3 3 4 5 6 7 496 112 3
cert_rows
cert_pivot_2 2 0 1 3
cert_heightProof 4
cert_coverFacet 0 562
cert_cover_2 0 3 0 4 8 50 562 3
cert_coverFacet 1 786
cert_cover_2 1 3 0 7 8 274 786 3
cert_coverFacet 2 738
cert_cover_5 2 1 0 4 5 6 162 738 2
cert_coverFacet 3 348
cert_cover_5 3 0 1 2 3 5 284 348 3
cert_coverFacet 4 796
cert_cover_5 4 0 1 2 3 8 284 796 3
cert_coverFacet 5 628
cert_cover_5 5 2 1 3 4 5 84 628 2
cert_coverFacet 6 708
cert_cover_2 6 5 1 6 8 196 708 3
cert_coverFacet 7 456
cert_cover_2 7 5 2 6 7 200 456 3
cert_coverFacet 8 496
cert_cover_5 8 3 3 4 5 6 112 496 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0308

end
end BundlePart24

section BundlePart25
/- Source: ProjectionCertificates/R_m16e10q1_0309.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0309

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [451, 805, 617, 425, 201, 849, 158, 174, 342, 294, 722, 418, 572, 788, 664, 712, 41, 73, 137, 289, 545, 193, 321, 577, 385, 769, 142, 22, 38, 262, 82, 146, 162, 290, 194, 322, 386, 28, 44, 276, 532, 292, 548, 772, 152, 536, 168, 552, 200, 584, 648, 336, 592, 656, 784, 416, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_451, vertices_805, vertices_617, vertices_425, vertices_201, vertices_849, vertices_158, vertices_174, vertices_342, vertices_294, vertices_722, vertices_418, vertices_572, vertices_788, vertices_664, vertices_712] (by decide +kernel)
  polygons := literalFinset [vertices_41, vertices_73, vertices_137, vertices_289, vertices_545, vertices_193, vertices_321, vertices_577, vertices_385, vertices_769, vertices_142, vertices_22, vertices_38, vertices_262, vertices_82, vertices_146, vertices_162, vertices_290, vertices_194, vertices_322, vertices_386, vertices_28, vertices_44, vertices_276, vertices_532, vertices_292, vertices_548, vertices_772, vertices_152, vertices_536, vertices_168, vertices_552, vertices_200, vertices_584, vertices_648, vertices_336, vertices_592, vertices_656, vertices_784, vertices_416, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_451), (false, vertices_805), (false, vertices_617), (false, vertices_425), (false, vertices_201), (false, vertices_849), (true, vertices_142), (true, vertices_22), (true, vertices_38), (true, vertices_262), (true, vertices_82), (true, vertices_146), (true, vertices_162), (true, vertices_290), (true, vertices_28), (true, vertices_44), (true, vertices_276), (true, vertices_532), (true, vertices_152), (true, vertices_536), (true, vertices_648), (true, vertices_656), (true, vertices_704)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 17 20 22 25 27 28 29 30 31
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_451) then 18 else
  if p.val = (false, vertices_805) then 21 else
  if p.val = (false, vertices_617) then 23 else
  if p.val = (false, vertices_425) then 24 else
  if p.val = (false, vertices_201) then 0 else
  if p.val = (false, vertices_849) then 26 else
  if p.val = (true, vertices_142) then 19 else
  if p.val = (true, vertices_22) then 1 else
  if p.val = (true, vertices_38) then 2 else
  if p.val = (true, vertices_262) then 3 else
  if p.val = (true, vertices_82) then 4 else
  if p.val = (true, vertices_146) then 5 else
  if p.val = (true, vertices_162) then 6 else
  if p.val = (true, vertices_290) then 7 else
  if p.val = (true, vertices_28) then 8 else
  if p.val = (true, vertices_44) then 9 else
  if p.val = (true, vertices_276) then 10 else
  if p.val = (true, vertices_532) then 11 else
  if p.val = (true, vertices_152) then 12 else
  if p.val = (true, vertices_536) then 13 else
  if p.val = (true, vertices_648) then 14 else
  if p.val = (true, vertices_656) then 15 else
  if p.val = (true, vertices_704) then 16 else
  0
cert_priority
cert_nodeAtPriority_33 201 22 38 262 82 146 162 290 28 44 276 532 152 536 648 656 704 451 142 805 617 425 849
cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 3 5 7 342 22 3
cert_row_4 1 0 3 5 6 8 722 82 3
cert_row_2 2 0 1 2 6 142
cert_row_4 3 1 2 3 4 8 572 28 3
cert_rows
cert_pivot_2 7 5 0 1
cert_heightProof 4
cert_coverFacet 0 158
cert_cover_5 0 2 0 1 2 3 142 158 3
cert_coverFacet 1 174
cert_cover_5 1 2 0 1 2 4 142 174 3
cert_coverFacet 2 342
cert_cover_5 2 0 0 1 3 5 22 342 3
cert_coverFacet 3 294
cert_cover_2 3 1 0 4 7 38 294 3
cert_coverFacet 4 722
cert_cover_5 4 1 0 3 5 6 82 722 3
cert_coverFacet 5 418
cert_cover_2 5 4 0 6 7 162 418 3
cert_coverFacet 6 572
cert_cover_5 6 3 1 2 3 4 28 572 3
cert_coverFacet 7 788
cert_cover_2 7 3 1 7 8 276 788 3
cert_coverFacet 8 664
cert_cover_2 8 3 2 6 8 152 664 3
cert_coverFacet 9 712
cert_cover_2 9 5 2 6 8 200 712 3
cert_coveringFacets_5
cert_coveringProof
cert_certificate 4 10
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0309

end
end BundlePart25

section BundlePart26
/- Source: ProjectionCertificates/R_m16e10q1_0310.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0310

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [779, 677, 361, 713, 817, 225, 206, 654, 566, 86, 346, 786, 436, 212, 464, 480, 73, 265, 521, 97, 161, 289, 545, 193, 641, 769, 142, 22, 70, 518, 74, 266, 522, 82, 274, 530, 770, 52, 84, 148, 164, 548, 196, 644, 200, 328, 648, 304, 560, 208, 336, 400, 784, 224, 352, 416, 448]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_779, vertices_677, vertices_361, vertices_713, vertices_817, vertices_225, vertices_206, vertices_654, vertices_566, vertices_86, vertices_346, vertices_786, vertices_436, vertices_212, vertices_464, vertices_480] (by decide +kernel)
  polygons := literalFinset [vertices_73, vertices_265, vertices_521, vertices_97, vertices_161, vertices_289, vertices_545, vertices_193, vertices_641, vertices_769, vertices_142, vertices_22, vertices_70, vertices_518, vertices_74, vertices_266, vertices_522, vertices_82, vertices_274, vertices_530, vertices_770, vertices_52, vertices_84, vertices_148, vertices_164, vertices_548, vertices_196, vertices_644, vertices_200, vertices_328, vertices_648, vertices_304, vertices_560, vertices_208, vertices_336, vertices_400, vertices_784, vertices_224, vertices_352, vertices_416, vertices_448] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_779), (false, vertices_677), (false, vertices_361), (false, vertices_713), (false, vertices_817), (false, vertices_225), (true, vertices_142), (true, vertices_22), (true, vertices_70), (true, vertices_518), (true, vertices_74), (true, vertices_82), (true, vertices_274), (true, vertices_530), (true, vertices_52), (true, vertices_84), (true, vertices_148), (true, vertices_196), (true, vertices_208), (true, vertices_336), (true, vertices_400), (true, vertices_416), (true, vertices_448)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 17 20 22 25 27 28 29 30 31
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_779) then 18 else
  if p.val = (false, vertices_677) then 21 else
  if p.val = (false, vertices_361) then 23 else
  if p.val = (false, vertices_713) then 24 else
  if p.val = (false, vertices_817) then 26 else
  if p.val = (false, vertices_225) then 0 else
  if p.val = (true, vertices_142) then 19 else
  if p.val = (true, vertices_22) then 1 else
  if p.val = (true, vertices_70) then 2 else
  if p.val = (true, vertices_518) then 3 else
  if p.val = (true, vertices_74) then 4 else
  if p.val = (true, vertices_82) then 5 else
  if p.val = (true, vertices_274) then 6 else
  if p.val = (true, vertices_530) then 7 else
  if p.val = (true, vertices_52) then 8 else
  if p.val = (true, vertices_84) then 9 else
  if p.val = (true, vertices_148) then 10 else
  if p.val = (true, vertices_196) then 11 else
  if p.val = (true, vertices_208) then 12 else
  if p.val = (true, vertices_336) then 13 else
  if p.val = (true, vertices_400) then 14 else
  if p.val = (true, vertices_416) then 15 else
  if p.val = (true, vertices_448) then 16 else
  0
cert_priority
cert_nodeAtPriority_33 225 22 70 518 74 82 274 530 52 84 148 196 208 336 400 416 448 779 142 677 361 713 817
cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 3 4 8 566 22 3
cert_row_4 1 0 2 3 5 7 346 74 2
cert_row_2 2 0 1 2 6 142
cert_row_4 3 1 3 4 6 7 436 52 3
cert_rows
cert_pivot_2 8 5 0 1
cert_heightProof 4
cert_coverFacet 0 206
cert_cover_5 0 2 0 1 2 5 142 206 3
cert_coverFacet 1 654
cert_cover_5 1 2 0 1 2 8 142 654 3
cert_coverFacet 2 566
cert_cover_5 2 0 0 1 3 4 22 566 3
cert_coverFacet 3 86
cert_cover_2 3 1 0 3 5 22 86 3
cert_coverFacet 4 346
cert_cover_5 4 1 0 2 3 5 74 346 2
cert_coverFacet 5 786
cert_cover_2 5 3 0 7 8 274 786 3
cert_coverFacet 6 436
cert_cover_5 6 3 1 3 4 6 52 436 3
cert_coverFacet 7 212
cert_cover_2 7 3 1 5 6 84 212 3
cert_coverFacet 8 464
cert_cover_2 8 5 3 6 7 208 464 3
cert_coverFacet 9 480
cert_cover_2 9 5 4 6 7 224 480 3
cert_coveringFacets_5
cert_coveringProof
cert_certificate 4 10
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0310

end
end BundlePart26

section BundlePart27
/- Source: ProjectionCertificates/R_m16e10q1_0311.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0311

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [647, 781, 229, 357, 665, 457, 310, 166, 774, 794, 562, 738, 376, 216, 624, 720, 101, 133, 261, 517, 137, 265, 521, 193, 321, 641, 38, 134, 262, 518, 50, 274, 530, 162, 546, 642, 770, 164, 292, 772, 88, 152, 280, 536, 200, 328, 776, 112, 304, 560, 208, 592, 656, 224, 352, 608, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_647, vertices_781, vertices_229, vertices_357, vertices_665, vertices_457, vertices_310, vertices_166, vertices_774, vertices_794, vertices_562, vertices_738, vertices_376, vertices_216, vertices_624, vertices_720] (by decide +kernel)
  polygons := literalFinset [vertices_101, vertices_133, vertices_261, vertices_517, vertices_137, vertices_265, vertices_521, vertices_193, vertices_321, vertices_641, vertices_38, vertices_134, vertices_262, vertices_518, vertices_50, vertices_274, vertices_530, vertices_162, vertices_546, vertices_642, vertices_770, vertices_164, vertices_292, vertices_772, vertices_88, vertices_152, vertices_280, vertices_536, vertices_200, vertices_328, vertices_776, vertices_112, vertices_304, vertices_560, vertices_208, vertices_592, vertices_656, vertices_224, vertices_352, vertices_608, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_647), (false, vertices_781), (false, vertices_229), (false, vertices_357), (false, vertices_665), (false, vertices_457), (true, vertices_38), (true, vertices_262), (true, vertices_50), (true, vertices_274), (true, vertices_530), (true, vertices_162), (true, vertices_546), (true, vertices_770), (true, vertices_88), (true, vertices_280), (true, vertices_112), (true, vertices_304), (true, vertices_560), (true, vertices_208), (true, vertices_592), (true, vertices_608), (true, vertices_704)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 17 19 23 26 27 28 29 30 31
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_647) then 18 else
  if p.val = (false, vertices_781) then 20 else
  if p.val = (false, vertices_229) then 21 else
  if p.val = (false, vertices_357) then 22 else
  if p.val = (false, vertices_665) then 24 else
  if p.val = (false, vertices_457) then 25 else
  if p.val = (true, vertices_38) then 0 else
  if p.val = (true, vertices_262) then 1 else
  if p.val = (true, vertices_50) then 2 else
  if p.val = (true, vertices_274) then 3 else
  if p.val = (true, vertices_530) then 4 else
  if p.val = (true, vertices_162) then 5 else
  if p.val = (true, vertices_546) then 6 else
  if p.val = (true, vertices_770) then 7 else
  if p.val = (true, vertices_88) then 8 else
  if p.val = (true, vertices_280) then 9 else
  if p.val = (true, vertices_112) then 10 else
  if p.val = (true, vertices_304) then 11 else
  if p.val = (true, vertices_560) then 12 else
  if p.val = (true, vertices_208) then 13 else
  if p.val = (true, vertices_592) then 14 else
  if p.val = (true, vertices_608) then 15 else
  if p.val = (true, vertices_704) then 16 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_38), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_262), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_50), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_274), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_530), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_162), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_546), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_770), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_88), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_280), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_112), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_304), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_560), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_208), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_592), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_608), by decide +kernel⟩
  | 16 => Sum.inr ⟨(true, vertices_704), by decide +kernel⟩
  | 17 => Sum.inl 0
  | 18 => Sum.inr ⟨(false, vertices_647), by decide +kernel⟩
  | 19 => Sum.inl 1
  | 20 => Sum.inr ⟨(false, vertices_781), by decide +kernel⟩
  | 21 => Sum.inr ⟨(false, vertices_229), by decide +kernel⟩
  | 22 => Sum.inr ⟨(false, vertices_357), by decide +kernel⟩
  | 23 => Sum.inl 2
  | 24 => Sum.inr ⟨(false, vertices_665), by decide +kernel⟩
  | 25 => Sum.inr ⟨(false, vertices_457), by decide +kernel⟩
  | 26 => Sum.inl 3
  | 27 => Sum.inl 4
  | 28 => Sum.inl 5
  | 29 => Sum.inl 6
  | 30 => Sum.inl 7
  | 31 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 3 4 7 310 38 2
cert_row_4 1 0 4 5 6 8 738 162 2
cert_row_4 2 0 2 3 7 8 794 274 1
cert_row_4 3 2 3 4 5 7 376 88 2
cert_rows
cert_pivot_2 1 6 0 2
cert_heightProof 4
cert_coverFacet 0 310
cert_cover_5 0 0 0 1 3 4 38 310 2
cert_coverFacet 1 166
cert_cover_2 1 1 0 4 6 38 166 3
cert_coverFacet 2 774
cert_cover_2 2 1 0 7 8 262 774 3
cert_coverFacet 3 794
cert_cover_5 3 2 0 2 3 7 274 794 1
cert_coverFacet 4 562
cert_cover_2 4 3 0 4 8 50 562 3
cert_coverFacet 5 738
cert_cover_5 5 1 0 4 5 6 162 738 2
cert_coverFacet 6 376
cert_cover_5 6 3 2 3 4 5 88 376 2
cert_coverFacet 7 216
cert_cover_2 7 3 2 5 6 88 216 3
cert_coverFacet 8 624
cert_cover_2 8 4 3 5 8 112 624 3
cert_coverFacet 9 720
cert_cover_2 9 5 3 6 8 208 720 3
cert_coveringFacets_5
cert_coveringProof
cert_certificate 4 10
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0311

end
end BundlePart27

section BundlePart28
/- Source: ProjectionCertificates/R_m16e10q1_0312.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0312

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [419, 805, 617, 169, 457, 849, 158, 174, 342, 294, 722, 450, 572, 788, 664, 712, 41, 73, 137, 161, 289, 545, 321, 577, 385, 769, 142, 22, 38, 262, 82, 146, 162, 290, 194, 322, 386, 28, 44, 276, 532, 292, 548, 772, 152, 536, 168, 552, 200, 584, 648, 336, 592, 656, 784, 448, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_419, vertices_805, vertices_617, vertices_169, vertices_457, vertices_849, vertices_158, vertices_174, vertices_342, vertices_294, vertices_722, vertices_450, vertices_572, vertices_788, vertices_664, vertices_712] (by decide +kernel)
  polygons := literalFinset [vertices_41, vertices_73, vertices_137, vertices_161, vertices_289, vertices_545, vertices_321, vertices_577, vertices_385, vertices_769, vertices_142, vertices_22, vertices_38, vertices_262, vertices_82, vertices_146, vertices_162, vertices_290, vertices_194, vertices_322, vertices_386, vertices_28, vertices_44, vertices_276, vertices_532, vertices_292, vertices_548, vertices_772, vertices_152, vertices_536, vertices_168, vertices_552, vertices_200, vertices_584, vertices_648, vertices_336, vertices_592, vertices_656, vertices_784, vertices_448, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_419), (false, vertices_805), (false, vertices_617), (false, vertices_169), (false, vertices_457), (false, vertices_849), (true, vertices_142), (true, vertices_22), (true, vertices_38), (true, vertices_262), (true, vertices_82), (true, vertices_146), (true, vertices_194), (true, vertices_322), (true, vertices_28), (true, vertices_44), (true, vertices_276), (true, vertices_532), (true, vertices_152), (true, vertices_536), (true, vertices_648), (true, vertices_656), (true, vertices_704)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 17 20 22 25 27 28 29 30 31
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_419) then 18 else
  if p.val = (false, vertices_805) then 21 else
  if p.val = (false, vertices_617) then 23 else
  if p.val = (false, vertices_169) then 0 else
  if p.val = (false, vertices_457) then 24 else
  if p.val = (false, vertices_849) then 26 else
  if p.val = (true, vertices_142) then 19 else
  if p.val = (true, vertices_22) then 1 else
  if p.val = (true, vertices_38) then 2 else
  if p.val = (true, vertices_262) then 3 else
  if p.val = (true, vertices_82) then 4 else
  if p.val = (true, vertices_146) then 5 else
  if p.val = (true, vertices_194) then 6 else
  if p.val = (true, vertices_322) then 7 else
  if p.val = (true, vertices_28) then 8 else
  if p.val = (true, vertices_44) then 9 else
  if p.val = (true, vertices_276) then 10 else
  if p.val = (true, vertices_532) then 11 else
  if p.val = (true, vertices_152) then 12 else
  if p.val = (true, vertices_536) then 13 else
  if p.val = (true, vertices_648) then 14 else
  if p.val = (true, vertices_656) then 15 else
  if p.val = (true, vertices_704) then 16 else
  0
cert_priority
cert_nodeAtPriority_33 169 22 38 262 82 146 194 322 28 44 276 532 152 536 648 656 704 419 142 805 617 457 849
cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 3 5 7 342 22 3
cert_row_4 1 0 3 5 6 8 722 82 3
cert_row_2 2 0 1 2 6 142
cert_row_4 3 1 2 3 4 8 572 28 3
cert_rows
cert_pivot_2 7 5 0 1
cert_heightProof 4
cert_coverFacet 0 158
cert_cover_5 0 2 0 1 2 3 142 158 3
cert_coverFacet 1 174
cert_cover_5 1 2 0 1 2 4 142 174 3
cert_coverFacet 2 342
cert_cover_5 2 0 0 1 3 5 22 342 3
cert_coverFacet 3 294
cert_cover_2 3 1 0 4 7 38 294 3
cert_coverFacet 4 722
cert_cover_5 4 1 0 3 5 6 82 722 3
cert_coverFacet 5 450
cert_cover_2 5 5 0 6 7 194 450 3
cert_coverFacet 6 572
cert_cover_5 6 3 1 2 3 4 28 572 3
cert_coverFacet 7 788
cert_cover_2 7 3 1 7 8 276 788 3
cert_coverFacet 8 664
cert_cover_2 8 3 2 6 8 152 664 3
cert_coverFacet 9 712
cert_cover_2 9 5 2 6 8 200 712 3
cert_coveringFacets_5
cert_coveringProof
cert_certificate 4 10
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0312

end
end BundlePart28

section BundlePart29
/- Source: ProjectionCertificates/R_m16e10q1_0313.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0313

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [451, 557, 57, 601, 433, 337, 737, 398, 230, 614, 774, 850, 796, 172, 184, 408, 25, 41, 521, 49, 81, 273, 161, 545, 193, 321, 577, 385, 102, 134, 262, 518, 194, 322, 578, 386, 770, 44, 140, 268, 524, 164, 548, 772, 56, 152, 280, 536, 168, 392, 176, 336, 592, 400, 784, 224, 608]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_451, vertices_557, vertices_57, vertices_601, vertices_433, vertices_337, vertices_737, vertices_398, vertices_230, vertices_614, vertices_774, vertices_850, vertices_796, vertices_172, vertices_184, vertices_408] (by decide +kernel)
  polygons := literalFinset [vertices_25, vertices_41, vertices_521, vertices_49, vertices_81, vertices_273, vertices_161, vertices_545, vertices_193, vertices_321, vertices_577, vertices_385, vertices_102, vertices_134, vertices_262, vertices_518, vertices_194, vertices_322, vertices_578, vertices_386, vertices_770, vertices_44, vertices_140, vertices_268, vertices_524, vertices_164, vertices_548, vertices_772, vertices_56, vertices_152, vertices_280, vertices_536, vertices_168, vertices_392, vertices_176, vertices_336, vertices_592, vertices_400, vertices_784, vertices_224, vertices_608] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_451), (false, vertices_557), (false, vertices_57), (false, vertices_601), (false, vertices_433), (false, vertices_337), (false, vertices_737), (true, vertices_102), (true, vertices_134), (true, vertices_262), (true, vertices_518), (true, vertices_578), (true, vertices_770), (true, vertices_140), (true, vertices_268), (true, vertices_164), (true, vertices_772), (true, vertices_152), (true, vertices_280), (true, vertices_168), (true, vertices_392), (true, vertices_784)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 16 19 21 23 25 27 28 29 30
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_451) then 17 else
  if p.val = (false, vertices_557) then 20 else
  if p.val = (false, vertices_57) then 0 else
  if p.val = (false, vertices_601) then 22 else
  if p.val = (false, vertices_433) then 24 else
  if p.val = (false, vertices_337) then 1 else
  if p.val = (false, vertices_737) then 26 else
  if p.val = (true, vertices_102) then 18 else
  if p.val = (true, vertices_134) then 2 else
  if p.val = (true, vertices_262) then 3 else
  if p.val = (true, vertices_518) then 4 else
  if p.val = (true, vertices_578) then 5 else
  if p.val = (true, vertices_770) then 6 else
  if p.val = (true, vertices_140) then 7 else
  if p.val = (true, vertices_268) then 8 else
  if p.val = (true, vertices_164) then 9 else
  if p.val = (true, vertices_772) then 10 else
  if p.val = (true, vertices_152) then 11 else
  if p.val = (true, vertices_280) then 12 else
  if p.val = (true, vertices_168) then 13 else
  if p.val = (true, vertices_392) then 14 else
  if p.val = (true, vertices_784) then 15 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_57), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_337), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_134), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_262), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_518), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_578), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_770), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_140), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_268), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_164), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_772), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_152), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_280), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_168), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_392), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_784), by decide +kernel⟩
  | 16 => Sum.inl 0
  | 17 => Sum.inr ⟨(false, vertices_451), by decide +kernel⟩
  | 18 => Sum.inr ⟨(true, vertices_102), by decide +kernel⟩
  | 19 => Sum.inl 1
  | 20 => Sum.inr ⟨(false, vertices_557), by decide +kernel⟩
  | 21 => Sum.inl 2
  | 22 => Sum.inr ⟨(false, vertices_601), by decide +kernel⟩
  | 23 => Sum.inl 3
  | 24 => Sum.inr ⟨(false, vertices_433), by decide +kernel⟩
  | 25 => Sum.inl 4
  | 26 => Sum.inr ⟨(false, vertices_737), by decide +kernel⟩
  | 27 => Sum.inl 5
  | 28 => Sum.inl 6
  | 29 => Sum.inl 7
  | 30 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 1 4 5 102
cert_row_4 1 0 1 2 6 7 398 134 2
cert_row_4 2 0 3 5 7 8 850 322 1
cert_row_4 3 1 2 3 7 8 796 268 2
cert_rows
cert_pivot_2 4 6 0 1
cert_heightProof 4
cert_coverFacet 0 398
cert_cover_5 0 1 0 1 2 6 134 398 2
cert_coverFacet 1 230
cert_cover_5 1 0 0 1 4 6 102 230 3
cert_coverFacet 2 614
cert_cover_5 2 0 0 1 4 8 102 614 3
cert_coverFacet 3 774
cert_cover_2 3 1 0 7 8 262 774 3
cert_coverFacet 4 850
cert_cover_5 4 2 0 3 5 7 322 850 1
cert_coverFacet 5 796
cert_cover_5 5 3 1 2 3 7 268 796 2
cert_coverFacet 6 172
cert_cover_2 6 2 1 4 6 44 172 3
cert_coverFacet 7 184
cert_cover_2 7 3 2 4 6 56 184 3
cert_coverFacet 8 408
cert_cover_2 8 3 2 6 7 152 408 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0313

end
end BundlePart29

-- Public target certificates; internal witness data stays private.
namespace Nonrational.TerminalVerification
open Papers.RationalityTen.ChirotopeDensity.FiniteProjection
open Nonrational.TerminalData
set_option maxRecDepth 100000
set_option maxHeartbeats 0

public theorem projection_4173 : Certifies 4173 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0284.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_4174 : Certifies 4174 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0285.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_4175 : Certifies 4175 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0286.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_4176 : Certifies 4176 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0287.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_4177 : Certifies 4177 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0288.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_4178 : Certifies 4178 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0289.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_4179 : Certifies 4179 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0290.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_4180 : Certifies 4180 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0291.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_4181 : Certifies 4181 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0292.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_4182 : Certifies 4182 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0293.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_4183 : Certifies 4183 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0294.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_4184 : Certifies 4184 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0295.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_4185 : Certifies 4185 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0296.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_4186 : Certifies 4186 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0297.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_4187 : Certifies 4187 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0298.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_4188 : Certifies 4188 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0299.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_4189 : Certifies 4189 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0300.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_4190 : Certifies 4190 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0301.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_4191 : Certifies 4191 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0302.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_4192 : Certifies 4192 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0303.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_4193 : Certifies 4193 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0304.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_4194 : Certifies 4194 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0305.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_4195 : Certifies 4195 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0306.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_4196 : Certifies 4196 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0307.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_4197 : Certifies 4197 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0308.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_4198 : Certifies 4198 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0309.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_4199 : Certifies 4199 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0310.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_4200 : Certifies 4200 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0311.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_4201 : Certifies 4201 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0312.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_4202 : Certifies 4202 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0313.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem certified_B138 (j : Fin 30) :
    Certifies (4173 + j.val) := by
  fin_cases j
  · exact projection_4173
  · exact projection_4174
  · exact projection_4175
  · exact projection_4176
  · exact projection_4177
  · exact projection_4178
  · exact projection_4179
  · exact projection_4180
  · exact projection_4181
  · exact projection_4182
  · exact projection_4183
  · exact projection_4184
  · exact projection_4185
  · exact projection_4186
  · exact projection_4187
  · exact projection_4188
  · exact projection_4189
  · exact projection_4190
  · exact projection_4191
  · exact projection_4192
  · exact projection_4193
  · exact projection_4194
  · exact projection_4195
  · exact projection_4196
  · exact projection_4197
  · exact projection_4198
  · exact projection_4199
  · exact projection_4200
  · exact projection_4201
  · exact projection_4202

end Nonrational.TerminalVerification
-- Explicit facial frame witnesses, with lexical vector tracking.
