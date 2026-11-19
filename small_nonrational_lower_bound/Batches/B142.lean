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
/- Source: ProjectionCertificates/R_m16e10q1_0406.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0406

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [199, 587, 419, 771, 357, 165, 793, 329, 914, 706, 572, 620, 180, 724, 440, 360, 67, 131, 259, 515, 37, 69, 133, 73, 265, 521, 161, 289, 321, 769, 194, 578, 386, 642, 770, 556, 52, 148, 532, 100, 164, 196, 580, 56, 280, 536, 104, 296, 328, 584, 176, 400, 656, 784, 352, 416, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_199, vertices_587, vertices_419, vertices_771, vertices_357, vertices_165, vertices_793, vertices_329, vertices_914, vertices_706, vertices_572, vertices_620, vertices_180, vertices_724, vertices_440, vertices_360] (by decide +kernel)
  polygons := literalFinset [vertices_67, vertices_131, vertices_259, vertices_515, vertices_37, vertices_69, vertices_133, vertices_73, vertices_265, vertices_521, vertices_161, vertices_289, vertices_321, vertices_769, vertices_194, vertices_578, vertices_386, vertices_642, vertices_770, vertices_556, vertices_52, vertices_148, vertices_532, vertices_100, vertices_164, vertices_196, vertices_580, vertices_56, vertices_280, vertices_536, vertices_104, vertices_296, vertices_328, vertices_584, vertices_176, vertices_400, vertices_656, vertices_784, vertices_352, vertices_416, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_199), (false, vertices_587), (false, vertices_419), (false, vertices_771), (false, vertices_357), (false, vertices_165), (false, vertices_793), (false, vertices_329), (true, vertices_642), (true, vertices_556), (true, vertices_52), (true, vertices_148), (true, vertices_532), (true, vertices_580), (true, vertices_56), (true, vertices_104), (true, vertices_296), (true, vertices_176), (true, vertices_400), (true, vertices_656), (true, vertices_704)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 19 22 24 25 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_199) then 16 else
  if p.val = (false, vertices_587) then 17 else
  if p.val = (false, vertices_419) then 18 else
  if p.val = (false, vertices_771) then 0 else
  if p.val = (false, vertices_357) then 20 else
  if p.val = (false, vertices_165) then 1 else
  if p.val = (false, vertices_793) then 23 else
  if p.val = (false, vertices_329) then 2 else
  if p.val = (true, vertices_642) then 3 else
  if p.val = (true, vertices_556) then 21 else
  if p.val = (true, vertices_52) then 4 else
  if p.val = (true, vertices_148) then 5 else
  if p.val = (true, vertices_532) then 6 else
  if p.val = (true, vertices_580) then 7 else
  if p.val = (true, vertices_56) then 8 else
  if p.val = (true, vertices_104) then 9 else
  if p.val = (true, vertices_296) then 10 else
  if p.val = (true, vertices_176) then 11 else
  if p.val = (true, vertices_400) then 12 else
  if p.val = (true, vertices_656) then 13 else
  if p.val = (true, vertices_704) then 14 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_771), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_165), by decide +kernel⟩
  | 2 => Sum.inr ⟨(false, vertices_329), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_642), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_52), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_148), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_532), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_580), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_56), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_104), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_296), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_176), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_400), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_656), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_704), by decide +kernel⟩
  | 15 => Sum.inl 0
  | 16 => Sum.inr ⟨(false, vertices_199), by decide +kernel⟩
  | 17 => Sum.inr ⟨(false, vertices_587), by decide +kernel⟩
  | 18 => Sum.inr ⟨(false, vertices_419), by decide +kernel⟩
  | 19 => Sum.inl 1
  | 20 => Sum.inr ⟨(false, vertices_357), by decide +kernel⟩
  | 21 => Sum.inr ⟨(true, vertices_556), by decide +kernel⟩
  | 22 => Sum.inl 2
  | 23 => Sum.inr ⟨(false, vertices_793), by decide +kernel⟩
  | 24 => Sum.inl 3
  | 25 => Sum.inl 4
  | 26 => Sum.inl 5
  | 27 => Sum.inl 6
  | 28 => Sum.inl 7
  | 29 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 3 6 7 8 914 386 1
cert_row_4 1 1 3 5 6 8 724 148 2
cert_row_2 2 1 2 4 8 556
cert_row_4 3 2 3 4 6 7 440 56 3
cert_rows
cert_pivot_2 0 5 1 2
cert_heightProof 4
cert_coverFacet 0 914
cert_cover_5 0 0 0 3 6 7 386 914 1
cert_coverFacet 1 706
cert_cover_2 1 5 0 6 8 194 706 3
cert_coverFacet 2 572
cert_cover_5 2 2 1 2 3 4 556 572 2
cert_coverFacet 3 620
cert_cover_5 3 2 1 2 4 5 556 620 3
cert_coverFacet 4 180
cert_cover_2 4 3 1 4 6 52 180 3
cert_coverFacet 5 724
cert_cover_5 5 1 1 3 5 6 148 724 2
cert_coverFacet 6 440
cert_cover_5 6 3 2 3 4 6 56 440 3
cert_coverFacet 7 360
cert_cover_2 7 4 2 5 7 104 360 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0406

end
end BundlePart0

section BundlePart1
/- Source: ProjectionCertificates/R_m16e10q1_0407.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0407

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [51, 787, 419, 709, 601, 241, 897, 302, 58, 538, 842, 188, 220, 332, 932, 836, 19, 35, 259, 49, 81, 529, 161, 193, 577, 385, 641, 769, 26, 42, 266, 522, 50, 530, 290, 770, 156, 44, 76, 268, 164, 292, 196, 324, 580, 644, 772, 56, 88, 536, 328, 584, 176, 208, 416, 832, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_51, vertices_787, vertices_419, vertices_709, vertices_601, vertices_241, vertices_897, vertices_302, vertices_58, vertices_538, vertices_842, vertices_188, vertices_220, vertices_332, vertices_932, vertices_836] (by decide +kernel)
  polygons := literalFinset [vertices_19, vertices_35, vertices_259, vertices_49, vertices_81, vertices_529, vertices_161, vertices_193, vertices_577, vertices_385, vertices_641, vertices_769, vertices_26, vertices_42, vertices_266, vertices_522, vertices_50, vertices_530, vertices_290, vertices_770, vertices_156, vertices_44, vertices_76, vertices_268, vertices_164, vertices_292, vertices_196, vertices_324, vertices_580, vertices_644, vertices_772, vertices_56, vertices_88, vertices_536, vertices_328, vertices_584, vertices_176, vertices_208, vertices_416, vertices_832, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_51), (false, vertices_787), (false, vertices_419), (false, vertices_709), (false, vertices_601), (false, vertices_241), (false, vertices_897), (true, vertices_26), (true, vertices_42), (true, vertices_266), (true, vertices_522), (true, vertices_156), (true, vertices_44), (true, vertices_76), (true, vertices_268), (true, vertices_164), (true, vertices_292), (true, vertices_324), (true, vertices_772), (true, vertices_56), (true, vertices_328), (true, vertices_832)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 16 19 22 24 26 27 28 29 30
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_51) then 0 else
  if p.val = (false, vertices_787) then 17 else
  if p.val = (false, vertices_419) then 18 else
  if p.val = (false, vertices_709) then 20 else
  if p.val = (false, vertices_601) then 23 else
  if p.val = (false, vertices_241) then 25 else
  if p.val = (false, vertices_897) then 1 else
  if p.val = (true, vertices_26) then 2 else
  if p.val = (true, vertices_42) then 3 else
  if p.val = (true, vertices_266) then 4 else
  if p.val = (true, vertices_522) then 5 else
  if p.val = (true, vertices_156) then 21 else
  if p.val = (true, vertices_44) then 6 else
  if p.val = (true, vertices_76) then 7 else
  if p.val = (true, vertices_268) then 8 else
  if p.val = (true, vertices_164) then 9 else
  if p.val = (true, vertices_292) then 10 else
  if p.val = (true, vertices_324) then 11 else
  if p.val = (true, vertices_772) then 12 else
  if p.val = (true, vertices_56) then 13 else
  if p.val = (true, vertices_328) then 14 else
  if p.val = (true, vertices_832) then 15 else
  0
cert_priority
cert_nodeAtPriority_61 0 51 1 897 26 42 266 522 44 76 268 164 292 324 772 56 328 832 787 419 709 156 601 241
cert_priority_injective
cert_incidenceProof
cert_row_2 0 1 2 3 6 156
cert_row_4 1 0 2 5 7 8 842 266 2
cert_row_4 2 0 1 2 4 7 302 42 1
cert_row_4 3 1 4 6 7 8 932 164 3
cert_rows
cert_pivot_2 3 5 0 1
cert_heightProof 4
cert_coverFacet 0 302
cert_cover_5 0 2 0 1 2 4 42 302 1
cert_coverFacet 1 58
cert_cover_2 1 2 0 3 4 26 58 3
cert_coverFacet 2 538
cert_cover_2 2 2 0 3 8 26 538 3
cert_coverFacet 3 842
cert_cover_5 3 1 0 2 5 7 266 842 2
cert_coverFacet 4 188
cert_cover_5 4 0 1 2 3 4 156 188 3
cert_coverFacet 5 220
cert_cover_5 5 0 1 2 3 5 156 220 3
cert_coverFacet 6 332
cert_cover_2 6 2 1 5 7 76 332 3
cert_coverFacet 7 932
cert_cover_5 7 3 1 4 6 7 164 932 3
cert_coverFacet 8 836
cert_cover_2 8 5 1 7 8 324 836 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0407

end
end BundlePart1

section BundlePart2
/- Source: ProjectionCertificates/R_m16e10q1_0408.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0408

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [419, 565, 597, 229, 313, 217, 393, 678, 906, 306, 562, 850, 204, 844, 652, 344, 533, 37, 69, 25, 137, 265, 49, 81, 161, 289, 193, 385, 50, 274, 530, 162, 290, 546, 386, 642, 770, 76, 140, 524, 164, 548, 196, 580, 644, 88, 280, 200, 328, 392, 648, 776, 304, 560, 336, 592, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_419, vertices_565, vertices_597, vertices_229, vertices_313, vertices_217, vertices_393, vertices_678, vertices_906, vertices_306, vertices_562, vertices_850, vertices_204, vertices_844, vertices_652, vertices_344] (by decide +kernel)
  polygons := literalFinset [vertices_533, vertices_37, vertices_69, vertices_25, vertices_137, vertices_265, vertices_49, vertices_81, vertices_161, vertices_289, vertices_193, vertices_385, vertices_50, vertices_274, vertices_530, vertices_162, vertices_290, vertices_546, vertices_386, vertices_642, vertices_770, vertices_76, vertices_140, vertices_524, vertices_164, vertices_548, vertices_196, vertices_580, vertices_644, vertices_88, vertices_280, vertices_200, vertices_328, vertices_392, vertices_648, vertices_776, vertices_304, vertices_560, vertices_336, vertices_592, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_419), (false, vertices_565), (false, vertices_597), (false, vertices_229), (false, vertices_313), (false, vertices_217), (false, vertices_393), (true, vertices_50), (true, vertices_274), (true, vertices_530), (true, vertices_546), (true, vertices_642), (true, vertices_770), (true, vertices_76), (true, vertices_140), (true, vertices_524), (true, vertices_644), (true, vertices_328), (true, vertices_648), (true, vertices_776), (true, vertices_336), (true, vertices_832)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 16 18 22 25 26 27 28 29 30
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_419) then 17 else
  if p.val = (false, vertices_565) then 19 else
  if p.val = (false, vertices_597) then 20 else
  if p.val = (false, vertices_229) then 21 else
  if p.val = (false, vertices_313) then 23 else
  if p.val = (false, vertices_217) then 24 else
  if p.val = (false, vertices_393) then 0 else
  if p.val = (true, vertices_50) then 1 else
  if p.val = (true, vertices_274) then 2 else
  if p.val = (true, vertices_530) then 3 else
  if p.val = (true, vertices_546) then 4 else
  if p.val = (true, vertices_642) then 5 else
  if p.val = (true, vertices_770) then 6 else
  if p.val = (true, vertices_76) then 7 else
  if p.val = (true, vertices_140) then 8 else
  if p.val = (true, vertices_524) then 9 else
  if p.val = (true, vertices_644) then 10 else
  if p.val = (true, vertices_328) then 11 else
  if p.val = (true, vertices_648) then 12 else
  if p.val = (true, vertices_776) then 13 else
  if p.val = (true, vertices_336) then 14 else
  if p.val = (true, vertices_832) then 15 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_393), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_50), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_274), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_530), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_546), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_642), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_770), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_76), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_140), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_524), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_644), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_328), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_648), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_776), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_336), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_832), by decide +kernel⟩
  | 16 => Sum.inl 0
  | 17 => Sum.inr ⟨(false, vertices_419), by decide +kernel⟩
  | 18 => Sum.inl 1
  | 19 => Sum.inr ⟨(false, vertices_565), by decide +kernel⟩
  | 20 => Sum.inr ⟨(false, vertices_597), by decide +kernel⟩
  | 21 => Sum.inr ⟨(false, vertices_229), by decide +kernel⟩
  | 22 => Sum.inl 2
  | 23 => Sum.inr ⟨(false, vertices_313), by decide +kernel⟩
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
cert_row_4 0 0 1 4 6 8 678 162 1
cert_row_4 1 0 2 6 7 8 906 386 1
cert_row_4 2 0 3 5 7 8 850 274 2
cert_row_4 3 1 2 5 7 8 844 76 3
cert_rows
cert_pivot_2 4 6 0 1
cert_heightProof 4
cert_coverFacet 0 678
cert_cover_5 0 0 0 1 4 6 162 678 1
cert_coverFacet 1 906
cert_cover_5 1 1 0 2 6 7 386 906 1
cert_coverFacet 2 306
cert_cover_2 2 3 0 4 7 50 306 3
cert_coverFacet 3 562
cert_cover_2 3 3 0 4 8 50 562 3
cert_coverFacet 4 850
cert_cover_5 4 2 0 3 5 7 274 850 2
cert_coverFacet 5 204
cert_cover_2 5 2 1 5 6 76 204 3
cert_coverFacet 6 844
cert_cover_5 6 3 1 2 5 7 76 844 3
cert_coverFacet 7 652
cert_cover_2 7 2 1 6 8 140 652 3
cert_coverFacet 8 344
cert_cover_2 8 3 2 5 7 88 344 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0408

end
end BundlePart2

section BundlePart3
/- Source: ProjectionCertificates/R_m16e10q1_0409.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0409

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [779, 51, 595, 419, 709, 241, 897, 302, 58, 538, 188, 220, 332, 932, 836, 856, 19, 35, 259, 515, 49, 81, 161, 193, 577, 385, 641, 769, 26, 42, 266, 522, 50, 530, 290, 156, 44, 76, 268, 164, 292, 196, 324, 580, 644, 772, 56, 88, 536, 328, 776, 176, 208, 592, 416, 832, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_779, vertices_51, vertices_595, vertices_419, vertices_709, vertices_241, vertices_897, vertices_302, vertices_58, vertices_538, vertices_188, vertices_220, vertices_332, vertices_932, vertices_836, vertices_856] (by decide +kernel)
  polygons := literalFinset [vertices_19, vertices_35, vertices_259, vertices_515, vertices_49, vertices_81, vertices_161, vertices_193, vertices_577, vertices_385, vertices_641, vertices_769, vertices_26, vertices_42, vertices_266, vertices_522, vertices_50, vertices_530, vertices_290, vertices_156, vertices_44, vertices_76, vertices_268, vertices_164, vertices_292, vertices_196, vertices_324, vertices_580, vertices_644, vertices_772, vertices_56, vertices_88, vertices_536, vertices_328, vertices_776, vertices_176, vertices_208, vertices_592, vertices_416, vertices_832, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_779), (false, vertices_51), (false, vertices_595), (false, vertices_419), (false, vertices_709), (false, vertices_241), (false, vertices_897), (true, vertices_26), (true, vertices_42), (true, vertices_156), (true, vertices_44), (true, vertices_76), (true, vertices_268), (true, vertices_164), (true, vertices_292), (true, vertices_324), (true, vertices_772), (true, vertices_56), (true, vertices_88), (true, vertices_536), (true, vertices_328), (true, vertices_832)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 16 20 23 24 26 27 28 29 30
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_779) then 17 else
  if p.val = (false, vertices_51) then 0 else
  if p.val = (false, vertices_595) then 18 else
  if p.val = (false, vertices_419) then 19 else
  if p.val = (false, vertices_709) then 21 else
  if p.val = (false, vertices_241) then 25 else
  if p.val = (false, vertices_897) then 1 else
  if p.val = (true, vertices_26) then 2 else
  if p.val = (true, vertices_42) then 3 else
  if p.val = (true, vertices_156) then 22 else
  if p.val = (true, vertices_44) then 4 else
  if p.val = (true, vertices_76) then 5 else
  if p.val = (true, vertices_268) then 6 else
  if p.val = (true, vertices_164) then 7 else
  if p.val = (true, vertices_292) then 8 else
  if p.val = (true, vertices_324) then 9 else
  if p.val = (true, vertices_772) then 10 else
  if p.val = (true, vertices_56) then 11 else
  if p.val = (true, vertices_88) then 12 else
  if p.val = (true, vertices_536) then 13 else
  if p.val = (true, vertices_328) then 14 else
  if p.val = (true, vertices_832) then 15 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_51), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_897), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_26), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_42), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_44), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_76), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_268), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_164), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_292), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_324), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_772), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_56), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_88), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_536), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_328), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_832), by decide +kernel⟩
  | 16 => Sum.inl 0
  | 17 => Sum.inr ⟨(false, vertices_779), by decide +kernel⟩
  | 18 => Sum.inr ⟨(false, vertices_595), by decide +kernel⟩
  | 19 => Sum.inr ⟨(false, vertices_419), by decide +kernel⟩
  | 20 => Sum.inl 1
  | 21 => Sum.inr ⟨(false, vertices_709), by decide +kernel⟩
  | 22 => Sum.inr ⟨(true, vertices_156), by decide +kernel⟩
  | 23 => Sum.inl 2
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
cert_row_4 0 0 1 2 4 7 302 42 1
cert_row_4 1 1 4 6 7 8 932 164 3
cert_row_2 2 1 2 3 6 156
cert_row_4 3 2 3 5 7 8 856 88 3
cert_rows
cert_pivot_2 0 4 1 2
cert_heightProof 4
cert_coverFacet 0 302
cert_cover_5 0 0 0 1 2 4 42 302 1
cert_coverFacet 1 58
cert_cover_2 1 2 0 3 4 26 58 3
cert_coverFacet 2 538
cert_cover_2 2 2 0 3 8 26 538 3
cert_coverFacet 3 188
cert_cover_5 3 2 1 2 3 4 156 188 3
cert_coverFacet 4 220
cert_cover_5 4 2 1 2 3 5 156 220 3
cert_coverFacet 5 332
cert_cover_2 5 2 1 5 7 76 332 3
cert_coverFacet 6 932
cert_cover_5 6 1 1 4 6 7 164 932 3
cert_coverFacet 7 836
cert_cover_2 7 5 1 7 8 324 836 3
cert_coverFacet 8 856
cert_cover_5 8 3 2 3 5 7 88 856 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0409

end
end BundlePart3

section BundlePart4
/- Source: ProjectionCertificates/R_m16e10q1_0410.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0410

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [779, 659, 387, 541, 57, 425, 241, 710, 226, 866, 418, 316, 844, 372, 212, 660, 131, 259, 515, 25, 41, 265, 521, 49, 145, 529, 161, 385, 98, 162, 290, 194, 578, 386, 642, 770, 28, 268, 524, 308, 84, 148, 532, 196, 324, 580, 644, 56, 296, 776, 112, 208, 656, 224, 352, 416, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_779, vertices_659, vertices_387, vertices_541, vertices_57, vertices_425, vertices_241, vertices_710, vertices_226, vertices_866, vertices_418, vertices_316, vertices_844, vertices_372, vertices_212, vertices_660] (by decide +kernel)
  polygons := literalFinset [vertices_131, vertices_259, vertices_515, vertices_25, vertices_41, vertices_265, vertices_521, vertices_49, vertices_145, vertices_529, vertices_161, vertices_385, vertices_98, vertices_162, vertices_290, vertices_194, vertices_578, vertices_386, vertices_642, vertices_770, vertices_28, vertices_268, vertices_524, vertices_308, vertices_84, vertices_148, vertices_532, vertices_196, vertices_324, vertices_580, vertices_644, vertices_56, vertices_296, vertices_776, vertices_112, vertices_208, vertices_656, vertices_224, vertices_352, vertices_416, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_779), (false, vertices_659), (false, vertices_387), (false, vertices_541), (false, vertices_57), (false, vertices_425), (false, vertices_241), (true, vertices_98), (true, vertices_162), (true, vertices_290), (true, vertices_194), (true, vertices_578), (true, vertices_268), (true, vertices_308), (true, vertices_84), (true, vertices_148), (true, vertices_196), (true, vertices_324), (true, vertices_580), (true, vertices_644), (true, vertices_352), (true, vertices_832)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 16 19 22 24 26 27 28 29 30
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_779) then 17 else
  if p.val = (false, vertices_659) then 18 else
  if p.val = (false, vertices_387) then 0 else
  if p.val = (false, vertices_541) then 20 else
  if p.val = (false, vertices_57) then 1 else
  if p.val = (false, vertices_425) then 23 else
  if p.val = (false, vertices_241) then 25 else
  if p.val = (true, vertices_98) then 2 else
  if p.val = (true, vertices_162) then 3 else
  if p.val = (true, vertices_290) then 4 else
  if p.val = (true, vertices_194) then 5 else
  if p.val = (true, vertices_578) then 6 else
  if p.val = (true, vertices_268) then 7 else
  if p.val = (true, vertices_308) then 21 else
  if p.val = (true, vertices_84) then 8 else
  if p.val = (true, vertices_148) then 9 else
  if p.val = (true, vertices_196) then 10 else
  if p.val = (true, vertices_324) then 11 else
  if p.val = (true, vertices_580) then 12 else
  if p.val = (true, vertices_644) then 13 else
  if p.val = (true, vertices_352) then 14 else
  if p.val = (true, vertices_832) then 15 else
  0
cert_priority
cert_nodeAtPriority_61 0 387 1 57 98 162 290 194 578 268 84 148 196 324 580 644 352 832 779 659 541 308 425 241
cert_priority_injective
cert_incidenceProof
cert_row_2 0 1 3 4 7 308
cert_row_4 1 0 1 5 6 8 710 194 1
cert_row_4 2 0 4 5 7 8 866 98 3
cert_row_4 3 1 2 5 7 8 844 268 2
cert_rows
cert_pivot_2 3 6 0 1
cert_heightProof 4
cert_coverFacet 0 710
cert_cover_5 0 1 0 1 5 6 194 710 1
cert_coverFacet 1 226
cert_cover_2 1 4 0 5 6 98 226 3
cert_coverFacet 2 866
cert_cover_5 2 2 0 4 5 7 98 866 3
cert_coverFacet 3 418
cert_cover_2 3 4 0 6 7 162 418 3
cert_coverFacet 4 316
cert_cover_5 4 0 1 2 3 4 28 316 3
cert_coverFacet 5 844
cert_cover_5 5 3 1 2 5 7 268 844 2
cert_coverFacet 6 372
cert_cover_5 6 0 1 3 4 5 308 372 3
cert_coverFacet 7 212
cert_cover_2 7 3 1 5 6 84 212 3
cert_coverFacet 8 660
cert_cover_2 8 3 1 6 8 148 660 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0410

end
end BundlePart4

section BundlePart5
/- Source: ProjectionCertificates/R_m16e10q1_0411.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0411

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [659, 597, 325, 901, 89, 409, 361, 678, 314, 570, 402, 482, 620, 228, 452, 600, 69, 261, 517, 25, 73, 265, 81, 145, 529, 321, 385, 641, 58, 146, 274, 530, 162, 290, 546, 386, 642, 100, 164, 548, 196, 324, 580, 388, 644, 88, 280, 536, 104, 296, 552, 584, 592, 400, 224, 352, 448]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_659, vertices_597, vertices_325, vertices_901, vertices_89, vertices_409, vertices_361, vertices_678, vertices_314, vertices_570, vertices_402, vertices_482, vertices_620, vertices_228, vertices_452, vertices_600] (by decide +kernel)
  polygons := literalFinset [vertices_69, vertices_261, vertices_517, vertices_25, vertices_73, vertices_265, vertices_81, vertices_145, vertices_529, vertices_321, vertices_385, vertices_641, vertices_58, vertices_146, vertices_274, vertices_530, vertices_162, vertices_290, vertices_546, vertices_386, vertices_642, vertices_100, vertices_164, vertices_548, vertices_196, vertices_324, vertices_580, vertices_388, vertices_644, vertices_88, vertices_280, vertices_536, vertices_104, vertices_296, vertices_552, vertices_584, vertices_592, vertices_400, vertices_224, vertices_352, vertices_448] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_659), (false, vertices_597), (false, vertices_325), (false, vertices_901), (false, vertices_89), (false, vertices_409), (false, vertices_361), (true, vertices_58), (true, vertices_274), (true, vertices_162), (true, vertices_290), (true, vertices_546), (true, vertices_386), (true, vertices_100), (true, vertices_164), (true, vertices_548), (true, vertices_196), (true, vertices_536), (true, vertices_552), (true, vertices_584), (true, vertices_224), (true, vertices_448)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 16 19 22 25 26 27 28 29 30
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_659) then 17 else
  if p.val = (false, vertices_597) then 20 else
  if p.val = (false, vertices_325) then 0 else
  if p.val = (false, vertices_901) then 21 else
  if p.val = (false, vertices_89) then 1 else
  if p.val = (false, vertices_409) then 23 else
  if p.val = (false, vertices_361) then 24 else
  if p.val = (true, vertices_58) then 18 else
  if p.val = (true, vertices_274) then 2 else
  if p.val = (true, vertices_162) then 3 else
  if p.val = (true, vertices_290) then 4 else
  if p.val = (true, vertices_546) then 5 else
  if p.val = (true, vertices_386) then 6 else
  if p.val = (true, vertices_100) then 7 else
  if p.val = (true, vertices_164) then 8 else
  if p.val = (true, vertices_548) then 9 else
  if p.val = (true, vertices_196) then 10 else
  if p.val = (true, vertices_536) then 11 else
  if p.val = (true, vertices_552) then 12 else
  if p.val = (true, vertices_584) then 13 else
  if p.val = (true, vertices_224) then 14 else
  if p.val = (true, vertices_448) then 15 else
  0
cert_priority
cert_nodeAtPriority_39 0 325 1 89 274 162 290 546 386 100 164 548 196 536 552 584 224 448 659 58 597 901 409 361
cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 2 3 4 58
cert_row_4 1 0 4 5 6 7 482 162 2
cert_row_4 2 0 1 4 6 8 678 162 1
cert_row_4 3 1 2 4 5 8 620 100 1
cert_rows
cert_pivot_2 3 7 0 1
cert_heightProof 4
cert_coverFacet 0 678
cert_cover_5 0 2 0 1 4 6 162 678 1
cert_coverFacet 1 314
cert_cover_5 1 0 0 2 3 7 58 314 3
cert_coverFacet 2 570
cert_cover_5 2 0 0 2 3 8 58 570 3
cert_coverFacet 3 402
cert_cover_2 3 3 0 6 7 146 402 3
cert_coverFacet 4 482
cert_cover_5 4 1 0 4 5 6 162 482 2
cert_coverFacet 5 620
cert_cover_5 5 3 1 2 4 5 100 620 1
cert_coverFacet 6 228
cert_cover_2 6 4 1 5 6 100 228 3
cert_coverFacet 7 452
cert_cover_2 7 5 1 6 7 196 452 3
cert_coverFacet 8 600
cert_cover_2 8 3 2 5 8 88 600 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0411

end
end BundlePart5

section BundlePart6
/- Source: ProjectionCertificates/R_m16e10q1_0412.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0412

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [835, 61, 217, 809, 457, 625, 782, 406, 646, 738, 450, 284, 556, 244, 676, 408, 25, 41, 201, 265, 49, 81, 545, 321, 577, 769, 134, 262, 518, 194, 322, 578, 386, 642, 770, 28, 44, 268, 524, 52, 148, 276, 164, 548, 644, 152, 280, 552, 392, 776, 112, 208, 400, 224, 608, 672, 448]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_835, vertices_61, vertices_217, vertices_809, vertices_457, vertices_625, vertices_782, vertices_406, vertices_646, vertices_738, vertices_450, vertices_284, vertices_556, vertices_244, vertices_676, vertices_408] (by decide +kernel)
  polygons := literalFinset [vertices_25, vertices_41, vertices_201, vertices_265, vertices_49, vertices_81, vertices_545, vertices_321, vertices_577, vertices_769, vertices_134, vertices_262, vertices_518, vertices_194, vertices_322, vertices_578, vertices_386, vertices_642, vertices_770, vertices_28, vertices_44, vertices_268, vertices_524, vertices_52, vertices_148, vertices_276, vertices_164, vertices_548, vertices_644, vertices_152, vertices_280, vertices_552, vertices_392, vertices_776, vertices_112, vertices_208, vertices_400, vertices_224, vertices_608, vertices_672, vertices_448] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_835), (false, vertices_61), (false, vertices_217), (false, vertices_809), (false, vertices_457), (false, vertices_625), (true, vertices_134), (true, vertices_262), (true, vertices_518), (true, vertices_194), (true, vertices_386), (true, vertices_642), (true, vertices_268), (true, vertices_524), (true, vertices_148), (true, vertices_276), (true, vertices_164), (true, vertices_548), (true, vertices_644), (true, vertices_280), (true, vertices_400), (true, vertices_224), (true, vertices_672)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 17 19 21 25 27 28 29 30 31
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_835) then 18 else
  if p.val = (false, vertices_61) then 20 else
  if p.val = (false, vertices_217) then 22 else
  if p.val = (false, vertices_809) then 23 else
  if p.val = (false, vertices_457) then 24 else
  if p.val = (false, vertices_625) then 26 else
  if p.val = (true, vertices_134) then 0 else
  if p.val = (true, vertices_262) then 1 else
  if p.val = (true, vertices_518) then 2 else
  if p.val = (true, vertices_194) then 3 else
  if p.val = (true, vertices_386) then 4 else
  if p.val = (true, vertices_642) then 5 else
  if p.val = (true, vertices_268) then 6 else
  if p.val = (true, vertices_524) then 7 else
  if p.val = (true, vertices_148) then 8 else
  if p.val = (true, vertices_276) then 9 else
  if p.val = (true, vertices_164) then 10 else
  if p.val = (true, vertices_548) then 11 else
  if p.val = (true, vertices_644) then 12 else
  if p.val = (true, vertices_280) then 13 else
  if p.val = (true, vertices_400) then 14 else
  if p.val = (true, vertices_224) then 15 else
  if p.val = (true, vertices_672) then 16 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_134), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_262), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_518), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_194), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_386), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_642), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_268), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_524), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_148), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_276), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_164), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_548), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_644), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_280), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_400), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_224), by decide +kernel⟩
  | 16 => Sum.inr ⟨(true, vertices_672), by decide +kernel⟩
  | 17 => Sum.inl 0
  | 18 => Sum.inr ⟨(false, vertices_835), by decide +kernel⟩
  | 19 => Sum.inl 1
  | 20 => Sum.inr ⟨(false, vertices_61), by decide +kernel⟩
  | 21 => Sum.inl 2
  | 22 => Sum.inr ⟨(false, vertices_217), by decide +kernel⟩
  | 23 => Sum.inr ⟨(false, vertices_809), by decide +kernel⟩
  | 24 => Sum.inr ⟨(false, vertices_457), by decide +kernel⟩
  | 25 => Sum.inl 3
  | 26 => Sum.inr ⟨(false, vertices_625), by decide +kernel⟩
  | 27 => Sum.inl 4
  | 28 => Sum.inl 5
  | 29 => Sum.inl 6
  | 30 => Sum.inl 7
  | 31 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 2 7 8 782 262 2
cert_row_4 1 0 1 3 6 7 406 134 2
cert_row_4 2 0 4 5 6 8 738 194 1
cert_row_4 3 1 3 4 5 6 244 52 3
cert_rows
cert_pivot_2 2 7 0 1
cert_heightProof 4
cert_coverFacet 0 782
cert_cover_5 0 0 0 1 2 7 262 782 2
cert_coverFacet 1 406
cert_cover_5 1 1 0 1 3 6 134 406 2
cert_coverFacet 2 646
cert_cover_2 2 1 0 6 8 134 646 3
cert_coverFacet 3 738
cert_cover_5 3 2 0 4 5 6 194 738 1
cert_coverFacet 4 450
cert_cover_2 4 5 0 6 7 194 450 3
cert_coverFacet 5 284
cert_cover_2 5 2 1 3 7 28 284 3
cert_coverFacet 6 556
cert_cover_2 6 2 1 4 8 44 556 3
cert_coverFacet 7 244
cert_cover_5 7 3 1 3 4 5 52 244 3
cert_coverFacet 8 676
cert_cover_2 8 4 1 6 8 164 676 3
cert_coverFacet 9 408
cert_cover_2 9 3 2 6 7 152 408 3
cert_coveringFacets_5
cert_coveringProof
cert_certificate 4 10
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0412

end
end BundlePart6

section BundlePart7
/- Source: ProjectionCertificates/R_m16e10q1_0413.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0413

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [295, 157, 285, 677, 809, 713, 278, 534, 550, 362, 626, 466, 724, 408, 616, 456, 29, 37, 133, 261, 137, 265, 521, 289, 545, 641, 22, 38, 262, 518, 82, 274, 530, 98, 290, 546, 322, 148, 276, 532, 548, 644, 152, 280, 104, 296, 552, 200, 328, 584, 392, 208, 592, 400, 608, 448, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_295, vertices_157, vertices_285, vertices_677, vertices_809, vertices_713, vertices_278, vertices_534, vertices_550, vertices_362, vertices_626, vertices_466, vertices_724, vertices_408, vertices_616, vertices_456] (by decide +kernel)
  polygons := literalFinset [vertices_29, vertices_37, vertices_133, vertices_261, vertices_137, vertices_265, vertices_521, vertices_289, vertices_545, vertices_641, vertices_22, vertices_38, vertices_262, vertices_518, vertices_82, vertices_274, vertices_530, vertices_98, vertices_290, vertices_546, vertices_322, vertices_148, vertices_276, vertices_532, vertices_548, vertices_644, vertices_152, vertices_280, vertices_104, vertices_296, vertices_552, vertices_200, vertices_328, vertices_584, vertices_392, vertices_208, vertices_592, vertices_400, vertices_608, vertices_448, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_295), (false, vertices_157), (false, vertices_285), (false, vertices_677), (false, vertices_809), (false, vertices_713), (true, vertices_22), (true, vertices_518), (true, vertices_82), (true, vertices_274), (true, vertices_530), (true, vertices_98), (true, vertices_546), (true, vertices_322), (true, vertices_532), (true, vertices_104), (true, vertices_328), (true, vertices_392), (true, vertices_208), (true, vertices_592), (true, vertices_400), (true, vertices_608), (true, vertices_448)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 17 19 23 26 27 28 29 30 31
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_295) then 18 else
  if p.val = (false, vertices_157) then 20 else
  if p.val = (false, vertices_285) then 21 else
  if p.val = (false, vertices_677) then 22 else
  if p.val = (false, vertices_809) then 24 else
  if p.val = (false, vertices_713) then 25 else
  if p.val = (true, vertices_22) then 0 else
  if p.val = (true, vertices_518) then 1 else
  if p.val = (true, vertices_82) then 2 else
  if p.val = (true, vertices_274) then 3 else
  if p.val = (true, vertices_530) then 4 else
  if p.val = (true, vertices_98) then 5 else
  if p.val = (true, vertices_546) then 6 else
  if p.val = (true, vertices_322) then 7 else
  if p.val = (true, vertices_532) then 8 else
  if p.val = (true, vertices_104) then 9 else
  if p.val = (true, vertices_328) then 10 else
  if p.val = (true, vertices_392) then 11 else
  if p.val = (true, vertices_208) then 12 else
  if p.val = (true, vertices_592) then 13 else
  if p.val = (true, vertices_400) then 14 else
  if p.val = (true, vertices_608) then 15 else
  if p.val = (true, vertices_448) then 16 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_22), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_518), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_82), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_274), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_530), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_98), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_546), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_322), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_532), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_104), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_328), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_392), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_208), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_592), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_400), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_608), by decide +kernel⟩
  | 16 => Sum.inr ⟨(true, vertices_448), by decide +kernel⟩
  | 17 => Sum.inl 0
  | 18 => Sum.inr ⟨(false, vertices_295), by decide +kernel⟩
  | 19 => Sum.inl 1
  | 20 => Sum.inr ⟨(false, vertices_157), by decide +kernel⟩
  | 21 => Sum.inr ⟨(false, vertices_285), by decide +kernel⟩
  | 22 => Sum.inr ⟨(false, vertices_677), by decide +kernel⟩
  | 23 => Sum.inl 2
  | 24 => Sum.inr ⟨(false, vertices_809), by decide +kernel⟩
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
cert_row_4 0 0 2 4 5 7 362 98 1
cert_row_4 1 0 3 4 5 8 626 82 2
cert_row_4 2 0 3 5 6 7 466 82 3
cert_row_4 3 1 3 5 6 8 724 148 2
cert_rows
cert_pivot_2 2 4 0 1
cert_heightProof 4
cert_coverFacet 0 278
cert_cover_2 0 1 0 3 7 22 278 3
cert_coverFacet 1 534
cert_cover_2 1 1 0 3 8 22 534 3
cert_coverFacet 2 550
cert_cover_2 2 1 0 4 8 38 550 3
cert_coverFacet 3 362
cert_cover_5 3 0 0 2 4 5 98 362 1
cert_coverFacet 4 626
cert_cover_5 4 1 0 3 4 5 82 626 2
cert_coverFacet 5 466
cert_cover_5 5 2 0 3 5 6 82 466 3
cert_coverFacet 6 724
cert_cover_5 6 3 1 3 5 6 148 724 2
cert_coverFacet 7 408
cert_cover_2 7 3 2 6 7 152 408 3
cert_coverFacet 8 616
cert_cover_2 8 4 2 5 8 104 616 3
cert_coverFacet 9 456
cert_cover_2 9 5 2 6 7 200 456 3
cert_coveringFacets_5
cert_coveringProof
cert_certificate 4 10
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0413

end
end BundlePart7

section BundlePart8
/- Source: ProjectionCertificates/R_m16e10q1_0414.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0414

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [899, 117, 789, 677, 313, 425, 838, 682, 202, 586, 466, 620, 340, 120, 216, 408, 21, 37, 517, 297, 49, 273, 161, 385, 641, 769, 74, 138, 522, 194, 322, 578, 386, 642, 770, 84, 276, 100, 548, 324, 580, 772, 56, 88, 152, 280, 104, 168, 552, 200, 584, 392, 112, 208, 336, 400, 672]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_899, vertices_117, vertices_789, vertices_677, vertices_313, vertices_425, vertices_838, vertices_682, vertices_202, vertices_586, vertices_466, vertices_620, vertices_340, vertices_120, vertices_216, vertices_408] (by decide +kernel)
  polygons := literalFinset [vertices_21, vertices_37, vertices_517, vertices_297, vertices_49, vertices_273, vertices_161, vertices_385, vertices_641, vertices_769, vertices_74, vertices_138, vertices_522, vertices_194, vertices_322, vertices_578, vertices_386, vertices_642, vertices_770, vertices_84, vertices_276, vertices_100, vertices_548, vertices_324, vertices_580, vertices_772, vertices_56, vertices_88, vertices_152, vertices_280, vertices_104, vertices_168, vertices_552, vertices_200, vertices_584, vertices_392, vertices_112, vertices_208, vertices_336, vertices_400, vertices_672] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_899), (false, vertices_117), (false, vertices_789), (false, vertices_677), (false, vertices_313), (false, vertices_425), (true, vertices_74), (true, vertices_138), (true, vertices_522), (true, vertices_194), (true, vertices_322), (true, vertices_578), (true, vertices_324), (true, vertices_580), (true, vertices_88), (true, vertices_152), (true, vertices_104), (true, vertices_552), (true, vertices_200), (true, vertices_584), (true, vertices_208), (true, vertices_336), (true, vertices_400)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 17 19 23 26 27 28 29 30 31
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_899) then 18 else
  if p.val = (false, vertices_117) then 20 else
  if p.val = (false, vertices_789) then 21 else
  if p.val = (false, vertices_677) then 22 else
  if p.val = (false, vertices_313) then 24 else
  if p.val = (false, vertices_425) then 25 else
  if p.val = (true, vertices_74) then 0 else
  if p.val = (true, vertices_138) then 1 else
  if p.val = (true, vertices_522) then 2 else
  if p.val = (true, vertices_194) then 3 else
  if p.val = (true, vertices_322) then 4 else
  if p.val = (true, vertices_578) then 5 else
  if p.val = (true, vertices_324) then 6 else
  if p.val = (true, vertices_580) then 7 else
  if p.val = (true, vertices_88) then 8 else
  if p.val = (true, vertices_152) then 9 else
  if p.val = (true, vertices_104) then 10 else
  if p.val = (true, vertices_552) then 11 else
  if p.val = (true, vertices_200) then 12 else
  if p.val = (true, vertices_584) then 13 else
  if p.val = (true, vertices_208) then 14 else
  if p.val = (true, vertices_336) then 15 else
  if p.val = (true, vertices_400) then 16 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_74), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_138), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_522), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_194), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_322), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_578), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_324), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_580), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_88), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_152), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_104), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_552), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_200), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_584), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_208), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_336), by decide +kernel⟩
  | 16 => Sum.inr ⟨(true, vertices_400), by decide +kernel⟩
  | 17 => Sum.inl 0
  | 18 => Sum.inr ⟨(false, vertices_899), by decide +kernel⟩
  | 19 => Sum.inl 1
  | 20 => Sum.inr ⟨(false, vertices_117), by decide +kernel⟩
  | 21 => Sum.inr ⟨(false, vertices_789), by decide +kernel⟩
  | 22 => Sum.inr ⟨(false, vertices_677), by decide +kernel⟩
  | 23 => Sum.inl 2
  | 24 => Sum.inr ⟨(false, vertices_313), by decide +kernel⟩
  | 25 => Sum.inr ⟨(false, vertices_425), by decide +kernel⟩
  | 26 => Sum.inl 3
  | 27 => Sum.inl 4
  | 28 => Sum.inl 5
  | 29 => Sum.inl 6
  | 30 => Sum.inl 7
  | 31 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 3 5 6 7 466 194 1
cert_row_4 1 0 1 5 7 8 838 322 1
cert_row_4 2 0 2 4 6 8 682 138 2
cert_row_4 3 1 2 4 5 8 620 100 1
cert_rows
cert_pivot_2 3 7 0 1
cert_heightProof 4
cert_coverFacet 0 838
cert_cover_5 0 1 0 1 5 7 322 838 1
cert_coverFacet 1 682
cert_cover_5 1 2 0 2 4 6 138 682 2
cert_coverFacet 2 202
cert_cover_2 2 2 0 5 6 74 202 3
cert_coverFacet 3 586
cert_cover_2 3 2 0 5 8 74 586 3
cert_coverFacet 4 466
cert_cover_5 4 0 0 3 5 6 194 466 1
cert_coverFacet 5 620
cert_cover_5 5 3 1 2 4 5 100 620 1
cert_coverFacet 6 340
cert_cover_2 6 3 1 5 7 84 340 3
cert_coverFacet 7 120
cert_cover_2 7 3 2 4 5 56 120 3
cert_coverFacet 8 216
cert_cover_2 8 3 2 5 6 88 216 3
cert_coverFacet 9 408
cert_cover_2 9 3 2 6 7 152 408 3
cert_coveringFacets_5
cert_coveringProof
cert_certificate 4 10
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0414

end
end BundlePart8

section BundlePart9
/- Source: ProjectionCertificates/R_m16e10q1_0415.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0415

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [419, 597, 217, 409, 817, 737, 334, 526, 310, 550, 682, 394, 716, 564, 340, 344, 153, 81, 273, 529, 161, 289, 545, 193, 577, 385, 14, 38, 262, 518, 138, 266, 522, 162, 290, 546, 386, 76, 524, 52, 84, 276, 532, 548, 324, 580, 88, 280, 200, 328, 392, 648, 304, 560, 336, 672, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_419, vertices_597, vertices_217, vertices_409, vertices_817, vertices_737, vertices_334, vertices_526, vertices_310, vertices_550, vertices_682, vertices_394, vertices_716, vertices_564, vertices_340, vertices_344] (by decide +kernel)
  polygons := literalFinset [vertices_153, vertices_81, vertices_273, vertices_529, vertices_161, vertices_289, vertices_545, vertices_193, vertices_577, vertices_385, vertices_14, vertices_38, vertices_262, vertices_518, vertices_138, vertices_266, vertices_522, vertices_162, vertices_290, vertices_546, vertices_386, vertices_76, vertices_524, vertices_52, vertices_84, vertices_276, vertices_532, vertices_548, vertices_324, vertices_580, vertices_88, vertices_280, vertices_200, vertices_328, vertices_392, vertices_648, vertices_304, vertices_560, vertices_336, vertices_672, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_419), (false, vertices_597), (false, vertices_217), (false, vertices_409), (false, vertices_817), (false, vertices_737), (true, vertices_14), (true, vertices_38), (true, vertices_262), (true, vertices_518), (true, vertices_138), (true, vertices_266), (true, vertices_522), (true, vertices_546), (true, vertices_76), (true, vertices_524), (true, vertices_52), (true, vertices_276), (true, vertices_548), (true, vertices_324), (true, vertices_328), (true, vertices_648), (true, vertices_336)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 17 19 21 24 26 28 29 30 31
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_419) then 18 else
  if p.val = (false, vertices_597) then 20 else
  if p.val = (false, vertices_217) then 22 else
  if p.val = (false, vertices_409) then 23 else
  if p.val = (false, vertices_817) then 25 else
  if p.val = (false, vertices_737) then 27 else
  if p.val = (true, vertices_14) then 0 else
  if p.val = (true, vertices_38) then 1 else
  if p.val = (true, vertices_262) then 2 else
  if p.val = (true, vertices_518) then 3 else
  if p.val = (true, vertices_138) then 4 else
  if p.val = (true, vertices_266) then 5 else
  if p.val = (true, vertices_522) then 6 else
  if p.val = (true, vertices_546) then 7 else
  if p.val = (true, vertices_76) then 8 else
  if p.val = (true, vertices_524) then 9 else
  if p.val = (true, vertices_52) then 10 else
  if p.val = (true, vertices_276) then 11 else
  if p.val = (true, vertices_548) then 12 else
  if p.val = (true, vertices_324) then 13 else
  if p.val = (true, vertices_328) then 14 else
  if p.val = (true, vertices_648) then 15 else
  if p.val = (true, vertices_336) then 16 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_14), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_38), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_262), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_518), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_138), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_266), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_522), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_546), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_76), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_524), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_52), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_276), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_548), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_324), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_328), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_648), by decide +kernel⟩
  | 16 => Sum.inr ⟨(true, vertices_336), by decide +kernel⟩
  | 17 => Sum.inl 0
  | 18 => Sum.inr ⟨(false, vertices_419), by decide +kernel⟩
  | 19 => Sum.inl 1
  | 20 => Sum.inr ⟨(false, vertices_597), by decide +kernel⟩
  | 21 => Sum.inl 2
  | 22 => Sum.inr ⟨(false, vertices_217), by decide +kernel⟩
  | 23 => Sum.inr ⟨(false, vertices_409), by decide +kernel⟩
  | 24 => Sum.inl 3
  | 25 => Sum.inr ⟨(false, vertices_817), by decide +kernel⟩
  | 26 => Sum.inl 4
  | 27 => Sum.inr ⟨(false, vertices_737), by decide +kernel⟩
  | 28 => Sum.inl 5
  | 29 => Sum.inl 6
  | 30 => Sum.inl 7
  | 31 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 3 4 7 310 38 2
cert_row_4 1 0 1 2 5 7 334 14 3
cert_row_4 2 0 2 4 6 8 682 138 2
cert_row_4 3 1 2 5 6 8 716 76 3
cert_rows
cert_pivot_2 3 7 0 1
cert_heightProof 4
cert_coverFacet 0 334
cert_cover_5 0 1 0 1 2 5 14 334 3
cert_coverFacet 1 526
cert_cover_2 1 1 0 2 8 14 526 3
cert_coverFacet 2 310
cert_cover_5 2 0 0 1 3 4 38 310 2
cert_coverFacet 3 550
cert_cover_2 3 1 0 4 8 38 550 3
cert_coverFacet 4 682
cert_cover_5 4 2 0 2 4 6 138 682 2
cert_coverFacet 5 394
cert_cover_2 5 2 0 6 7 138 394 3
cert_coverFacet 6 716
cert_cover_5 6 3 1 2 5 6 76 716 3
cert_coverFacet 7 564
cert_cover_2 7 3 1 4 8 52 564 3
cert_coverFacet 8 340
cert_cover_2 8 3 1 5 7 84 340 3
cert_coverFacet 9 344
cert_cover_2 9 3 2 5 7 88 344 3
cert_coveringFacets_5
cert_coveringProof
cert_certificate 4 10
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0415

end
end BundlePart9

section BundlePart10
/- Source: ProjectionCertificates/R_m16e10q1_0416.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0416

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [775, 173, 397, 613, 121, 841, 390, 646, 794, 434, 722, 244, 708, 312, 600, 424, 141, 37, 261, 517, 41, 73, 265, 97, 577, 769, 134, 262, 518, 146, 274, 530, 386, 642, 770, 100, 164, 196, 580, 388, 644, 56, 88, 280, 536, 168, 296, 584, 392, 776, 112, 176, 304, 208, 592, 416, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_775, vertices_173, vertices_397, vertices_613, vertices_121, vertices_841, vertices_390, vertices_646, vertices_794, vertices_434, vertices_722, vertices_244, vertices_708, vertices_312, vertices_600, vertices_424] (by decide +kernel)
  polygons := literalFinset [vertices_141, vertices_37, vertices_261, vertices_517, vertices_41, vertices_73, vertices_265, vertices_97, vertices_577, vertices_769, vertices_134, vertices_262, vertices_518, vertices_146, vertices_274, vertices_530, vertices_386, vertices_642, vertices_770, vertices_100, vertices_164, vertices_196, vertices_580, vertices_388, vertices_644, vertices_56, vertices_88, vertices_280, vertices_536, vertices_168, vertices_296, vertices_584, vertices_392, vertices_776, vertices_112, vertices_176, vertices_304, vertices_208, vertices_592, vertices_416, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_775), (false, vertices_173), (false, vertices_397), (false, vertices_613), (false, vertices_121), (false, vertices_841), (true, vertices_134), (true, vertices_146), (true, vertices_274), (true, vertices_530), (true, vertices_386), (true, vertices_642), (true, vertices_196), (true, vertices_644), (true, vertices_280), (true, vertices_536), (true, vertices_296), (true, vertices_176), (true, vertices_304), (true, vertices_208), (true, vertices_592), (true, vertices_416), (true, vertices_704)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 17 19 23 26 27 28 29 30 31
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_775) then 18 else
  if p.val = (false, vertices_173) then 20 else
  if p.val = (false, vertices_397) then 21 else
  if p.val = (false, vertices_613) then 22 else
  if p.val = (false, vertices_121) then 24 else
  if p.val = (false, vertices_841) then 25 else
  if p.val = (true, vertices_134) then 0 else
  if p.val = (true, vertices_146) then 1 else
  if p.val = (true, vertices_274) then 2 else
  if p.val = (true, vertices_530) then 3 else
  if p.val = (true, vertices_386) then 4 else
  if p.val = (true, vertices_642) then 5 else
  if p.val = (true, vertices_196) then 6 else
  if p.val = (true, vertices_644) then 7 else
  if p.val = (true, vertices_280) then 8 else
  if p.val = (true, vertices_536) then 9 else
  if p.val = (true, vertices_296) then 10 else
  if p.val = (true, vertices_176) then 11 else
  if p.val = (true, vertices_304) then 12 else
  if p.val = (true, vertices_208) then 13 else
  if p.val = (true, vertices_592) then 14 else
  if p.val = (true, vertices_416) then 15 else
  if p.val = (true, vertices_704) then 16 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_134), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_146), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_274), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_530), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_386), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_642), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_196), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_644), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_280), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_536), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_296), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_176), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_304), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_208), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_592), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_416), by decide +kernel⟩
  | 16 => Sum.inr ⟨(true, vertices_704), by decide +kernel⟩
  | 17 => Sum.inl 0
  | 18 => Sum.inr ⟨(false, vertices_775), by decide +kernel⟩
  | 19 => Sum.inl 1
  | 20 => Sum.inr ⟨(false, vertices_173), by decide +kernel⟩
  | 21 => Sum.inr ⟨(false, vertices_397), by decide +kernel⟩
  | 22 => Sum.inr ⟨(false, vertices_613), by decide +kernel⟩
  | 23 => Sum.inl 2
  | 24 => Sum.inr ⟨(false, vertices_121), by decide +kernel⟩
  | 25 => Sum.inr ⟨(false, vertices_841), by decide +kernel⟩
  | 26 => Sum.inl 3
  | 27 => Sum.inl 4
  | 28 => Sum.inl 5
  | 29 => Sum.inl 6
  | 30 => Sum.inl 7
  | 31 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 2 3 7 8 794 274 1
cert_row_4 1 0 3 4 6 7 434 146 2
cert_row_4 2 0 3 5 6 8 722 146 2
cert_row_4 3 1 3 4 5 6 244 100 1
cert_rows
cert_pivot_2 2 7 0 1
cert_heightProof 4
cert_coverFacet 0 390
cert_cover_2 0 1 0 6 7 134 390 3
cert_coverFacet 1 646
cert_cover_2 1 1 0 6 8 134 646 3
cert_coverFacet 2 794
cert_cover_5 2 0 0 2 3 7 274 794 1
cert_coverFacet 3 434
cert_cover_5 3 1 0 3 4 6 146 434 2
cert_coverFacet 4 722
cert_cover_5 4 2 0 3 5 6 146 722 2
cert_coverFacet 5 244
cert_cover_5 5 3 1 3 4 5 100 244 1
cert_coverFacet 6 708
cert_cover_2 6 5 1 6 8 196 708 3
cert_coverFacet 7 312
cert_cover_2 7 3 2 4 7 56 312 3
cert_coverFacet 8 600
cert_cover_2 8 3 2 5 8 88 600 3
cert_coverFacet 9 424
cert_cover_2 9 4 2 6 7 168 424 3
cert_coveringFacets_5
cert_coveringProof
cert_certificate 4 10
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0416

end
end BundlePart10

section BundlePart11
/- Source: ProjectionCertificates/R_m16e10q1_0417.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0417

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [803, 205, 613, 901, 369, 465, 782, 186, 538, 394, 626, 418, 604, 396, 216, 432, 69, 133, 517, 337, 97, 289, 545, 193, 385, 769, 26, 138, 266, 522, 50, 530, 162, 290, 546, 386, 770, 76, 140, 268, 524, 580, 388, 772, 88, 152, 536, 200, 392, 112, 176, 304, 208, 592, 400, 608, 416]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_803, vertices_205, vertices_613, vertices_901, vertices_369, vertices_465, vertices_782, vertices_186, vertices_538, vertices_394, vertices_626, vertices_418, vertices_604, vertices_396, vertices_216, vertices_432] (by decide +kernel)
  polygons := literalFinset [vertices_69, vertices_133, vertices_517, vertices_337, vertices_97, vertices_289, vertices_545, vertices_193, vertices_385, vertices_769, vertices_26, vertices_138, vertices_266, vertices_522, vertices_50, vertices_530, vertices_162, vertices_290, vertices_546, vertices_386, vertices_770, vertices_76, vertices_140, vertices_268, vertices_524, vertices_580, vertices_388, vertices_772, vertices_88, vertices_152, vertices_536, vertices_200, vertices_392, vertices_112, vertices_176, vertices_304, vertices_208, vertices_592, vertices_400, vertices_608, vertices_416] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_803), (false, vertices_205), (false, vertices_613), (false, vertices_901), (false, vertices_369), (false, vertices_465), (true, vertices_26), (true, vertices_138), (true, vertices_266), (true, vertices_522), (true, vertices_50), (true, vertices_530), (true, vertices_162), (true, vertices_386), (true, vertices_268), (true, vertices_524), (true, vertices_88), (true, vertices_152), (true, vertices_536), (true, vertices_392), (true, vertices_176), (true, vertices_592), (true, vertices_416)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 17 19 23 24 27 28 29 30 31
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_803) then 18 else
  if p.val = (false, vertices_205) then 20 else
  if p.val = (false, vertices_613) then 21 else
  if p.val = (false, vertices_901) then 22 else
  if p.val = (false, vertices_369) then 25 else
  if p.val = (false, vertices_465) then 26 else
  if p.val = (true, vertices_26) then 0 else
  if p.val = (true, vertices_138) then 1 else
  if p.val = (true, vertices_266) then 2 else
  if p.val = (true, vertices_522) then 3 else
  if p.val = (true, vertices_50) then 4 else
  if p.val = (true, vertices_530) then 5 else
  if p.val = (true, vertices_162) then 6 else
  if p.val = (true, vertices_386) then 7 else
  if p.val = (true, vertices_268) then 8 else
  if p.val = (true, vertices_524) then 9 else
  if p.val = (true, vertices_88) then 10 else
  if p.val = (true, vertices_152) then 11 else
  if p.val = (true, vertices_536) then 12 else
  if p.val = (true, vertices_392) then 13 else
  if p.val = (true, vertices_176) then 14 else
  if p.val = (true, vertices_592) then 15 else
  if p.val = (true, vertices_416) then 16 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_26), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_138), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_266), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_522), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_50), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_530), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_162), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_386), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_268), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_524), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_88), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_152), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_536), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_392), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_176), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_592), by decide +kernel⟩
  | 16 => Sum.inr ⟨(true, vertices_416), by decide +kernel⟩
  | 17 => Sum.inl 0
  | 18 => Sum.inr ⟨(false, vertices_803), by decide +kernel⟩
  | 19 => Sum.inl 1
  | 20 => Sum.inr ⟨(false, vertices_205), by decide +kernel⟩
  | 21 => Sum.inr ⟨(false, vertices_613), by decide +kernel⟩
  | 22 => Sum.inr ⟨(false, vertices_901), by decide +kernel⟩
  | 23 => Sum.inl 2
  | 24 => Sum.inl 3
  | 25 => Sum.inr ⟨(false, vertices_369), by decide +kernel⟩
  | 26 => Sum.inr ⟨(false, vertices_465), by decide +kernel⟩
  | 27 => Sum.inl 4
  | 28 => Sum.inl 5
  | 29 => Sum.inl 6
  | 30 => Sum.inl 7
  | 31 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 2 7 8 782 266 1
cert_row_4 1 0 2 3 4 6 186 26 3
cert_row_4 2 0 3 4 5 8 626 50 3
cert_row_4 3 1 2 3 5 8 604 76 2
cert_rows
cert_pivot_2 7 6 0 1
cert_heightProof 4
cert_coverFacet 0 782
cert_cover_5 0 0 0 1 2 7 266 782 1
cert_coverFacet 1 186
cert_cover_5 1 1 0 2 3 4 26 186 3
cert_coverFacet 2 538
cert_cover_2 2 2 0 3 8 26 538 3
cert_coverFacet 3 394
cert_cover_2 3 2 0 6 7 138 394 3
cert_coverFacet 4 626
cert_cover_5 4 2 0 3 4 5 50 626 3
cert_coverFacet 5 418
cert_cover_2 5 4 0 6 7 162 418 3
cert_coverFacet 6 604
cert_cover_5 6 3 1 2 3 5 76 604 2
cert_coverFacet 7 396
cert_cover_2 7 2 1 6 7 140 396 3
cert_coverFacet 8 216
cert_cover_2 8 3 2 5 6 88 216 3
cert_coverFacet 9 432
cert_cover_2 9 4 3 6 7 176 432 3
cert_coveringFacets_5
cert_coveringProof
cert_certificate 4 10
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0417

end
end BundlePart11

section BundlePart12
/- Source: ProjectionCertificates/R_m16e10q1_0418.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0418

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [419, 93, 525, 805, 453, 585, 737, 286, 302, 570, 466, 658, 674, 556, 340, 728, 13, 69, 261, 517, 73, 521, 161, 289, 545, 193, 577, 385, 270, 26, 42, 146, 274, 530, 162, 290, 546, 386, 642, 28, 44, 524, 84, 276, 292, 548, 324, 88, 536, 552, 584, 208, 336, 656, 672, 448, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_419, vertices_93, vertices_525, vertices_805, vertices_453, vertices_585, vertices_737, vertices_286, vertices_302, vertices_570, vertices_466, vertices_658, vertices_674, vertices_556, vertices_340, vertices_728] (by decide +kernel)
  polygons := literalFinset [vertices_13, vertices_69, vertices_261, vertices_517, vertices_73, vertices_521, vertices_161, vertices_289, vertices_545, vertices_193, vertices_577, vertices_385, vertices_270, vertices_26, vertices_42, vertices_146, vertices_274, vertices_530, vertices_162, vertices_290, vertices_546, vertices_386, vertices_642, vertices_28, vertices_44, vertices_524, vertices_84, vertices_276, vertices_292, vertices_548, vertices_324, vertices_88, vertices_536, vertices_552, vertices_584, vertices_208, vertices_336, vertices_656, vertices_672, vertices_448, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_419), (false, vertices_93), (false, vertices_525), (false, vertices_805), (false, vertices_453), (false, vertices_585), (false, vertices_737), (true, vertices_270), (true, vertices_26), (true, vertices_42), (true, vertices_146), (true, vertices_274), (true, vertices_530), (true, vertices_546), (true, vertices_642), (true, vertices_44), (true, vertices_276), (true, vertices_536), (true, vertices_552), (true, vertices_208), (true, vertices_336), (true, vertices_656)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 16 19 23 24 25 27 28 29 30
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_419) then 17 else
  if p.val = (false, vertices_93) then 20 else
  if p.val = (false, vertices_525) then 0 else
  if p.val = (false, vertices_805) then 21 else
  if p.val = (false, vertices_453) then 22 else
  if p.val = (false, vertices_585) then 1 else
  if p.val = (false, vertices_737) then 26 else
  if p.val = (true, vertices_270) then 18 else
  if p.val = (true, vertices_26) then 2 else
  if p.val = (true, vertices_42) then 3 else
  if p.val = (true, vertices_146) then 4 else
  if p.val = (true, vertices_274) then 5 else
  if p.val = (true, vertices_530) then 6 else
  if p.val = (true, vertices_546) then 7 else
  if p.val = (true, vertices_642) then 8 else
  if p.val = (true, vertices_44) then 9 else
  if p.val = (true, vertices_276) then 10 else
  if p.val = (true, vertices_536) then 11 else
  if p.val = (true, vertices_552) then 12 else
  if p.val = (true, vertices_208) then 13 else
  if p.val = (true, vertices_336) then 14 else
  if p.val = (true, vertices_656) then 15 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_525), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_585), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_26), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_42), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_146), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_274), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_530), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_546), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_642), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_44), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_276), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_536), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_552), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_208), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_336), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_656), by decide +kernel⟩
  | 16 => Sum.inl 0
  | 17 => Sum.inr ⟨(false, vertices_419), by decide +kernel⟩
  | 18 => Sum.inr ⟨(true, vertices_270), by decide +kernel⟩
  | 19 => Sum.inl 1
  | 20 => Sum.inr ⟨(false, vertices_93), by decide +kernel⟩
  | 21 => Sum.inr ⟨(false, vertices_805), by decide +kernel⟩
  | 22 => Sum.inr ⟨(false, vertices_453), by decide +kernel⟩
  | 23 => Sum.inl 2
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
cert_row_2 0 0 1 2 7 270
cert_row_4 1 0 2 3 4 8 570 26 3
cert_row_4 2 0 3 5 6 7 466 146 2
cert_row_4 3 2 3 5 6 8 728 88 3
cert_rows
cert_pivot_2 1 4 0 2
cert_heightProof 4
cert_coverFacet 0 286
cert_cover_5 0 0 0 1 2 3 270 286 3
cert_coverFacet 1 302
cert_cover_5 1 0 0 1 2 4 270 302 3
cert_coverFacet 2 570
cert_cover_5 2 1 0 2 3 4 26 570 3
cert_coverFacet 3 466
cert_cover_5 3 2 0 3 5 6 146 466 2
cert_coverFacet 4 658
cert_cover_2 4 3 0 6 8 146 658 3
cert_coverFacet 5 674
cert_cover_2 5 4 0 6 8 162 674 3
cert_coverFacet 6 556
cert_cover_2 6 2 1 4 8 44 556 3
cert_coverFacet 7 340
cert_cover_2 7 3 1 5 7 84 340 3
cert_coverFacet 8 728
cert_cover_5 8 3 2 3 5 6 88 728 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0418

end
end BundlePart12

section BundlePart13
/- Source: ProjectionCertificates/R_m16e10q1_0419.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0419

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [451, 29, 45, 565, 345, 425, 241, 342, 598, 774, 906, 738, 284, 684, 780, 624, 13, 21, 37, 25, 41, 265, 49, 81, 161, 193, 321, 385, 86, 262, 518, 194, 322, 578, 386, 642, 770, 28, 44, 268, 524, 276, 532, 548, 772, 280, 168, 392, 648, 776, 112, 560, 336, 592, 224, 608, 672]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_451, vertices_29, vertices_45, vertices_565, vertices_345, vertices_425, vertices_241, vertices_342, vertices_598, vertices_774, vertices_906, vertices_738, vertices_284, vertices_684, vertices_780, vertices_624] (by decide +kernel)
  polygons := literalFinset [vertices_13, vertices_21, vertices_37, vertices_25, vertices_41, vertices_265, vertices_49, vertices_81, vertices_161, vertices_193, vertices_321, vertices_385, vertices_86, vertices_262, vertices_518, vertices_194, vertices_322, vertices_578, vertices_386, vertices_642, vertices_770, vertices_28, vertices_44, vertices_268, vertices_524, vertices_276, vertices_532, vertices_548, vertices_772, vertices_280, vertices_168, vertices_392, vertices_648, vertices_776, vertices_112, vertices_560, vertices_336, vertices_592, vertices_224, vertices_608, vertices_672] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_451), (false, vertices_29), (false, vertices_45), (false, vertices_565), (false, vertices_345), (false, vertices_425), (false, vertices_241), (true, vertices_86), (true, vertices_262), (true, vertices_518), (true, vertices_578), (true, vertices_642), (true, vertices_770), (true, vertices_268), (true, vertices_524), (true, vertices_276), (true, vertices_772), (true, vertices_648), (true, vertices_776), (true, vertices_592), (true, vertices_608), (true, vertices_672)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 16 19 21 24 26 27 28 29 30
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_451) then 17 else
  if p.val = (false, vertices_29) then 0 else
  if p.val = (false, vertices_45) then 1 else
  if p.val = (false, vertices_565) then 20 else
  if p.val = (false, vertices_345) then 22 else
  if p.val = (false, vertices_425) then 23 else
  if p.val = (false, vertices_241) then 25 else
  if p.val = (true, vertices_86) then 18 else
  if p.val = (true, vertices_262) then 2 else
  if p.val = (true, vertices_518) then 3 else
  if p.val = (true, vertices_578) then 4 else
  if p.val = (true, vertices_642) then 5 else
  if p.val = (true, vertices_770) then 6 else
  if p.val = (true, vertices_268) then 7 else
  if p.val = (true, vertices_524) then 8 else
  if p.val = (true, vertices_276) then 9 else
  if p.val = (true, vertices_772) then 10 else
  if p.val = (true, vertices_648) then 11 else
  if p.val = (true, vertices_776) then 12 else
  if p.val = (true, vertices_592) then 13 else
  if p.val = (true, vertices_608) then 14 else
  if p.val = (true, vertices_672) then 15 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_29), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_45), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_262), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_518), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_578), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_642), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_770), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_268), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_524), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_276), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_772), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_648), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_776), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_592), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_608), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_672), by decide +kernel⟩
  | 16 => Sum.inl 0
  | 17 => Sum.inr ⟨(false, vertices_451), by decide +kernel⟩
  | 18 => Sum.inr ⟨(true, vertices_86), by decide +kernel⟩
  | 19 => Sum.inl 1
  | 20 => Sum.inr ⟨(false, vertices_565), by decide +kernel⟩
  | 21 => Sum.inl 2
  | 22 => Sum.inr ⟨(false, vertices_345), by decide +kernel⟩
  | 23 => Sum.inr ⟨(false, vertices_425), by decide +kernel⟩
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
cert_row_2 0 0 1 3 5 86
cert_row_4 1 0 2 6 7 8 906 386 1
cert_row_4 2 0 4 5 6 8 738 194 1
cert_row_4 3 1 2 4 6 8 684 44 3
cert_rows
cert_pivot_2 3 7 0 1
cert_heightProof 4
cert_coverFacet 0 342
cert_cover_5 0 0 0 1 3 7 86 342 3
cert_coverFacet 1 598
cert_cover_5 1 0 0 1 3 8 86 598 3
cert_coverFacet 2 774
cert_cover_2 2 1 0 7 8 262 774 3
cert_coverFacet 3 906
cert_cover_5 3 1 0 2 6 7 386 906 1
cert_coverFacet 4 738
cert_cover_5 4 2 0 4 5 6 194 738 1
cert_coverFacet 5 284
cert_cover_2 5 2 1 3 7 28 284 3
cert_coverFacet 6 684
cert_cover_5 6 3 1 2 4 6 44 684 3
cert_coverFacet 7 780
cert_cover_2 7 2 1 7 8 268 780 3
cert_coverFacet 8 624
cert_cover_2 8 4 3 5 8 112 624 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0419

end
end BundlePart13

section BundlePart14
/- Source: ProjectionCertificates/R_m16e10q1_0420.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0420

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [419, 93, 525, 357, 677, 585, 961, 286, 302, 570, 466, 658, 674, 556, 340, 728, 13, 37, 69, 517, 73, 521, 161, 289, 321, 577, 385, 641, 270, 26, 42, 146, 274, 530, 162, 290, 546, 386, 642, 28, 44, 524, 84, 276, 292, 548, 324, 88, 536, 552, 584, 208, 336, 656, 672, 448, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_419, vertices_93, vertices_525, vertices_357, vertices_677, vertices_585, vertices_961, vertices_286, vertices_302, vertices_570, vertices_466, vertices_658, vertices_674, vertices_556, vertices_340, vertices_728] (by decide +kernel)
  polygons := literalFinset [vertices_13, vertices_37, vertices_69, vertices_517, vertices_73, vertices_521, vertices_161, vertices_289, vertices_321, vertices_577, vertices_385, vertices_641, vertices_270, vertices_26, vertices_42, vertices_146, vertices_274, vertices_530, vertices_162, vertices_290, vertices_546, vertices_386, vertices_642, vertices_28, vertices_44, vertices_524, vertices_84, vertices_276, vertices_292, vertices_548, vertices_324, vertices_88, vertices_536, vertices_552, vertices_584, vertices_208, vertices_336, vertices_656, vertices_672, vertices_448, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_419), (false, vertices_93), (false, vertices_525), (false, vertices_357), (false, vertices_677), (false, vertices_585), (false, vertices_961), (true, vertices_270), (true, vertices_26), (true, vertices_42), (true, vertices_146), (true, vertices_274), (true, vertices_530), (true, vertices_546), (true, vertices_642), (true, vertices_44), (true, vertices_276), (true, vertices_536), (true, vertices_552), (true, vertices_208), (true, vertices_336), (true, vertices_656)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 16 19 23 24 25 26 28 29 30
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_419) then 17 else
  if p.val = (false, vertices_93) then 20 else
  if p.val = (false, vertices_525) then 0 else
  if p.val = (false, vertices_357) then 21 else
  if p.val = (false, vertices_677) then 22 else
  if p.val = (false, vertices_585) then 1 else
  if p.val = (false, vertices_961) then 27 else
  if p.val = (true, vertices_270) then 18 else
  if p.val = (true, vertices_26) then 2 else
  if p.val = (true, vertices_42) then 3 else
  if p.val = (true, vertices_146) then 4 else
  if p.val = (true, vertices_274) then 5 else
  if p.val = (true, vertices_530) then 6 else
  if p.val = (true, vertices_546) then 7 else
  if p.val = (true, vertices_642) then 8 else
  if p.val = (true, vertices_44) then 9 else
  if p.val = (true, vertices_276) then 10 else
  if p.val = (true, vertices_536) then 11 else
  if p.val = (true, vertices_552) then 12 else
  if p.val = (true, vertices_208) then 13 else
  if p.val = (true, vertices_336) then 14 else
  if p.val = (true, vertices_656) then 15 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_525), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_585), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_26), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_42), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_146), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_274), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_530), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_546), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_642), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_44), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_276), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_536), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_552), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_208), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_336), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_656), by decide +kernel⟩
  | 16 => Sum.inl 0
  | 17 => Sum.inr ⟨(false, vertices_419), by decide +kernel⟩
  | 18 => Sum.inr ⟨(true, vertices_270), by decide +kernel⟩
  | 19 => Sum.inl 1
  | 20 => Sum.inr ⟨(false, vertices_93), by decide +kernel⟩
  | 21 => Sum.inr ⟨(false, vertices_357), by decide +kernel⟩
  | 22 => Sum.inr ⟨(false, vertices_677), by decide +kernel⟩
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
cert_row_2 0 0 1 2 7 270
cert_row_4 1 0 2 3 4 8 570 26 3
cert_row_4 2 0 3 5 6 7 466 146 2
cert_row_4 3 2 3 5 6 8 728 88 3
cert_rows
cert_pivot_2 1 4 0 2
cert_heightProof 4
cert_coverFacet 0 286
cert_cover_5 0 0 0 1 2 3 270 286 3
cert_coverFacet 1 302
cert_cover_5 1 0 0 1 2 4 270 302 3
cert_coverFacet 2 570
cert_cover_5 2 1 0 2 3 4 26 570 3
cert_coverFacet 3 466
cert_cover_5 3 2 0 3 5 6 146 466 2
cert_coverFacet 4 658
cert_cover_2 4 3 0 6 8 146 658 3
cert_coverFacet 5 674
cert_cover_2 5 4 0 6 8 162 674 3
cert_coverFacet 6 556
cert_cover_2 6 2 1 4 8 44 556 3
cert_coverFacet 7 340
cert_cover_2 7 3 1 5 7 84 340 3
cert_coverFacet 8 728
cert_cover_5 8 3 2 3 5 6 88 728 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0420

end
end BundlePart14

section BundlePart15
/- Source: ProjectionCertificates/R_m16e10q1_0421.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0421

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [451, 29, 45, 565, 409, 233, 369, 342, 598, 774, 906, 738, 284, 684, 780, 624, 13, 21, 37, 25, 41, 137, 49, 273, 97, 193, 321, 385, 86, 262, 518, 194, 322, 578, 386, 642, 770, 28, 44, 268, 524, 276, 532, 548, 772, 280, 168, 392, 648, 776, 112, 560, 336, 592, 224, 608, 672]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_451, vertices_29, vertices_45, vertices_565, vertices_409, vertices_233, vertices_369, vertices_342, vertices_598, vertices_774, vertices_906, vertices_738, vertices_284, vertices_684, vertices_780, vertices_624] (by decide +kernel)
  polygons := literalFinset [vertices_13, vertices_21, vertices_37, vertices_25, vertices_41, vertices_137, vertices_49, vertices_273, vertices_97, vertices_193, vertices_321, vertices_385, vertices_86, vertices_262, vertices_518, vertices_194, vertices_322, vertices_578, vertices_386, vertices_642, vertices_770, vertices_28, vertices_44, vertices_268, vertices_524, vertices_276, vertices_532, vertices_548, vertices_772, vertices_280, vertices_168, vertices_392, vertices_648, vertices_776, vertices_112, vertices_560, vertices_336, vertices_592, vertices_224, vertices_608, vertices_672] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_451), (false, vertices_29), (false, vertices_45), (false, vertices_565), (false, vertices_409), (false, vertices_233), (false, vertices_369), (true, vertices_86), (true, vertices_262), (true, vertices_518), (true, vertices_578), (true, vertices_642), (true, vertices_770), (true, vertices_268), (true, vertices_524), (true, vertices_276), (true, vertices_772), (true, vertices_648), (true, vertices_776), (true, vertices_592), (true, vertices_608), (true, vertices_672)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 16 19 21 24 26 27 28 29 30
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_451) then 17 else
  if p.val = (false, vertices_29) then 0 else
  if p.val = (false, vertices_45) then 1 else
  if p.val = (false, vertices_565) then 20 else
  if p.val = (false, vertices_409) then 22 else
  if p.val = (false, vertices_233) then 23 else
  if p.val = (false, vertices_369) then 25 else
  if p.val = (true, vertices_86) then 18 else
  if p.val = (true, vertices_262) then 2 else
  if p.val = (true, vertices_518) then 3 else
  if p.val = (true, vertices_578) then 4 else
  if p.val = (true, vertices_642) then 5 else
  if p.val = (true, vertices_770) then 6 else
  if p.val = (true, vertices_268) then 7 else
  if p.val = (true, vertices_524) then 8 else
  if p.val = (true, vertices_276) then 9 else
  if p.val = (true, vertices_772) then 10 else
  if p.val = (true, vertices_648) then 11 else
  if p.val = (true, vertices_776) then 12 else
  if p.val = (true, vertices_592) then 13 else
  if p.val = (true, vertices_608) then 14 else
  if p.val = (true, vertices_672) then 15 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_29), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_45), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_262), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_518), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_578), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_642), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_770), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_268), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_524), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_276), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_772), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_648), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_776), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_592), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_608), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_672), by decide +kernel⟩
  | 16 => Sum.inl 0
  | 17 => Sum.inr ⟨(false, vertices_451), by decide +kernel⟩
  | 18 => Sum.inr ⟨(true, vertices_86), by decide +kernel⟩
  | 19 => Sum.inl 1
  | 20 => Sum.inr ⟨(false, vertices_565), by decide +kernel⟩
  | 21 => Sum.inl 2
  | 22 => Sum.inr ⟨(false, vertices_409), by decide +kernel⟩
  | 23 => Sum.inr ⟨(false, vertices_233), by decide +kernel⟩
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
cert_row_2 0 0 1 3 5 86
cert_row_4 1 0 2 6 7 8 906 386 1
cert_row_4 2 0 4 5 6 8 738 194 1
cert_row_4 3 1 2 4 6 8 684 44 3
cert_rows
cert_pivot_2 3 7 0 1
cert_heightProof 4
cert_coverFacet 0 342
cert_cover_5 0 0 0 1 3 7 86 342 3
cert_coverFacet 1 598
cert_cover_5 1 0 0 1 3 8 86 598 3
cert_coverFacet 2 774
cert_cover_2 2 1 0 7 8 262 774 3
cert_coverFacet 3 906
cert_cover_5 3 1 0 2 6 7 386 906 1
cert_coverFacet 4 738
cert_cover_5 4 2 0 4 5 6 194 738 1
cert_coverFacet 5 284
cert_cover_2 5 2 1 3 7 28 284 3
cert_coverFacet 6 684
cert_cover_5 6 3 1 2 4 6 44 684 3
cert_coverFacet 7 780
cert_cover_2 7 2 1 7 8 268 780 3
cert_coverFacet 8 624
cert_cover_2 8 4 3 5 8 112 624 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0421

end
end BundlePart15

section BundlePart16
/- Source: ProjectionCertificates/R_m16e10q1_0422.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0422

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [647, 299, 523, 451, 617, 369, 705, 158, 526, 410, 540, 116, 564, 468, 740, 824, 11, 131, 259, 515, 41, 521, 97, 289, 193, 321, 577, 641, 14, 134, 518, 154, 266, 522, 386, 28, 524, 52, 84, 148, 532, 100, 548, 196, 644, 280, 536, 296, 552, 112, 304, 560, 336, 400, 608, 448, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_647, vertices_299, vertices_523, vertices_451, vertices_617, vertices_369, vertices_705, vertices_158, vertices_526, vertices_410, vertices_540, vertices_116, vertices_564, vertices_468, vertices_740, vertices_824] (by decide +kernel)
  polygons := literalFinset [vertices_11, vertices_131, vertices_259, vertices_515, vertices_41, vertices_521, vertices_97, vertices_289, vertices_193, vertices_321, vertices_577, vertices_641, vertices_14, vertices_134, vertices_518, vertices_154, vertices_266, vertices_522, vertices_386, vertices_28, vertices_524, vertices_52, vertices_84, vertices_148, vertices_532, vertices_100, vertices_548, vertices_196, vertices_644, vertices_280, vertices_536, vertices_296, vertices_552, vertices_112, vertices_304, vertices_560, vertices_336, vertices_400, vertices_608, vertices_448, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_647), (false, vertices_299), (false, vertices_523), (false, vertices_451), (false, vertices_617), (false, vertices_369), (false, vertices_705), (true, vertices_14), (true, vertices_154), (true, vertices_28), (true, vertices_524), (true, vertices_52), (true, vertices_84), (true, vertices_148), (true, vertices_532), (true, vertices_100), (true, vertices_548), (true, vertices_196), (true, vertices_280), (true, vertices_536), (true, vertices_560), (true, vertices_400)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 18 16 22 24 26 27 28 29 30
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_647) then 17 else
  if p.val = (false, vertices_299) then 19 else
  if p.val = (false, vertices_523) then 0 else
  if p.val = (false, vertices_451) then 20 else
  if p.val = (false, vertices_617) then 23 else
  if p.val = (false, vertices_369) then 25 else
  if p.val = (false, vertices_705) then 1 else
  if p.val = (true, vertices_14) then 2 else
  if p.val = (true, vertices_154) then 21 else
  if p.val = (true, vertices_28) then 3 else
  if p.val = (true, vertices_524) then 4 else
  if p.val = (true, vertices_52) then 5 else
  if p.val = (true, vertices_84) then 6 else
  if p.val = (true, vertices_148) then 7 else
  if p.val = (true, vertices_532) then 8 else
  if p.val = (true, vertices_100) then 9 else
  if p.val = (true, vertices_548) then 10 else
  if p.val = (true, vertices_196) then 11 else
  if p.val = (true, vertices_280) then 12 else
  if p.val = (true, vertices_536) then 13 else
  if p.val = (true, vertices_560) then 14 else
  if p.val = (true, vertices_400) then 15 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_523), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_705), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_14), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_28), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_524), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_52), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_84), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_148), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_532), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_100), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_548), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_196), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_280), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_536), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_560), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_400), by decide +kernel⟩
  | 16 => Sum.inl 1
  | 17 => Sum.inr ⟨(false, vertices_647), by decide +kernel⟩
  | 18 => Sum.inl 0
  | 19 => Sum.inr ⟨(false, vertices_299), by decide +kernel⟩
  | 20 => Sum.inr ⟨(false, vertices_451), by decide +kernel⟩
  | 21 => Sum.inr ⟨(true, vertices_154), by decide +kernel⟩
  | 22 => Sum.inl 2
  | 23 => Sum.inr ⟨(false, vertices_617), by decide +kernel⟩
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
cert_row_2 0 0 2 3 6 154
cert_row_4 1 2 3 4 7 8 824 280 2
cert_row_4 2 1 3 5 6 7 468 84 3
cert_row_4 3 1 4 5 6 8 740 100 3
cert_rows
cert_pivot_2 0 2 3 1
cert_heightProof 4
cert_coverFacet 0 158
cert_cover_5 0 0 0 1 2 3 14 158 3
cert_coverFacet 1 526
cert_cover_2 1 1 0 2 8 14 526 3
cert_coverFacet 2 410
cert_cover_5 2 0 0 2 3 7 154 410 3
cert_coverFacet 3 540
cert_cover_2 3 2 1 3 8 28 540 3
cert_coverFacet 4 116
cert_cover_2 4 3 1 4 5 52 116 3
cert_coverFacet 5 564
cert_cover_2 5 3 1 4 8 52 564 3
cert_coverFacet 6 468
cert_cover_5 6 2 1 3 5 6 84 468 3
cert_coverFacet 7 740
cert_cover_5 7 3 1 4 5 6 100 740 3
cert_coverFacet 8 824
cert_cover_5 8 1 2 3 4 7 280 824 2
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0422

end
end BundlePart16

section BundlePart17
/- Source: ProjectionCertificates/R_m16e10q1_0423.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0423

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [659, 309, 533, 613, 409, 681, 297, 838, 218, 346, 786, 738, 236, 300, 332, 788, 21, 37, 517, 41, 137, 265, 145, 273, 529, 289, 545, 641, 90, 146, 274, 530, 194, 322, 578, 642, 770, 44, 76, 268, 276, 532, 100, 292, 324, 580, 772, 152, 280, 168, 296, 200, 328, 784, 224, 608, 672]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_659, vertices_309, vertices_533, vertices_613, vertices_409, vertices_681, vertices_297, vertices_838, vertices_218, vertices_346, vertices_786, vertices_738, vertices_236, vertices_300, vertices_332, vertices_788] (by decide +kernel)
  polygons := literalFinset [vertices_21, vertices_37, vertices_517, vertices_41, vertices_137, vertices_265, vertices_145, vertices_273, vertices_529, vertices_289, vertices_545, vertices_641, vertices_90, vertices_146, vertices_274, vertices_530, vertices_194, vertices_322, vertices_578, vertices_642, vertices_770, vertices_44, vertices_76, vertices_268, vertices_276, vertices_532, vertices_100, vertices_292, vertices_324, vertices_580, vertices_772, vertices_152, vertices_280, vertices_168, vertices_296, vertices_200, vertices_328, vertices_784, vertices_224, vertices_608, vertices_672] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_659), (false, vertices_309), (false, vertices_533), (false, vertices_613), (false, vertices_409), (false, vertices_681), (false, vertices_297), (true, vertices_90), (true, vertices_274), (true, vertices_194), (true, vertices_322), (true, vertices_578), (true, vertices_770), (true, vertices_44), (true, vertices_76), (true, vertices_268), (true, vertices_324), (true, vertices_772), (true, vertices_200), (true, vertices_328), (true, vertices_784), (true, vertices_224)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 16 19 22 25 26 27 28 29 30
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_659) then 17 else
  if p.val = (false, vertices_309) then 20 else
  if p.val = (false, vertices_533) then 0 else
  if p.val = (false, vertices_613) then 21 else
  if p.val = (false, vertices_409) then 23 else
  if p.val = (false, vertices_681) then 24 else
  if p.val = (false, vertices_297) then 1 else
  if p.val = (true, vertices_90) then 18 else
  if p.val = (true, vertices_274) then 2 else
  if p.val = (true, vertices_194) then 3 else
  if p.val = (true, vertices_322) then 4 else
  if p.val = (true, vertices_578) then 5 else
  if p.val = (true, vertices_770) then 6 else
  if p.val = (true, vertices_44) then 7 else
  if p.val = (true, vertices_76) then 8 else
  if p.val = (true, vertices_268) then 9 else
  if p.val = (true, vertices_324) then 10 else
  if p.val = (true, vertices_772) then 11 else
  if p.val = (true, vertices_200) then 12 else
  if p.val = (true, vertices_328) then 13 else
  if p.val = (true, vertices_784) then 14 else
  if p.val = (true, vertices_224) then 15 else
  0
cert_priority
cert_nodeAtPriority_39 0 533 1 297 274 194 322 578 770 44 76 268 324 772 200 328 784 224 659 90 309 613 409 681
cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 2 3 5 90
cert_row_4 1 0 1 5 7 8 838 322 1
cert_row_4 2 0 4 5 6 8 738 194 1
cert_row_4 3 1 2 4 5 6 236 44 3
cert_rows
cert_pivot_2 3 7 0 1
cert_heightProof 4
cert_coverFacet 0 838
cert_cover_5 0 1 0 1 5 7 322 838 1
cert_coverFacet 1 218
cert_cover_5 1 0 0 2 3 6 90 218 3
cert_coverFacet 2 346
cert_cover_5 2 0 0 2 3 7 90 346 3
cert_coverFacet 3 786
cert_cover_2 3 3 0 7 8 274 786 3
cert_coverFacet 4 738
cert_cover_5 4 2 0 4 5 6 194 738 1
cert_coverFacet 5 236
cert_cover_5 5 3 1 2 4 5 44 236 3
cert_coverFacet 6 300
cert_cover_2 6 2 1 4 7 44 300 3
cert_coverFacet 7 332
cert_cover_2 7 2 1 5 7 76 332 3
cert_coverFacet 8 788
cert_cover_2 8 3 1 7 8 276 788 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0423

end
end BundlePart17

section BundlePart18
/- Source: ProjectionCertificates/R_m16e10q1_0424.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0424

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [775, 181, 533, 453, 233, 625, 833, 286, 542, 106, 554, 458, 866, 404, 696, 408, 21, 133, 261, 517, 49, 529, 97, 161, 193, 321, 577, 769, 30, 262, 518, 42, 74, 266, 522, 98, 546, 322, 770, 148, 276, 532, 388, 152, 280, 536, 104, 168, 552, 200, 392, 176, 560, 400, 608, 448, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_775, vertices_181, vertices_533, vertices_453, vertices_233, vertices_625, vertices_833, vertices_286, vertices_542, vertices_106, vertices_554, vertices_458, vertices_866, vertices_404, vertices_696, vertices_408] (by decide +kernel)
  polygons := literalFinset [vertices_21, vertices_133, vertices_261, vertices_517, vertices_49, vertices_529, vertices_97, vertices_161, vertices_193, vertices_321, vertices_577, vertices_769, vertices_30, vertices_262, vertices_518, vertices_42, vertices_74, vertices_266, vertices_522, vertices_98, vertices_546, vertices_322, vertices_770, vertices_148, vertices_276, vertices_532, vertices_388, vertices_152, vertices_280, vertices_536, vertices_104, vertices_168, vertices_552, vertices_200, vertices_392, vertices_176, vertices_560, vertices_400, vertices_608, vertices_448, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_775), (false, vertices_181), (false, vertices_533), (false, vertices_453), (false, vertices_233), (false, vertices_625), (false, vertices_833), (true, vertices_30), (true, vertices_42), (true, vertices_74), (true, vertices_266), (true, vertices_522), (true, vertices_98), (true, vertices_546), (true, vertices_322), (true, vertices_276), (true, vertices_152), (true, vertices_280), (true, vertices_536), (true, vertices_552), (true, vertices_392), (true, vertices_400)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 16 19 22 24 26 27 28 29 30
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_775) then 17 else
  if p.val = (false, vertices_181) then 20 else
  if p.val = (false, vertices_533) then 0 else
  if p.val = (false, vertices_453) then 21 else
  if p.val = (false, vertices_233) then 23 else
  if p.val = (false, vertices_625) then 25 else
  if p.val = (false, vertices_833) then 1 else
  if p.val = (true, vertices_30) then 18 else
  if p.val = (true, vertices_42) then 2 else
  if p.val = (true, vertices_74) then 3 else
  if p.val = (true, vertices_266) then 4 else
  if p.val = (true, vertices_522) then 5 else
  if p.val = (true, vertices_98) then 6 else
  if p.val = (true, vertices_546) then 7 else
  if p.val = (true, vertices_322) then 8 else
  if p.val = (true, vertices_276) then 9 else
  if p.val = (true, vertices_152) then 10 else
  if p.val = (true, vertices_280) then 11 else
  if p.val = (true, vertices_536) then 12 else
  if p.val = (true, vertices_552) then 13 else
  if p.val = (true, vertices_392) then 14 else
  if p.val = (true, vertices_400) then 15 else
  0
cert_priority
cert_nodeAtPriority_50 1 533 0 833 42 74 266 522 98 546 322 276 152 280 536 552 392 400 775 30 181 453 233 625
cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 1 2 3 30
cert_row_4 1 2 3 4 6 8 696 152 2
cert_row_4 2 0 2 5 6 7 458 74 3
cert_row_4 3 0 4 5 7 8 866 98 3
cert_rows
cert_pivot_2 1 3 2 0
cert_heightProof 4
cert_coverFacet 0 286
cert_cover_5 0 0 0 1 2 7 30 286 3
cert_coverFacet 1 542
cert_cover_5 1 0 0 1 2 8 30 542 3
cert_coverFacet 2 106
cert_cover_2 2 2 0 4 5 42 106 3
cert_coverFacet 3 554
cert_cover_2 3 2 0 4 8 42 554 3
cert_coverFacet 4 458
cert_cover_5 4 2 0 2 5 6 74 458 3
cert_coverFacet 5 866
cert_cover_5 5 3 0 4 5 7 98 866 3
cert_coverFacet 6 404
cert_cover_2 6 3 1 6 7 148 404 3
cert_coverFacet 7 696
cert_cover_5 7 1 2 3 4 6 152 696 2
cert_coverFacet 8 408
cert_cover_2 8 3 2 6 7 152 408 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0424

end
end BundlePart18

section BundlePart19
/- Source: ProjectionCertificates/R_m16e10q1_0425.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0425

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [403, 659, 803, 709, 617, 481, 286, 602, 778, 92, 236, 300, 436, 596, 660, 808, 147, 259, 515, 97, 289, 545, 193, 577, 385, 641, 26, 266, 522, 274, 530, 770, 28, 44, 76, 268, 84, 148, 276, 532, 164, 292, 196, 580, 644, 88, 104, 296, 552, 584, 776, 592, 400, 656, 224, 416, 800]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_403, vertices_659, vertices_803, vertices_709, vertices_617, vertices_481, vertices_286, vertices_602, vertices_778, vertices_92, vertices_236, vertices_300, vertices_436, vertices_596, vertices_660, vertices_808] (by decide +kernel)
  polygons := literalFinset [vertices_147, vertices_259, vertices_515, vertices_97, vertices_289, vertices_545, vertices_193, vertices_577, vertices_385, vertices_641, vertices_26, vertices_266, vertices_522, vertices_274, vertices_530, vertices_770, vertices_28, vertices_44, vertices_76, vertices_268, vertices_84, vertices_148, vertices_276, vertices_532, vertices_164, vertices_292, vertices_196, vertices_580, vertices_644, vertices_88, vertices_104, vertices_296, vertices_552, vertices_584, vertices_776, vertices_592, vertices_400, vertices_656, vertices_224, vertices_416, vertices_800] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_403), (false, vertices_659), (false, vertices_803), (false, vertices_709), (false, vertices_617), (false, vertices_481), (true, vertices_26), (true, vertices_266), (true, vertices_522), (true, vertices_28), (true, vertices_44), (true, vertices_76), (true, vertices_268), (true, vertices_84), (true, vertices_148), (true, vertices_276), (true, vertices_532), (true, vertices_164), (true, vertices_292), (true, vertices_88), (true, vertices_296), (true, vertices_776), (true, vertices_592)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 17 21 23 25 26 28 29 30 31
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_403) then 18 else
  if p.val = (false, vertices_659) then 19 else
  if p.val = (false, vertices_803) then 20 else
  if p.val = (false, vertices_709) then 22 else
  if p.val = (false, vertices_617) then 24 else
  if p.val = (false, vertices_481) then 27 else
  if p.val = (true, vertices_26) then 0 else
  if p.val = (true, vertices_266) then 1 else
  if p.val = (true, vertices_522) then 2 else
  if p.val = (true, vertices_28) then 3 else
  if p.val = (true, vertices_44) then 4 else
  if p.val = (true, vertices_76) then 5 else
  if p.val = (true, vertices_268) then 6 else
  if p.val = (true, vertices_84) then 7 else
  if p.val = (true, vertices_148) then 8 else
  if p.val = (true, vertices_276) then 9 else
  if p.val = (true, vertices_532) then 10 else
  if p.val = (true, vertices_164) then 11 else
  if p.val = (true, vertices_292) then 12 else
  if p.val = (true, vertices_88) then 13 else
  if p.val = (true, vertices_296) then 14 else
  if p.val = (true, vertices_776) then 15 else
  if p.val = (true, vertices_592) then 16 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_26), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_266), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_522), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_28), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_44), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_76), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_268), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_84), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_148), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_276), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_532), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_164), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_292), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_88), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_296), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_776), by decide +kernel⟩
  | 16 => Sum.inr ⟨(true, vertices_592), by decide +kernel⟩
  | 17 => Sum.inl 0
  | 18 => Sum.inr ⟨(false, vertices_403), by decide +kernel⟩
  | 19 => Sum.inr ⟨(false, vertices_659), by decide +kernel⟩
  | 20 => Sum.inr ⟨(false, vertices_803), by decide +kernel⟩
  | 21 => Sum.inl 1
  | 22 => Sum.inr ⟨(false, vertices_709), by decide +kernel⟩
  | 23 => Sum.inl 2
  | 24 => Sum.inr ⟨(false, vertices_617), by decide +kernel⟩
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
cert_row_4 0 0 2 3 5 8 602 26 3
cert_row_4 1 0 1 2 3 7 286 26 1
cert_row_4 2 1 2 4 5 6 236 44 3
cert_row_4 3 1 3 4 6 7 436 148 2
cert_rows
cert_pivot_2 8 0 2 1
cert_heightProof 4
cert_coverFacet 0 286
cert_cover_5 0 1 0 1 2 3 26 286 1
cert_coverFacet 1 602
cert_cover_5 1 0 0 2 3 5 26 602 3
cert_coverFacet 2 778
cert_cover_2 2 2 0 7 8 266 778 3
cert_coverFacet 3 92
cert_cover_2 3 2 1 3 5 28 92 3
cert_coverFacet 4 236
cert_cover_5 4 2 1 2 4 5 44 236 3
cert_coverFacet 5 300
cert_cover_2 5 2 1 4 7 44 300 3
cert_coverFacet 6 436
cert_cover_5 6 3 1 3 4 6 148 436 2
cert_coverFacet 7 596
cert_cover_2 7 3 1 5 8 84 596 3
cert_coverFacet 8 660
cert_cover_2 8 3 1 6 8 148 660 3
cert_coverFacet 9 808
cert_cover_2 9 4 2 7 8 296 808 3
cert_coveringFacets_5
cert_coveringProof
cert_certificate 4 10
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0425

end
end BundlePart19

section BundlePart20
/- Source: ProjectionCertificates/R_m16e10q1_0426.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0426

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [59, 339, 803, 837, 89, 553, 713, 182, 406, 550, 774, 460, 740, 696, 344, 408, 19, 35, 259, 25, 41, 73, 521, 81, 545, 321, 577, 769, 150, 38, 262, 518, 50, 274, 546, 770, 164, 548, 196, 324, 580, 388, 772, 56, 88, 152, 280, 552, 200, 328, 392, 648, 176, 336, 400, 672, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_59, vertices_339, vertices_803, vertices_837, vertices_89, vertices_553, vertices_713, vertices_182, vertices_406, vertices_550, vertices_774, vertices_460, vertices_740, vertices_696, vertices_344, vertices_408] (by decide +kernel)
  polygons := literalFinset [vertices_19, vertices_35, vertices_259, vertices_25, vertices_41, vertices_73, vertices_521, vertices_81, vertices_545, vertices_321, vertices_577, vertices_769, vertices_150, vertices_38, vertices_262, vertices_518, vertices_50, vertices_274, vertices_546, vertices_770, vertices_164, vertices_548, vertices_196, vertices_324, vertices_580, vertices_388, vertices_772, vertices_56, vertices_88, vertices_152, vertices_280, vertices_552, vertices_200, vertices_328, vertices_392, vertices_648, vertices_176, vertices_336, vertices_400, vertices_672, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_59), (false, vertices_339), (false, vertices_803), (false, vertices_837), (false, vertices_89), (false, vertices_553), (false, vertices_713), (true, vertices_150), (true, vertices_38), (true, vertices_262), (true, vertices_518), (true, vertices_164), (true, vertices_548), (true, vertices_196), (true, vertices_388), (true, vertices_152), (true, vertices_280), (true, vertices_328), (true, vertices_392), (true, vertices_176), (true, vertices_400), (true, vertices_672)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 19 16 23 25 26 27 28 29 30
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_59) then 20 else
  if p.val = (false, vertices_339) then 21 else
  if p.val = (false, vertices_803) then 22 else
  if p.val = (false, vertices_837) then 17 else
  if p.val = (false, vertices_89) then 0 else
  if p.val = (false, vertices_553) then 1 else
  if p.val = (false, vertices_713) then 24 else
  if p.val = (true, vertices_150) then 18 else
  if p.val = (true, vertices_38) then 2 else
  if p.val = (true, vertices_262) then 3 else
  if p.val = (true, vertices_518) then 4 else
  if p.val = (true, vertices_164) then 5 else
  if p.val = (true, vertices_548) then 6 else
  if p.val = (true, vertices_196) then 7 else
  if p.val = (true, vertices_388) then 8 else
  if p.val = (true, vertices_152) then 9 else
  if p.val = (true, vertices_280) then 10 else
  if p.val = (true, vertices_328) then 11 else
  if p.val = (true, vertices_392) then 12 else
  if p.val = (true, vertices_176) then 13 else
  if p.val = (true, vertices_400) then 14 else
  if p.val = (true, vertices_672) then 15 else
  0
cert_priority
cert_nodeAtPriority_5 1 89 0 553 38 262 518 164 548 196 388 152 280 328 392 176 400 672 837 150 59 339 803 713
cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 1 3 6 150
cert_row_4 1 1 2 5 6 7 460 196 1
cert_row_4 2 1 4 5 6 8 740 164 2
cert_row_4 3 2 3 4 6 8 696 56 3
cert_rows
cert_pivot_2 0 7 1 2
cert_heightProof 4
cert_coverFacet 0 182
cert_cover_5 0 0 0 1 3 4 150 182 3
cert_coverFacet 1 406
cert_cover_5 1 0 0 1 3 7 150 406 3
cert_coverFacet 2 550
cert_cover_2 2 1 0 4 8 38 550 3
cert_coverFacet 3 774
cert_cover_2 3 1 0 7 8 262 774 3
cert_coverFacet 4 460
cert_cover_5 4 1 1 2 5 6 196 460 1
cert_coverFacet 5 740
cert_cover_5 5 2 1 4 5 6 164 740 2
cert_coverFacet 6 696
cert_cover_5 6 3 2 3 4 6 56 696 3
cert_coverFacet 7 344
cert_cover_2 7 3 2 5 7 88 344 3
cert_coverFacet 8 408
cert_cover_2 8 3 2 6 7 152 408 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0426

end
end BundlePart20

section BundlePart21
/- Source: ProjectionCertificates/R_m16e10q1_0427.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0427

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [803, 93, 405, 613, 293, 281, 841, 422, 234, 618, 650, 914, 244, 216, 664, 792, 21, 37, 69, 261, 25, 73, 265, 273, 289, 545, 577, 769, 106, 138, 522, 162, 290, 546, 386, 642, 770, 84, 148, 100, 164, 292, 388, 88, 152, 280, 536, 200, 584, 648, 776, 208, 400, 656, 784, 224, 608]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_803, vertices_93, vertices_405, vertices_613, vertices_293, vertices_281, vertices_841, vertices_422, vertices_234, vertices_618, vertices_650, vertices_914, vertices_244, vertices_216, vertices_664, vertices_792] (by decide +kernel)
  polygons := literalFinset [vertices_21, vertices_37, vertices_69, vertices_261, vertices_25, vertices_73, vertices_265, vertices_273, vertices_289, vertices_545, vertices_577, vertices_769, vertices_106, vertices_138, vertices_522, vertices_162, vertices_290, vertices_546, vertices_386, vertices_642, vertices_770, vertices_84, vertices_148, vertices_100, vertices_164, vertices_292, vertices_388, vertices_88, vertices_152, vertices_280, vertices_536, vertices_200, vertices_584, vertices_648, vertices_776, vertices_208, vertices_400, vertices_656, vertices_784, vertices_224, vertices_608] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_803), (false, vertices_93), (false, vertices_405), (false, vertices_613), (false, vertices_293), (false, vertices_281), (false, vertices_841), (true, vertices_106), (true, vertices_138), (true, vertices_522), (true, vertices_162), (true, vertices_386), (true, vertices_642), (true, vertices_164), (true, vertices_152), (true, vertices_536), (true, vertices_200), (true, vertices_648), (true, vertices_208), (true, vertices_656), (true, vertices_784), (true, vertices_224)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 16 19 23 25 26 27 28 29 30
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_803) then 17 else
  if p.val = (false, vertices_93) then 20 else
  if p.val = (false, vertices_405) then 21 else
  if p.val = (false, vertices_613) then 22 else
  if p.val = (false, vertices_293) then 0 else
  if p.val = (false, vertices_281) then 1 else
  if p.val = (false, vertices_841) then 24 else
  if p.val = (true, vertices_106) then 18 else
  if p.val = (true, vertices_138) then 2 else
  if p.val = (true, vertices_522) then 3 else
  if p.val = (true, vertices_162) then 4 else
  if p.val = (true, vertices_386) then 5 else
  if p.val = (true, vertices_642) then 6 else
  if p.val = (true, vertices_164) then 7 else
  if p.val = (true, vertices_152) then 8 else
  if p.val = (true, vertices_536) then 9 else
  if p.val = (true, vertices_200) then 10 else
  if p.val = (true, vertices_648) then 11 else
  if p.val = (true, vertices_208) then 12 else
  if p.val = (true, vertices_656) then 13 else
  if p.val = (true, vertices_784) then 14 else
  if p.val = (true, vertices_224) then 15 else
  0
cert_priority
cert_nodeAtPriority_5 0 293 1 281 138 522 162 386 642 164 152 536 200 648 208 656 784 224 803 106 93 405 613 841
cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 2 4 5 106
cert_row_4 1 0 3 6 7 8 914 386 1
cert_row_4 2 0 1 4 6 7 422 162 1
cert_row_4 3 1 3 4 5 6 244 84 2
cert_rows
cert_pivot_2 2 8 0 1
cert_heightProof 4
cert_coverFacet 0 422
cert_cover_5 0 2 0 1 4 6 162 422 1
cert_coverFacet 1 234
cert_cover_5 1 0 0 2 4 6 106 234 3
cert_coverFacet 2 618
cert_cover_5 2 0 0 2 4 8 106 618 3
cert_coverFacet 3 650
cert_cover_2 3 2 0 6 8 138 650 3
cert_coverFacet 4 914
cert_cover_5 4 1 0 3 6 7 386 914 1
cert_coverFacet 5 244
cert_cover_5 5 3 1 3 4 5 84 244 2
cert_coverFacet 6 216
cert_cover_2 6 3 2 5 6 88 216 3
cert_coverFacet 7 664
cert_cover_2 7 3 2 6 8 152 664 3
cert_coverFacet 8 792
cert_cover_2 8 3 2 7 8 280 792 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0427

end
end BundlePart21

section BundlePart22
/- Source: ProjectionCertificates/R_m16e10q1_0428.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0428

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [355, 653, 789, 229, 325, 425, 777, 342, 570, 218, 234, 786, 802, 724, 664, 808, 69, 133, 261, 517, 137, 265, 521, 97, 161, 289, 321, 769, 26, 42, 202, 82, 274, 530, 98, 290, 546, 322, 770, 84, 276, 532, 196, 324, 644, 152, 536, 168, 296, 552, 648, 776, 208, 656, 784, 224, 800]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_355, vertices_653, vertices_789, vertices_229, vertices_325, vertices_425, vertices_777, vertices_342, vertices_570, vertices_218, vertices_234, vertices_786, vertices_802, vertices_724, vertices_664, vertices_808] (by decide +kernel)
  polygons := literalFinset [vertices_69, vertices_133, vertices_261, vertices_517, vertices_137, vertices_265, vertices_521, vertices_97, vertices_161, vertices_289, vertices_321, vertices_769, vertices_26, vertices_42, vertices_202, vertices_82, vertices_274, vertices_530, vertices_98, vertices_290, vertices_546, vertices_322, vertices_770, vertices_84, vertices_276, vertices_532, vertices_196, vertices_324, vertices_644, vertices_152, vertices_536, vertices_168, vertices_296, vertices_552, vertices_648, vertices_776, vertices_208, vertices_656, vertices_784, vertices_224, vertices_800] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_355), (false, vertices_653), (false, vertices_789), (false, vertices_229), (false, vertices_325), (false, vertices_425), (false, vertices_777), (true, vertices_26), (true, vertices_42), (true, vertices_202), (true, vertices_82), (true, vertices_274), (true, vertices_530), (true, vertices_546), (true, vertices_770), (true, vertices_84), (true, vertices_152), (true, vertices_536), (true, vertices_552), (true, vertices_208), (true, vertices_656), (true, vertices_800)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 16 19 23 25 26 27 28 29 30
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_355) then 17 else
  if p.val = (false, vertices_653) then 20 else
  if p.val = (false, vertices_789) then 21 else
  if p.val = (false, vertices_229) then 22 else
  if p.val = (false, vertices_325) then 0 else
  if p.val = (false, vertices_425) then 24 else
  if p.val = (false, vertices_777) then 1 else
  if p.val = (true, vertices_26) then 2 else
  if p.val = (true, vertices_42) then 3 else
  if p.val = (true, vertices_202) then 18 else
  if p.val = (true, vertices_82) then 4 else
  if p.val = (true, vertices_274) then 5 else
  if p.val = (true, vertices_530) then 6 else
  if p.val = (true, vertices_546) then 7 else
  if p.val = (true, vertices_770) then 8 else
  if p.val = (true, vertices_84) then 9 else
  if p.val = (true, vertices_152) then 10 else
  if p.val = (true, vertices_536) then 11 else
  if p.val = (true, vertices_552) then 12 else
  if p.val = (true, vertices_208) then 13 else
  if p.val = (true, vertices_656) then 14 else
  if p.val = (true, vertices_800) then 15 else
  0
cert_priority
cert_nodeAtPriority_5 0 325 1 777 26 42 82 274 530 546 770 84 152 536 552 208 656 800 355 202 653 789 229 425
cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 3 5 7 342 82 1
cert_row_4 1 0 2 3 4 8 570 26 3
cert_row_2 2 0 2 5 6 202
cert_row_4 3 1 3 5 6 8 724 84 3
cert_rows
cert_pivot_2 7 4 0 1
cert_heightProof 4
cert_coverFacet 0 342
cert_cover_5 0 0 0 1 3 5 82 342 1
cert_coverFacet 1 570
cert_cover_5 1 1 0 2 3 4 26 570 3
cert_coverFacet 2 218
cert_cover_5 2 2 0 2 3 5 26 218 3
cert_coverFacet 3 234
cert_cover_5 3 2 0 2 4 5 42 234 3
cert_coverFacet 4 786
cert_cover_2 4 3 0 7 8 274 786 3
cert_coverFacet 5 802
cert_cover_2 5 4 0 7 8 290 802 3
cert_coverFacet 6 724
cert_cover_5 6 3 1 3 5 6 84 724 3
cert_coverFacet 7 664
cert_cover_2 7 3 2 6 8 152 664 3
cert_coverFacet 8 808
cert_cover_2 8 4 2 7 8 296 808 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0428

end
end BundlePart22

section BundlePart23
/- Source: ProjectionCertificates/R_m16e10q1_0429.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0429

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [339, 109, 333, 789, 677, 625, 782, 666, 394, 242, 786, 450, 172, 652, 488, 688, 77, 37, 261, 517, 81, 273, 529, 97, 545, 321, 138, 266, 522, 82, 146, 274, 530, 194, 322, 386, 770, 44, 140, 268, 524, 164, 644, 772, 104, 168, 328, 392, 648, 112, 176, 560, 656, 784, 224, 672, 448]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_339, vertices_109, vertices_333, vertices_789, vertices_677, vertices_625, vertices_782, vertices_666, vertices_394, vertices_242, vertices_786, vertices_450, vertices_172, vertices_652, vertices_488, vertices_688] (by decide +kernel)
  polygons := literalFinset [vertices_77, vertices_37, vertices_261, vertices_517, vertices_81, vertices_273, vertices_529, vertices_97, vertices_545, vertices_321, vertices_138, vertices_266, vertices_522, vertices_82, vertices_146, vertices_274, vertices_530, vertices_194, vertices_322, vertices_386, vertices_770, vertices_44, vertices_140, vertices_268, vertices_524, vertices_164, vertices_644, vertices_772, vertices_104, vertices_168, vertices_328, vertices_392, vertices_648, vertices_112, vertices_176, vertices_560, vertices_656, vertices_784, vertices_224, vertices_672, vertices_448] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_339), (false, vertices_109), (false, vertices_333), (false, vertices_789), (false, vertices_677), (false, vertices_625), (true, vertices_138), (true, vertices_266), (true, vertices_522), (true, vertices_146), (true, vertices_530), (true, vertices_194), (true, vertices_386), (true, vertices_770), (true, vertices_140), (true, vertices_524), (true, vertices_168), (true, vertices_392), (true, vertices_648), (true, vertices_176), (true, vertices_656), (true, vertices_224), (true, vertices_448)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 17 22 19 25 27 28 29 30 31
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_339) then 18 else
  if p.val = (false, vertices_109) then 20 else
  if p.val = (false, vertices_333) then 21 else
  if p.val = (false, vertices_789) then 23 else
  if p.val = (false, vertices_677) then 24 else
  if p.val = (false, vertices_625) then 26 else
  if p.val = (true, vertices_138) then 0 else
  if p.val = (true, vertices_266) then 1 else
  if p.val = (true, vertices_522) then 2 else
  if p.val = (true, vertices_146) then 3 else
  if p.val = (true, vertices_530) then 4 else
  if p.val = (true, vertices_194) then 5 else
  if p.val = (true, vertices_386) then 6 else
  if p.val = (true, vertices_770) then 7 else
  if p.val = (true, vertices_140) then 8 else
  if p.val = (true, vertices_524) then 9 else
  if p.val = (true, vertices_168) then 10 else
  if p.val = (true, vertices_392) then 11 else
  if p.val = (true, vertices_648) then 12 else
  if p.val = (true, vertices_176) then 13 else
  if p.val = (true, vertices_656) then 14 else
  if p.val = (true, vertices_224) then 15 else
  if p.val = (true, vertices_448) then 16 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_138), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_266), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_522), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_146), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_530), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_194), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_386), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_770), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_140), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_524), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_168), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_392), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_648), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_176), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_656), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_224), by decide +kernel⟩
  | 16 => Sum.inr ⟨(true, vertices_448), by decide +kernel⟩
  | 17 => Sum.inl 0
  | 18 => Sum.inr ⟨(false, vertices_339), by decide +kernel⟩
  | 19 => Sum.inl 2
  | 20 => Sum.inr ⟨(false, vertices_109), by decide +kernel⟩
  | 21 => Sum.inr ⟨(false, vertices_333), by decide +kernel⟩
  | 22 => Sum.inl 1
  | 23 => Sum.inr ⟨(false, vertices_789), by decide +kernel⟩
  | 24 => Sum.inr ⟨(false, vertices_677), by decide +kernel⟩
  | 25 => Sum.inl 3
  | 26 => Sum.inr ⟨(false, vertices_625), by decide +kernel⟩
  | 27 => Sum.inl 4
  | 28 => Sum.inl 5
  | 29 => Sum.inl 6
  | 30 => Sum.inl 7
  | 31 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 2 7 8 782 266 1
cert_row_4 1 0 2 3 6 8 666 138 2
cert_row_4 2 0 3 4 5 6 242 82 2
cert_row_4 3 2 4 5 6 7 488 104 3
cert_rows
cert_pivot_2 1 8 0 2
cert_heightProof 4
cert_coverFacet 0 782
cert_cover_5 0 0 0 1 2 7 266 782 1
cert_coverFacet 1 666
cert_cover_5 1 1 0 2 3 6 138 666 2
cert_coverFacet 2 394
cert_cover_2 2 2 0 6 7 138 394 3
cert_coverFacet 3 242
cert_cover_5 3 2 0 3 4 5 82 242 2
cert_coverFacet 4 786
cert_cover_2 4 3 0 7 8 274 786 3
cert_coverFacet 5 450
cert_cover_2 5 5 0 6 7 194 450 3
cert_coverFacet 6 172
cert_cover_2 6 2 1 4 6 44 172 3
cert_coverFacet 7 652
cert_cover_2 7 2 1 6 8 140 652 3
cert_coverFacet 8 488
cert_cover_5 8 3 2 4 5 6 104 488 3
cert_coverFacet 9 688
cert_cover_2 9 4 3 6 8 176 688 3
cert_coveringFacets_5
cert_coveringProof
cert_certificate 4 10
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0429

end
end BundlePart23

section BundlePart24
/- Source: ProjectionCertificates/R_m16e10q1_0430.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0430

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [803, 93, 565, 581, 185, 297, 841, 902, 234, 362, 690, 450, 468, 660, 836, 216, 21, 69, 517, 25, 41, 73, 265, 49, 289, 545, 577, 769, 106, 162, 290, 546, 194, 322, 386, 642, 770, 84, 148, 532, 324, 580, 388, 644, 772, 88, 152, 168, 296, 200, 328, 176, 560, 208, 656, 448, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_803, vertices_93, vertices_565, vertices_581, vertices_185, vertices_297, vertices_841, vertices_902, vertices_234, vertices_362, vertices_690, vertices_450, vertices_468, vertices_660, vertices_836, vertices_216] (by decide +kernel)
  polygons := literalFinset [vertices_21, vertices_69, vertices_517, vertices_25, vertices_41, vertices_73, vertices_265, vertices_49, vertices_289, vertices_545, vertices_577, vertices_769, vertices_106, vertices_162, vertices_290, vertices_546, vertices_194, vertices_322, vertices_386, vertices_642, vertices_770, vertices_84, vertices_148, vertices_532, vertices_324, vertices_580, vertices_388, vertices_644, vertices_772, vertices_88, vertices_152, vertices_168, vertices_296, vertices_200, vertices_328, vertices_176, vertices_560, vertices_208, vertices_656, vertices_448, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_803), (false, vertices_93), (false, vertices_565), (false, vertices_581), (false, vertices_185), (false, vertices_297), (false, vertices_841), (true, vertices_106), (true, vertices_162), (true, vertices_194), (true, vertices_322), (true, vertices_386), (true, vertices_642), (true, vertices_148), (true, vertices_324), (true, vertices_388), (true, vertices_644), (true, vertices_772), (true, vertices_200), (true, vertices_208), (true, vertices_656), (true, vertices_448)] (by decide +kernel)
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
  if p.val = (true, vertices_324) then 8 else
  if p.val = (true, vertices_388) then 9 else
  if p.val = (true, vertices_644) then 10 else
  if p.val = (true, vertices_772) then 11 else
  if p.val = (true, vertices_200) then 12 else
  if p.val = (true, vertices_208) then 13 else
  if p.val = (true, vertices_656) then 14 else
  if p.val = (true, vertices_448) then 15 else
  0
cert_priority
cert_nodeAtPriority_39 0 581 1 297 162 194 322 386 642 148 324 388 644 772 200 208 656 448 803 106 93 565 185 841
cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 2 4 5 106
cert_row_4 1 0 3 4 6 8 690 162 1
cert_row_4 2 0 1 6 7 8 902 386 1
cert_row_4 3 1 3 5 6 7 468 84 3
cert_rows
cert_pivot_2 2 4 0 1
cert_heightProof 4
cert_coverFacet 0 902
cert_cover_5 0 2 0 1 6 7 386 902 1
cert_coverFacet 1 234
cert_cover_5 1 0 0 2 4 6 106 234 3
cert_coverFacet 2 362
cert_cover_5 2 0 0 2 4 7 106 362 3
cert_coverFacet 3 690
cert_cover_5 3 1 0 3 4 6 162 690 1
cert_coverFacet 4 450
cert_cover_2 4 5 0 6 7 194 450 3
cert_coverFacet 5 468
cert_cover_5 5 3 1 3 5 6 84 468 3
cert_coverFacet 6 660
cert_cover_2 6 3 1 6 8 148 660 3
cert_coverFacet 7 836
cert_cover_2 7 5 1 7 8 324 836 3
cert_coverFacet 8 216
cert_cover_2 8 3 2 5 6 88 216 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0430

end
end BundlePart24

section BundlePart25
/- Source: ProjectionCertificates/R_m16e10q1_0431.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0431

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [391, 653, 837, 409, 617, 329, 166, 806, 346, 242, 402, 866, 692, 120, 568, 664, 133, 261, 517, 73, 137, 265, 521, 321, 577, 385, 38, 134, 262, 82, 146, 274, 98, 162, 802, 322, 386, 164, 548, 644, 772, 56, 88, 152, 280, 536, 104, 552, 328, 648, 112, 176, 560, 400, 656, 608, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_391, vertices_653, vertices_837, vertices_409, vertices_617, vertices_329, vertices_166, vertices_806, vertices_346, vertices_242, vertices_402, vertices_866, vertices_692, vertices_120, vertices_568, vertices_664] (by decide +kernel)
  polygons := literalFinset [vertices_133, vertices_261, vertices_517, vertices_73, vertices_137, vertices_265, vertices_521, vertices_321, vertices_577, vertices_385, vertices_38, vertices_134, vertices_262, vertices_82, vertices_146, vertices_274, vertices_98, vertices_162, vertices_802, vertices_322, vertices_386, vertices_164, vertices_548, vertices_644, vertices_772, vertices_56, vertices_88, vertices_152, vertices_280, vertices_536, vertices_104, vertices_552, vertices_328, vertices_648, vertices_112, vertices_176, vertices_560, vertices_400, vertices_656, vertices_608, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_391), (false, vertices_653), (false, vertices_837), (false, vertices_409), (false, vertices_617), (false, vertices_329), (true, vertices_38), (true, vertices_82), (true, vertices_146), (true, vertices_274), (true, vertices_98), (true, vertices_162), (true, vertices_802), (true, vertices_322), (true, vertices_164), (true, vertices_548), (true, vertices_56), (true, vertices_88), (true, vertices_536), (true, vertices_112), (true, vertices_176), (true, vertices_560), (true, vertices_656)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 17 20 23 26 27 28 29 30 31
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_391) then 18 else
  if p.val = (false, vertices_653) then 21 else
  if p.val = (false, vertices_837) then 22 else
  if p.val = (false, vertices_409) then 24 else
  if p.val = (false, vertices_617) then 25 else
  if p.val = (false, vertices_329) then 0 else
  if p.val = (true, vertices_38) then 1 else
  if p.val = (true, vertices_82) then 2 else
  if p.val = (true, vertices_146) then 3 else
  if p.val = (true, vertices_274) then 4 else
  if p.val = (true, vertices_98) then 5 else
  if p.val = (true, vertices_162) then 6 else
  if p.val = (true, vertices_802) then 19 else
  if p.val = (true, vertices_322) then 7 else
  if p.val = (true, vertices_164) then 8 else
  if p.val = (true, vertices_548) then 9 else
  if p.val = (true, vertices_56) then 10 else
  if p.val = (true, vertices_88) then 11 else
  if p.val = (true, vertices_536) then 12 else
  if p.val = (true, vertices_112) then 13 else
  if p.val = (true, vertices_176) then 14 else
  if p.val = (true, vertices_560) then 15 else
  if p.val = (true, vertices_656) then 16 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_329), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_38), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_82), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_146), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_274), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_98), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_162), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_322), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_164), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_548), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_56), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_88), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_536), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_112), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_176), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_560), by decide +kernel⟩
  | 16 => Sum.inr ⟨(true, vertices_656), by decide +kernel⟩
  | 17 => Sum.inl 0
  | 18 => Sum.inr ⟨(false, vertices_391), by decide +kernel⟩
  | 19 => Sum.inr ⟨(true, vertices_802), by decide +kernel⟩
  | 20 => Sum.inl 1
  | 21 => Sum.inr ⟨(false, vertices_653), by decide +kernel⟩
  | 22 => Sum.inr ⟨(false, vertices_837), by decide +kernel⟩
  | 23 => Sum.inl 2
  | 24 => Sum.inr ⟨(false, vertices_409), by decide +kernel⟩
  | 25 => Sum.inr ⟨(false, vertices_617), by decide +kernel⟩
  | 26 => Sum.inl 3
  | 27 => Sum.inl 4
  | 28 => Sum.inl 5
  | 29 => Sum.inl 6
  | 30 => Sum.inl 7
  | 31 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 2 3 5 7 346 82 1
cert_row_2 1 0 4 7 8 802
cert_row_4 2 0 3 4 5 6 242 82 2
cert_row_4 3 1 3 4 6 8 692 164 1
cert_rows
cert_pivot_2 2 7 0 1
cert_heightProof 4
cert_coverFacet 0 166
cert_cover_2 0 1 0 4 6 38 166 3
cert_coverFacet 1 806
cert_cover_5 1 1 0 1 4 7 38 806 3
cert_coverFacet 2 346
cert_cover_5 2 0 0 2 3 5 82 346 1
cert_coverFacet 3 242
cert_cover_5 3 2 0 3 4 5 82 242 2
cert_coverFacet 4 402
cert_cover_2 4 3 0 6 7 146 402 3
cert_coverFacet 5 866
cert_cover_5 5 1 0 4 5 7 98 866 3
cert_coverFacet 6 692
cert_cover_5 6 3 1 3 4 6 164 692 1
cert_coverFacet 7 120
cert_cover_2 7 3 2 4 5 56 120 3
cert_coverFacet 8 568
cert_cover_2 8 3 2 4 8 56 568 3
cert_coverFacet 9 664
cert_cover_2 9 3 2 6 8 152 664 3
cert_coveringFacets_5
cert_coveringProof
cert_certificate 4 10
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0431

end
end BundlePart25

section BundlePart26
/- Source: ProjectionCertificates/R_m16e10q1_0432.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0432

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [327, 395, 611, 643, 173, 269, 101, 689, 722, 450, 812, 852, 612, 184, 824, 472, 67, 131, 259, 515, 13, 37, 69, 261, 137, 265, 97, 161, 545, 641, 194, 322, 578, 386, 642, 44, 268, 100, 548, 324, 580, 772, 56, 152, 280, 168, 808, 392, 176, 560, 208, 336, 592, 656, 784, 608, 448]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_327, vertices_395, vertices_611, vertices_643, vertices_173, vertices_269, vertices_101, vertices_689, vertices_722, vertices_450, vertices_812, vertices_852, vertices_612, vertices_184, vertices_824, vertices_472] (by decide +kernel)
  polygons := literalFinset [vertices_67, vertices_131, vertices_259, vertices_515, vertices_13, vertices_37, vertices_69, vertices_261, vertices_137, vertices_265, vertices_97, vertices_161, vertices_545, vertices_641, vertices_194, vertices_322, vertices_578, vertices_386, vertices_642, vertices_44, vertices_268, vertices_100, vertices_548, vertices_324, vertices_580, vertices_772, vertices_56, vertices_152, vertices_280, vertices_168, vertices_808, vertices_392, vertices_176, vertices_560, vertices_208, vertices_336, vertices_592, vertices_656, vertices_784, vertices_608, vertices_448] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_327), (false, vertices_395), (false, vertices_611), (false, vertices_643), (false, vertices_173), (false, vertices_269), (false, vertices_101), (false, vertices_689), (true, vertices_194), (true, vertices_548), (true, vertices_580), (true, vertices_772), (true, vertices_56), (true, vertices_152), (true, vertices_280), (true, vertices_808), (true, vertices_208), (true, vertices_336), (true, vertices_592), (true, vertices_784), (true, vertices_448)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 19 21 23 25 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_327) then 16 else
  if p.val = (false, vertices_395) then 17 else
  if p.val = (false, vertices_611) then 18 else
  if p.val = (false, vertices_643) then 0 else
  if p.val = (false, vertices_173) then 20 else
  if p.val = (false, vertices_269) then 1 else
  if p.val = (false, vertices_101) then 2 else
  if p.val = (false, vertices_689) then 24 else
  if p.val = (true, vertices_194) then 3 else
  if p.val = (true, vertices_548) then 4 else
  if p.val = (true, vertices_580) then 5 else
  if p.val = (true, vertices_772) then 6 else
  if p.val = (true, vertices_56) then 7 else
  if p.val = (true, vertices_152) then 8 else
  if p.val = (true, vertices_280) then 9 else
  if p.val = (true, vertices_808) then 22 else
  if p.val = (true, vertices_208) then 10 else
  if p.val = (true, vertices_336) then 11 else
  if p.val = (true, vertices_592) then 12 else
  if p.val = (true, vertices_784) then 13 else
  if p.val = (true, vertices_448) then 14 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_643), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_269), by decide +kernel⟩
  | 2 => Sum.inr ⟨(false, vertices_101), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_194), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_548), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_580), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_772), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_56), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_152), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_280), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_208), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_336), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_592), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_784), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_448), by decide +kernel⟩
  | 15 => Sum.inl 0
  | 16 => Sum.inr ⟨(false, vertices_327), by decide +kernel⟩
  | 17 => Sum.inr ⟨(false, vertices_395), by decide +kernel⟩
  | 18 => Sum.inr ⟨(false, vertices_611), by decide +kernel⟩
  | 19 => Sum.inl 1
  | 20 => Sum.inr ⟨(false, vertices_173), by decide +kernel⟩
  | 21 => Sum.inl 2
  | 22 => Sum.inr ⟨(true, vertices_808), by decide +kernel⟩
  | 23 => Sum.inl 3
  | 24 => Sum.inr ⟨(false, vertices_689), by decide +kernel⟩
  | 25 => Sum.inl 4
  | 26 => Sum.inl 5
  | 27 => Sum.inl 6
  | 28 => Sum.inl 7
  | 29 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 2 4 7 8 808
cert_row_4 1 0 3 5 6 8 722 194 1
cert_row_4 2 1 3 5 7 8 852 324 1
cert_row_4 3 2 3 5 6 7 472 152 2
cert_rows
cert_pivot_2 4 0 1 2
cert_heightProof 4
cert_coverFacet 0 722
cert_cover_5 0 1 0 3 5 6 194 722 1
cert_coverFacet 1 450
cert_cover_2 1 5 0 6 7 194 450 3
cert_coverFacet 2 812
cert_cover_5 2 0 1 2 4 7 44 812 3
cert_coverFacet 3 852
cert_cover_5 3 2 1 3 5 7 324 852 1
cert_coverFacet 4 612
cert_cover_2 4 4 1 5 8 100 612 3
cert_coverFacet 5 184
cert_cover_2 5 3 2 4 6 56 184 3
cert_coverFacet 6 824
cert_cover_5 6 0 2 3 4 7 56 824 3
cert_coverFacet 7 472
cert_cover_5 7 3 2 3 5 6 152 472 2
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0432

end
end BundlePart26

section BundlePart27
/- Source: ProjectionCertificates/R_m16e10q1_0433.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0433

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [391, 653, 837, 345, 617, 393, 166, 806, 410, 242, 338, 866, 692, 120, 568, 664, 133, 261, 517, 73, 137, 265, 521, 321, 577, 385, 38, 134, 262, 82, 146, 274, 98, 162, 802, 322, 386, 164, 548, 644, 772, 56, 88, 152, 280, 536, 104, 552, 392, 648, 112, 176, 560, 336, 656, 608, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_391, vertices_653, vertices_837, vertices_345, vertices_617, vertices_393, vertices_166, vertices_806, vertices_410, vertices_242, vertices_338, vertices_866, vertices_692, vertices_120, vertices_568, vertices_664] (by decide +kernel)
  polygons := literalFinset [vertices_133, vertices_261, vertices_517, vertices_73, vertices_137, vertices_265, vertices_521, vertices_321, vertices_577, vertices_385, vertices_38, vertices_134, vertices_262, vertices_82, vertices_146, vertices_274, vertices_98, vertices_162, vertices_802, vertices_322, vertices_386, vertices_164, vertices_548, vertices_644, vertices_772, vertices_56, vertices_88, vertices_152, vertices_280, vertices_536, vertices_104, vertices_552, vertices_392, vertices_648, vertices_112, vertices_176, vertices_560, vertices_336, vertices_656, vertices_608, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_391), (false, vertices_653), (false, vertices_837), (false, vertices_345), (false, vertices_617), (false, vertices_393), (true, vertices_38), (true, vertices_82), (true, vertices_146), (true, vertices_274), (true, vertices_98), (true, vertices_162), (true, vertices_802), (true, vertices_322), (true, vertices_164), (true, vertices_548), (true, vertices_56), (true, vertices_152), (true, vertices_536), (true, vertices_112), (true, vertices_176), (true, vertices_560), (true, vertices_656)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 17 20 23 26 27 28 29 30 31
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_391) then 18 else
  if p.val = (false, vertices_653) then 21 else
  if p.val = (false, vertices_837) then 22 else
  if p.val = (false, vertices_345) then 24 else
  if p.val = (false, vertices_617) then 25 else
  if p.val = (false, vertices_393) then 0 else
  if p.val = (true, vertices_38) then 1 else
  if p.val = (true, vertices_82) then 2 else
  if p.val = (true, vertices_146) then 3 else
  if p.val = (true, vertices_274) then 4 else
  if p.val = (true, vertices_98) then 5 else
  if p.val = (true, vertices_162) then 6 else
  if p.val = (true, vertices_802) then 19 else
  if p.val = (true, vertices_322) then 7 else
  if p.val = (true, vertices_164) then 8 else
  if p.val = (true, vertices_548) then 9 else
  if p.val = (true, vertices_56) then 10 else
  if p.val = (true, vertices_152) then 11 else
  if p.val = (true, vertices_536) then 12 else
  if p.val = (true, vertices_112) then 13 else
  if p.val = (true, vertices_176) then 14 else
  if p.val = (true, vertices_560) then 15 else
  if p.val = (true, vertices_656) then 16 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_393), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_38), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_82), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_146), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_274), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_98), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_162), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_322), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_164), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_548), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_56), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_152), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_536), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_112), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_176), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_560), by decide +kernel⟩
  | 16 => Sum.inr ⟨(true, vertices_656), by decide +kernel⟩
  | 17 => Sum.inl 0
  | 18 => Sum.inr ⟨(false, vertices_391), by decide +kernel⟩
  | 19 => Sum.inr ⟨(true, vertices_802), by decide +kernel⟩
  | 20 => Sum.inl 1
  | 21 => Sum.inr ⟨(false, vertices_653), by decide +kernel⟩
  | 22 => Sum.inr ⟨(false, vertices_837), by decide +kernel⟩
  | 23 => Sum.inl 2
  | 24 => Sum.inr ⟨(false, vertices_345), by decide +kernel⟩
  | 25 => Sum.inr ⟨(false, vertices_617), by decide +kernel⟩
  | 26 => Sum.inl 3
  | 27 => Sum.inl 4
  | 28 => Sum.inl 5
  | 29 => Sum.inl 6
  | 30 => Sum.inl 7
  | 31 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 2 3 6 7 410 146 1
cert_row_2 1 0 4 7 8 802
cert_row_4 2 0 3 4 5 6 242 82 2
cert_row_4 3 1 3 4 6 8 692 164 1
cert_rows
cert_pivot_2 2 7 0 1
cert_heightProof 4
cert_coverFacet 0 166
cert_cover_2 0 1 0 4 6 38 166 3
cert_coverFacet 1 806
cert_cover_5 1 1 0 1 4 7 38 806 3
cert_coverFacet 2 410
cert_cover_5 2 0 0 2 3 6 146 410 1
cert_coverFacet 3 242
cert_cover_5 3 2 0 3 4 5 82 242 2
cert_coverFacet 4 338
cert_cover_2 4 3 0 5 7 82 338 3
cert_coverFacet 5 866
cert_cover_5 5 1 0 4 5 7 98 866 3
cert_coverFacet 6 692
cert_cover_5 6 3 1 3 4 6 164 692 1
cert_coverFacet 7 120
cert_cover_2 7 3 2 4 5 56 120 3
cert_coverFacet 8 568
cert_cover_2 8 3 2 4 8 56 568 3
cert_coverFacet 9 664
cert_cover_2 9 3 2 6 8 152 664 3
cert_coveringFacets_5
cert_coveringProof
cert_certificate 4 10
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0433

end
end BundlePart27

section BundlePart28
/- Source: ProjectionCertificates/R_m16e10q1_0434.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0434

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [595, 301, 205, 165, 793, 585, 465, 417, 678, 714, 370, 562, 482, 652, 780, 820, 13, 37, 133, 73, 265, 521, 81, 273, 529, 161, 289, 193, 577, 385, 50, 82, 530, 354, 162, 546, 194, 578, 642, 140, 268, 524, 164, 292, 548, 644, 772, 200, 584, 648, 776, 304, 560, 336, 784, 416, 448]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_595, vertices_301, vertices_205, vertices_165, vertices_793, vertices_585, vertices_465, vertices_417, vertices_678, vertices_714, vertices_370, vertices_562, vertices_482, vertices_652, vertices_780, vertices_820] (by decide +kernel)
  polygons := literalFinset [vertices_13, vertices_37, vertices_133, vertices_73, vertices_265, vertices_521, vertices_81, vertices_273, vertices_529, vertices_161, vertices_289, vertices_193, vertices_577, vertices_385, vertices_50, vertices_82, vertices_530, vertices_354, vertices_162, vertices_546, vertices_194, vertices_578, vertices_642, vertices_140, vertices_268, vertices_524, vertices_164, vertices_292, vertices_548, vertices_644, vertices_772, vertices_200, vertices_584, vertices_648, vertices_776, vertices_304, vertices_560, vertices_336, vertices_784, vertices_416, vertices_448] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_595), (false, vertices_301), (false, vertices_205), (false, vertices_165), (false, vertices_793), (false, vertices_585), (false, vertices_465), (false, vertices_417), (true, vertices_50), (true, vertices_354), (true, vertices_162), (true, vertices_546), (true, vertices_194), (true, vertices_642), (true, vertices_524), (true, vertices_548), (true, vertices_644), (true, vertices_772), (true, vertices_648), (true, vertices_304), (true, vertices_560)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 18 21 23 25 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_595) then 16 else
  if p.val = (false, vertices_301) then 19 else
  if p.val = (false, vertices_205) then 20 else
  if p.val = (false, vertices_165) then 0 else
  if p.val = (false, vertices_793) then 22 else
  if p.val = (false, vertices_585) then 1 else
  if p.val = (false, vertices_465) then 24 else
  if p.val = (false, vertices_417) then 2 else
  if p.val = (true, vertices_50) then 3 else
  if p.val = (true, vertices_354) then 17 else
  if p.val = (true, vertices_162) then 4 else
  if p.val = (true, vertices_546) then 5 else
  if p.val = (true, vertices_194) then 6 else
  if p.val = (true, vertices_642) then 7 else
  if p.val = (true, vertices_524) then 8 else
  if p.val = (true, vertices_548) then 9 else
  if p.val = (true, vertices_644) then 10 else
  if p.val = (true, vertices_772) then 11 else
  if p.val = (true, vertices_648) then 12 else
  if p.val = (true, vertices_304) then 13 else
  if p.val = (true, vertices_560) then 14 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_165), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_585), by decide +kernel⟩
  | 2 => Sum.inr ⟨(false, vertices_417), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_50), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_162), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_546), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_194), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_642), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_524), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_548), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_644), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_772), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_648), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_304), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_560), by decide +kernel⟩
  | 15 => Sum.inl 0
  | 16 => Sum.inr ⟨(false, vertices_595), by decide +kernel⟩
  | 17 => Sum.inr ⟨(true, vertices_354), by decide +kernel⟩
  | 18 => Sum.inl 1
  | 19 => Sum.inr ⟨(false, vertices_301), by decide +kernel⟩
  | 20 => Sum.inr ⟨(false, vertices_205), by decide +kernel⟩
  | 21 => Sum.inl 2
  | 22 => Sum.inr ⟨(false, vertices_793), by decide +kernel⟩
  | 23 => Sum.inl 3
  | 24 => Sum.inr ⟨(false, vertices_465), by decide +kernel⟩
  | 25 => Sum.inl 4
  | 26 => Sum.inl 5
  | 27 => Sum.inl 6
  | 28 => Sum.inl 7
  | 29 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 2 5 6 8 714 194 1
cert_row_2 1 0 4 5 7 354
cert_row_4 2 0 1 4 6 8 678 162 1
cert_row_4 3 1 3 4 7 8 820 292 1
cert_rows
cert_pivot_2 2 5 0 1
cert_heightProof 4
cert_coverFacet 0 678
cert_cover_5 0 2 0 1 4 6 162 678 1
cert_coverFacet 1 714
cert_cover_5 1 0 0 2 5 6 194 714 1
cert_coverFacet 2 370
cert_cover_5 2 1 0 3 4 5 50 370 3
cert_coverFacet 3 562
cert_cover_2 3 3 0 4 8 50 562 3
cert_coverFacet 4 482
cert_cover_5 4 1 0 4 5 6 354 482 3
cert_coverFacet 5 652
cert_cover_2 5 2 1 6 8 140 652 3
cert_coverFacet 6 780
cert_cover_2 6 2 1 7 8 268 780 3
cert_coverFacet 7 820
cert_cover_5 7 3 1 3 4 7 292 820 1
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0434

end
end BundlePart28

section BundlePart29
/- Source: ProjectionCertificates/R_m16e10q1_0435.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0435

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [775, 405, 709, 665, 281, 809, 590, 230, 422, 122, 554, 802, 312, 600, 496, 720, 133, 261, 517, 25, 265, 521, 145, 273, 641, 769, 166, 70, 262, 518, 42, 74, 522, 98, 290, 546, 770, 196, 580, 388, 56, 88, 280, 536, 296, 552, 584, 112, 304, 208, 592, 400, 656, 224, 416, 800, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_775, vertices_405, vertices_709, vertices_665, vertices_281, vertices_809, vertices_590, vertices_230, vertices_422, vertices_122, vertices_554, vertices_802, vertices_312, vertices_600, vertices_496, vertices_720] (by decide +kernel)
  polygons := literalFinset [vertices_133, vertices_261, vertices_517, vertices_25, vertices_265, vertices_521, vertices_145, vertices_273, vertices_641, vertices_769, vertices_166, vertices_70, vertices_262, vertices_518, vertices_42, vertices_74, vertices_522, vertices_98, vertices_290, vertices_546, vertices_770, vertices_196, vertices_580, vertices_388, vertices_56, vertices_88, vertices_280, vertices_536, vertices_296, vertices_552, vertices_584, vertices_112, vertices_304, vertices_208, vertices_592, vertices_400, vertices_656, vertices_224, vertices_416, vertices_800, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_775), (false, vertices_405), (false, vertices_709), (false, vertices_665), (false, vertices_281), (false, vertices_809), (true, vertices_166), (true, vertices_70), (true, vertices_42), (true, vertices_74), (true, vertices_522), (true, vertices_98), (true, vertices_290), (true, vertices_546), (true, vertices_56), (true, vertices_88), (true, vertices_584), (true, vertices_112), (true, vertices_304), (true, vertices_208), (true, vertices_592), (true, vertices_224), (true, vertices_416)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 17 20 23 26 27 28 29 30 31
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_775) then 18 else
  if p.val = (false, vertices_405) then 21 else
  if p.val = (false, vertices_709) then 22 else
  if p.val = (false, vertices_665) then 24 else
  if p.val = (false, vertices_281) then 0 else
  if p.val = (false, vertices_809) then 25 else
  if p.val = (true, vertices_166) then 19 else
  if p.val = (true, vertices_70) then 1 else
  if p.val = (true, vertices_42) then 2 else
  if p.val = (true, vertices_74) then 3 else
  if p.val = (true, vertices_522) then 4 else
  if p.val = (true, vertices_98) then 5 else
  if p.val = (true, vertices_290) then 6 else
  if p.val = (true, vertices_546) then 7 else
  if p.val = (true, vertices_56) then 8 else
  if p.val = (true, vertices_88) then 9 else
  if p.val = (true, vertices_584) then 10 else
  if p.val = (true, vertices_112) then 11 else
  if p.val = (true, vertices_304) then 12 else
  if p.val = (true, vertices_208) then 13 else
  if p.val = (true, vertices_592) then 14 else
  if p.val = (true, vertices_224) then 15 else
  if p.val = (true, vertices_416) then 16 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_281), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_70), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_42), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_74), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_522), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_98), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_290), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_546), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_56), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_88), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_584), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_112), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_304), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_208), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_592), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_224), by decide +kernel⟩
  | 16 => Sum.inr ⟨(true, vertices_416), by decide +kernel⟩
  | 17 => Sum.inl 0
  | 18 => Sum.inr ⟨(false, vertices_775), by decide +kernel⟩
  | 19 => Sum.inr ⟨(true, vertices_166), by decide +kernel⟩
  | 20 => Sum.inl 1
  | 21 => Sum.inr ⟨(false, vertices_405), by decide +kernel⟩
  | 22 => Sum.inr ⟨(false, vertices_709), by decide +kernel⟩
  | 23 => Sum.inl 2
  | 24 => Sum.inr ⟨(false, vertices_665), by decide +kernel⟩
  | 25 => Sum.inr ⟨(false, vertices_809), by decide +kernel⟩
  | 26 => Sum.inl 3
  | 27 => Sum.inl 4
  | 28 => Sum.inl 5
  | 29 => Sum.inl 6
  | 30 => Sum.inl 7
  | 31 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 2 5 8 590 70 2
cert_row_2 1 0 1 4 6 166
cert_row_4 2 0 2 3 4 5 122 42 2
cert_row_4 3 3 4 5 6 7 496 112 3
cert_rows
cert_pivot_2 8 1 0 3
cert_heightProof 4
cert_coverFacet 0 590
cert_cover_5 0 0 0 1 2 5 70 590 2
cert_coverFacet 1 230
cert_cover_5 1 1 0 1 4 5 166 230 3
cert_coverFacet 2 422
cert_cover_5 2 1 0 1 4 7 166 422 3
cert_coverFacet 3 122
cert_cover_5 3 2 0 2 3 4 42 122 2
cert_coverFacet 4 554
cert_cover_2 4 2 0 4 8 42 554 3
cert_coverFacet 5 802
cert_cover_2 5 4 0 7 8 290 802 3
cert_coverFacet 6 312
cert_cover_2 6 3 2 4 7 56 312 3
cert_coverFacet 7 600
cert_cover_2 7 3 2 5 8 88 600 3
cert_coverFacet 8 496
cert_cover_5 8 3 3 4 5 6 112 496 3
cert_coverFacet 9 720
cert_cover_2 9 5 3 6 8 208 720 3
cert_coveringFacets_5
cert_coveringProof
cert_certificate 4 10
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0435

end
end BundlePart29

-- Public target certificates; internal witness data stays private.
namespace Nonrational.TerminalVerification
open Papers.RationalityTen.ChirotopeDensity.FiniteProjection
open Nonrational.TerminalData
set_option maxRecDepth 100000
set_option maxHeartbeats 0

public theorem projection_4293 : Certifies 4293 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0406.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_4294 : Certifies 4294 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0407.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_4295 : Certifies 4295 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0408.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_4296 : Certifies 4296 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0409.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_4297 : Certifies 4297 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0410.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_4298 : Certifies 4298 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0411.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_4299 : Certifies 4299 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0412.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_4300 : Certifies 4300 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0413.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_4301 : Certifies 4301 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0414.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_4302 : Certifies 4302 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0415.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_4303 : Certifies 4303 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0416.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_4304 : Certifies 4304 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0417.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_4305 : Certifies 4305 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0418.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_4306 : Certifies 4306 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0419.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_4307 : Certifies 4307 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0420.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_4308 : Certifies 4308 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0421.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_4309 : Certifies 4309 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0422.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_4310 : Certifies 4310 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0423.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_4311 : Certifies 4311 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0424.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_4312 : Certifies 4312 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0425.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_4313 : Certifies 4313 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0426.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_4314 : Certifies 4314 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0427.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_4315 : Certifies 4315 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0428.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_4316 : Certifies 4316 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0429.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_4317 : Certifies 4317 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0430.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_4318 : Certifies 4318 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0431.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_4319 : Certifies 4319 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0432.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_4320 : Certifies 4320 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0433.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_4321 : Certifies 4321 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0434.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_4322 : Certifies 4322 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0435.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem certified_B142 (j : Fin 30) :
    Certifies (4293 + j.val) := by
  fin_cases j
  · exact projection_4293
  · exact projection_4294
  · exact projection_4295
  · exact projection_4296
  · exact projection_4297
  · exact projection_4298
  · exact projection_4299
  · exact projection_4300
  · exact projection_4301
  · exact projection_4302
  · exact projection_4303
  · exact projection_4304
  · exact projection_4305
  · exact projection_4306
  · exact projection_4307
  · exact projection_4308
  · exact projection_4309
  · exact projection_4310
  · exact projection_4311
  · exact projection_4312
  · exact projection_4313
  · exact projection_4314
  · exact projection_4315
  · exact projection_4316
  · exact projection_4317
  · exact projection_4318
  · exact projection_4319
  · exact projection_4320
  · exact projection_4321
  · exact projection_4322

end Nonrational.TerminalVerification
-- Explicit facial frame witnesses, with lexical vector tracking.
