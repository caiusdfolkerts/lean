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
/- Source: ProjectionCertificates/R_m16e10q1_0741.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0741

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [551, 403, 227, 771, 345, 209, 865, 398, 166, 774, 668, 844, 692, 632, 408, 240, 35, 131, 259, 515, 81, 145, 273, 97, 545, 193, 321, 769, 38, 134, 262, 518, 162, 386, 770, 140, 268, 524, 660, 164, 548, 772, 88, 152, 280, 536, 328, 584, 392, 112, 176, 560, 208, 400, 224, 608, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_551, vertices_403, vertices_227, vertices_771, vertices_345, vertices_209, vertices_865, vertices_398, vertices_166, vertices_774, vertices_668, vertices_844, vertices_692, vertices_632, vertices_408, vertices_240] (by decide +kernel)
  polygons := literalFinset [vertices_35, vertices_131, vertices_259, vertices_515, vertices_81, vertices_145, vertices_273, vertices_97, vertices_545, vertices_193, vertices_321, vertices_769, vertices_38, vertices_134, vertices_262, vertices_518, vertices_162, vertices_386, vertices_770, vertices_140, vertices_268, vertices_524, vertices_660, vertices_164, vertices_548, vertices_772, vertices_88, vertices_152, vertices_280, vertices_536, vertices_328, vertices_584, vertices_392, vertices_112, vertices_176, vertices_560, vertices_208, vertices_400, vertices_224, vertices_608, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_551), (false, vertices_403), (false, vertices_227), (false, vertices_771), (false, vertices_345), (false, vertices_209), (false, vertices_865), (true, vertices_134), (true, vertices_262), (true, vertices_140), (true, vertices_268), (true, vertices_524), (true, vertices_660), (true, vertices_164), (true, vertices_772), (true, vertices_152), (true, vertices_536), (true, vertices_584), (true, vertices_392), (true, vertices_112), (true, vertices_176), (true, vertices_560)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 16 20 22 24 25 27 28 29 30
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_551) then 17 else
  if p.val = (false, vertices_403) then 18 else
  if p.val = (false, vertices_227) then 19 else
  if p.val = (false, vertices_771) then 0 else
  if p.val = (false, vertices_345) then 23 else
  if p.val = (false, vertices_209) then 1 else
  if p.val = (false, vertices_865) then 26 else
  if p.val = (true, vertices_134) then 2 else
  if p.val = (true, vertices_262) then 3 else
  if p.val = (true, vertices_140) then 4 else
  if p.val = (true, vertices_268) then 5 else
  if p.val = (true, vertices_524) then 6 else
  if p.val = (true, vertices_660) then 21 else
  if p.val = (true, vertices_164) then 7 else
  if p.val = (true, vertices_772) then 8 else
  if p.val = (true, vertices_152) then 9 else
  if p.val = (true, vertices_536) then 10 else
  if p.val = (true, vertices_584) then 11 else
  if p.val = (true, vertices_392) then 12 else
  if p.val = (true, vertices_112) then 13 else
  if p.val = (true, vertices_176) then 14 else
  if p.val = (true, vertices_560) then 15 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_771), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_209), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_134), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_262), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_140), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_268), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_524), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_164), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_772), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_152), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_536), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_584), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_392), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_112), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_176), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_560), by decide +kernel⟩
  | 16 => Sum.inl 0
  | 17 => Sum.inr ⟨(false, vertices_551), by decide +kernel⟩
  | 18 => Sum.inr ⟨(false, vertices_403), by decide +kernel⟩
  | 19 => Sum.inr ⟨(false, vertices_227), by decide +kernel⟩
  | 20 => Sum.inl 1
  | 21 => Sum.inr ⟨(true, vertices_660), by decide +kernel⟩
  | 22 => Sum.inl 2
  | 23 => Sum.inr ⟨(false, vertices_345), by decide +kernel⟩
  | 24 => Sum.inl 3
  | 25 => Sum.inl 4
  | 26 => Sum.inr ⟨(false, vertices_865), by decide +kernel⟩
  | 27 => Sum.inl 5
  | 28 => Sum.inl 6
  | 29 => Sum.inl 7
  | 30 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 2 6 7 398 134 2
cert_row_2 1 1 3 6 8 660
cert_row_4 2 1 2 5 7 8 844 268 2
cert_row_4 3 2 3 4 5 8 632 88 2
cert_rows
cert_pivot_2 0 6 1 2
cert_heightProof 4
cert_coverFacet 0 398
cert_cover_5 0 0 0 1 2 6 134 398 2
cert_coverFacet 1 166
cert_cover_2 1 1 0 4 6 38 166 3
cert_coverFacet 2 774
cert_cover_2 2 1 0 7 8 262 774 3
cert_coverFacet 3 668
cert_cover_5 3 1 1 2 3 6 140 668 2
cert_coverFacet 4 844
cert_cover_5 4 2 1 2 5 7 268 844 2
cert_coverFacet 5 692
cert_cover_5 5 1 1 3 4 6 660 692 2
cert_coverFacet 6 632
cert_cover_5 6 3 2 3 4 5 88 632 2
cert_coverFacet 7 408
cert_cover_2 7 3 2 6 7 152 408 3
cert_coverFacet 8 240
cert_cover_2 8 4 3 5 6 112 240 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0741

end
end BundlePart0

section BundlePart1
/- Source: ProjectionCertificates/R_m16e10q1_0742.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0742

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [199, 331, 803, 643, 61, 93, 677, 297, 914, 450, 180, 468, 696, 600, 872, 848, 67, 131, 259, 515, 29, 37, 69, 133, 41, 73, 265, 289, 545, 641, 194, 322, 386, 642, 770, 52, 84, 148, 164, 196, 56, 88, 536, 296, 552, 328, 584, 176, 336, 592, 400, 656, 784, 672, 800, 448, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_199, vertices_331, vertices_803, vertices_643, vertices_61, vertices_93, vertices_677, vertices_297, vertices_914, vertices_450, vertices_180, vertices_468, vertices_696, vertices_600, vertices_872, vertices_848] (by decide +kernel)
  polygons := literalFinset [vertices_67, vertices_131, vertices_259, vertices_515, vertices_29, vertices_37, vertices_69, vertices_133, vertices_41, vertices_73, vertices_265, vertices_289, vertices_545, vertices_641, vertices_194, vertices_322, vertices_386, vertices_642, vertices_770, vertices_52, vertices_84, vertices_148, vertices_164, vertices_196, vertices_56, vertices_88, vertices_536, vertices_296, vertices_552, vertices_328, vertices_584, vertices_176, vertices_336, vertices_592, vertices_400, vertices_656, vertices_784, vertices_672, vertices_800, vertices_448, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_199), (false, vertices_331), (false, vertices_803), (false, vertices_643), (false, vertices_61), (false, vertices_93), (false, vertices_677), (false, vertices_297), (true, vertices_386), (true, vertices_148), (true, vertices_536), (true, vertices_552), (true, vertices_584), (true, vertices_176), (true, vertices_336), (true, vertices_592), (true, vertices_400), (true, vertices_656), (true, vertices_784), (true, vertices_448), (true, vertices_832)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 19 23 24 25 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_199) then 16 else
  if p.val = (false, vertices_331) then 17 else
  if p.val = (false, vertices_803) then 18 else
  if p.val = (false, vertices_643) then 0 else
  if p.val = (false, vertices_61) then 20 else
  if p.val = (false, vertices_93) then 21 else
  if p.val = (false, vertices_677) then 22 else
  if p.val = (false, vertices_297) then 1 else
  if p.val = (true, vertices_386) then 2 else
  if p.val = (true, vertices_148) then 3 else
  if p.val = (true, vertices_536) then 4 else
  if p.val = (true, vertices_552) then 5 else
  if p.val = (true, vertices_584) then 6 else
  if p.val = (true, vertices_176) then 7 else
  if p.val = (true, vertices_336) then 8 else
  if p.val = (true, vertices_592) then 9 else
  if p.val = (true, vertices_400) then 10 else
  if p.val = (true, vertices_656) then 11 else
  if p.val = (true, vertices_784) then 12 else
  if p.val = (true, vertices_448) then 13 else
  if p.val = (true, vertices_832) then 14 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_643), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_297), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_386), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_148), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_536), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_552), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_584), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_176), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_336), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_592), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_400), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_656), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_784), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_448), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_832), by decide +kernel⟩
  | 15 => Sum.inl 0
  | 16 => Sum.inr ⟨(false, vertices_199), by decide +kernel⟩
  | 17 => Sum.inr ⟨(false, vertices_331), by decide +kernel⟩
  | 18 => Sum.inr ⟨(false, vertices_803), by decide +kernel⟩
  | 19 => Sum.inl 1
  | 20 => Sum.inr ⟨(false, vertices_61), by decide +kernel⟩
  | 21 => Sum.inr ⟨(false, vertices_93), by decide +kernel⟩
  | 22 => Sum.inr ⟨(false, vertices_677), by decide +kernel⟩
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
cert_row_4 0 0 3 6 7 8 914 386 1
cert_row_4 1 1 3 5 6 7 468 84 3
cert_row_4 2 2 3 4 6 8 696 56 3
cert_row_4 3 2 4 5 7 8 872 296 2
cert_rows
cert_pivot_2 0 1 3 2
cert_heightProof 4
cert_coverFacet 0 914
cert_cover_5 0 0 0 3 6 7 386 914 1
cert_coverFacet 1 450
cert_cover_2 1 5 0 6 7 194 450 3
cert_coverFacet 2 180
cert_cover_2 2 3 1 4 6 52 180 3
cert_coverFacet 3 468
cert_cover_5 3 1 1 3 5 6 84 468 3
cert_coverFacet 4 696
cert_cover_5 4 2 2 3 4 6 56 696 3
cert_coverFacet 5 600
cert_cover_2 5 3 2 5 8 88 600 3
cert_coverFacet 6 872
cert_cover_5 6 3 2 4 5 7 296 872 2
cert_coverFacet 7 848
cert_cover_2 7 5 3 7 8 336 848 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0742

end
end BundlePart1

section BundlePart2
/- Source: ProjectionCertificates/R_m16e10q1_0743.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0743

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [211, 301, 557, 901, 345, 665, 449, 614, 682, 114, 178, 962, 372, 836, 184, 312, 45, 261, 517, 25, 265, 521, 81, 145, 193, 321, 385, 641, 50, 82, 146, 98, 162, 546, 194, 578, 642, 100, 292, 548, 324, 580, 772, 56, 152, 280, 168, 296, 552, 648, 112, 176, 304, 336, 448, 832, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_211, vertices_301, vertices_557, vertices_901, vertices_345, vertices_665, vertices_449, vertices_614, vertices_682, vertices_114, vertices_178, vertices_962, vertices_372, vertices_836, vertices_184, vertices_312] (by decide +kernel)
  polygons := literalFinset [vertices_45, vertices_261, vertices_517, vertices_25, vertices_265, vertices_521, vertices_81, vertices_145, vertices_193, vertices_321, vertices_385, vertices_641, vertices_50, vertices_82, vertices_146, vertices_98, vertices_162, vertices_546, vertices_194, vertices_578, vertices_642, vertices_100, vertices_292, vertices_548, vertices_324, vertices_580, vertices_772, vertices_56, vertices_152, vertices_280, vertices_168, vertices_296, vertices_552, vertices_648, vertices_112, vertices_176, vertices_304, vertices_336, vertices_448, vertices_832, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_211), (false, vertices_301), (false, vertices_557), (false, vertices_901), (false, vertices_345), (false, vertices_665), (false, vertices_449), (true, vertices_50), (true, vertices_98), (true, vertices_162), (true, vertices_546), (true, vertices_578), (true, vertices_642), (true, vertices_100), (true, vertices_324), (true, vertices_580), (true, vertices_56), (true, vertices_168), (true, vertices_112), (true, vertices_176), (true, vertices_304), (true, vertices_832)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 16 18 22 25 26 27 28 29 30
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_211) then 17 else
  if p.val = (false, vertices_301) then 19 else
  if p.val = (false, vertices_557) then 20 else
  if p.val = (false, vertices_901) then 21 else
  if p.val = (false, vertices_345) then 23 else
  if p.val = (false, vertices_665) then 24 else
  if p.val = (false, vertices_449) then 0 else
  if p.val = (true, vertices_50) then 1 else
  if p.val = (true, vertices_98) then 2 else
  if p.val = (true, vertices_162) then 3 else
  if p.val = (true, vertices_546) then 4 else
  if p.val = (true, vertices_578) then 5 else
  if p.val = (true, vertices_642) then 6 else
  if p.val = (true, vertices_100) then 7 else
  if p.val = (true, vertices_324) then 8 else
  if p.val = (true, vertices_580) then 9 else
  if p.val = (true, vertices_56) then 10 else
  if p.val = (true, vertices_168) then 11 else
  if p.val = (true, vertices_112) then 12 else
  if p.val = (true, vertices_176) then 13 else
  if p.val = (true, vertices_304) then 14 else
  if p.val = (true, vertices_832) then 15 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_449), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_50), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_98), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_162), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_546), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_578), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_642), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_100), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_324), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_580), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_56), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_168), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_112), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_176), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_304), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_832), by decide +kernel⟩
  | 16 => Sum.inl 0
  | 17 => Sum.inr ⟨(false, vertices_211), by decide +kernel⟩
  | 18 => Sum.inl 1
  | 19 => Sum.inr ⟨(false, vertices_301), by decide +kernel⟩
  | 20 => Sum.inr ⟨(false, vertices_557), by decide +kernel⟩
  | 21 => Sum.inr ⟨(false, vertices_901), by decide +kernel⟩
  | 22 => Sum.inl 2
  | 23 => Sum.inr ⟨(false, vertices_345), by decide +kernel⟩
  | 24 => Sum.inr ⟨(false, vertices_665), by decide +kernel⟩
  | 25 => Sum.inl 3
  | 26 => Sum.inl 4
  | 27 => Sum.inl 5
  | 28 => Sum.inl 6
  | 29 => Sum.inl 7
  | 30 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 2 4 6 8 682 162 1
cert_row_4 1 0 5 6 7 8 962 194 3
cert_row_4 2 0 1 4 5 8 614 98 1
cert_row_4 3 1 3 4 5 7 372 100 1
cert_rows
cert_pivot_2 2 6 0 1
cert_heightProof 4
cert_coverFacet 0 614
cert_cover_5 0 2 0 1 4 5 98 614 1
cert_coverFacet 1 682
cert_cover_5 1 0 0 2 4 6 162 682 1
cert_coverFacet 2 114
cert_cover_2 2 3 0 4 5 50 114 3
cert_coverFacet 3 178
cert_cover_2 3 3 0 4 6 50 178 3
cert_coverFacet 4 962
cert_cover_5 4 1 0 5 6 7 194 962 3
cert_coverFacet 5 372
cert_cover_5 5 3 1 3 4 5 100 372 1
cert_coverFacet 6 836
cert_cover_2 6 5 1 7 8 324 836 3
cert_coverFacet 7 184
cert_cover_2 7 3 2 4 6 56 184 3
cert_coverFacet 8 312
cert_cover_2 8 3 2 4 7 56 312 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0743

end
end BundlePart2

section BundlePart3
/- Source: ProjectionCertificates/R_m16e10q1_0744.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0744

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [779, 61, 269, 357, 537, 241, 849, 398, 218, 602, 738, 898, 156, 180, 932, 864, 13, 37, 261, 25, 265, 521, 49, 81, 529, 97, 321, 769, 90, 138, 266, 522, 194, 578, 386, 642, 770, 28, 140, 268, 52, 148, 164, 292, 388, 152, 536, 176, 208, 592, 224, 352, 608, 672, 800, 832, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_779, vertices_61, vertices_269, vertices_357, vertices_537, vertices_241, vertices_849, vertices_398, vertices_218, vertices_602, vertices_738, vertices_898, vertices_156, vertices_180, vertices_932, vertices_864] (by decide +kernel)
  polygons := literalFinset [vertices_13, vertices_37, vertices_261, vertices_25, vertices_265, vertices_521, vertices_49, vertices_81, vertices_529, vertices_97, vertices_321, vertices_769, vertices_90, vertices_138, vertices_266, vertices_522, vertices_194, vertices_578, vertices_386, vertices_642, vertices_770, vertices_28, vertices_140, vertices_268, vertices_52, vertices_148, vertices_164, vertices_292, vertices_388, vertices_152, vertices_536, vertices_176, vertices_208, vertices_592, vertices_224, vertices_352, vertices_608, vertices_672, vertices_800, vertices_832, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_779), (false, vertices_61), (false, vertices_269), (false, vertices_357), (false, vertices_537), (false, vertices_241), (false, vertices_849), (true, vertices_90), (true, vertices_138), (true, vertices_194), (true, vertices_578), (true, vertices_386), (true, vertices_642), (true, vertices_140), (true, vertices_148), (true, vertices_164), (true, vertices_388), (true, vertices_152), (true, vertices_608), (true, vertices_672), (true, vertices_800), (true, vertices_896)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 16 19 22 23 26 27 28 29 30
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_779) then 17 else
  if p.val = (false, vertices_61) then 20 else
  if p.val = (false, vertices_269) then 0 else
  if p.val = (false, vertices_357) then 21 else
  if p.val = (false, vertices_537) then 1 else
  if p.val = (false, vertices_241) then 24 else
  if p.val = (false, vertices_849) then 25 else
  if p.val = (true, vertices_90) then 18 else
  if p.val = (true, vertices_138) then 2 else
  if p.val = (true, vertices_194) then 3 else
  if p.val = (true, vertices_578) then 4 else
  if p.val = (true, vertices_386) then 5 else
  if p.val = (true, vertices_642) then 6 else
  if p.val = (true, vertices_140) then 7 else
  if p.val = (true, vertices_148) then 8 else
  if p.val = (true, vertices_164) then 9 else
  if p.val = (true, vertices_388) then 10 else
  if p.val = (true, vertices_152) then 11 else
  if p.val = (true, vertices_608) then 12 else
  if p.val = (true, vertices_672) then 13 else
  if p.val = (true, vertices_800) then 14 else
  if p.val = (true, vertices_896) then 15 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_269), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_537), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_138), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_194), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_578), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_386), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_642), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_140), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_148), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_164), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_388), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_152), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_608), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_672), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_800), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_896), by decide +kernel⟩
  | 16 => Sum.inl 0
  | 17 => Sum.inr ⟨(false, vertices_779), by decide +kernel⟩
  | 18 => Sum.inr ⟨(true, vertices_90), by decide +kernel⟩
  | 19 => Sum.inl 1
  | 20 => Sum.inr ⟨(false, vertices_61), by decide +kernel⟩
  | 21 => Sum.inr ⟨(false, vertices_357), by decide +kernel⟩
  | 22 => Sum.inl 2
  | 23 => Sum.inl 3
  | 24 => Sum.inr ⟨(false, vertices_241), by decide +kernel⟩
  | 25 => Sum.inr ⟨(false, vertices_849), by decide +kernel⟩
  | 26 => Sum.inl 4
  | 27 => Sum.inl 5
  | 28 => Sum.inl 6
  | 29 => Sum.inl 7
  | 30 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 2 3 5 90
cert_row_4 1 0 1 2 6 7 398 138 1
cert_row_4 2 0 4 5 6 8 738 194 1
cert_row_4 3 1 4 6 7 8 932 164 3
cert_rows
cert_pivot_2 3 2 0 1
cert_heightProof 4
cert_coverFacet 0 398
cert_cover_5 0 1 0 1 2 6 138 398 1
cert_coverFacet 1 218
cert_cover_5 1 0 0 2 3 6 90 218 3
cert_coverFacet 2 602
cert_cover_5 2 0 0 2 3 8 90 602 3
cert_coverFacet 3 738
cert_cover_5 3 2 0 4 5 6 194 738 1
cert_coverFacet 4 898
cert_cover_2 4 6 0 7 8 386 898 3
cert_coverFacet 5 156
cert_cover_2 5 2 1 3 6 28 156 3
cert_coverFacet 6 180
cert_cover_2 6 3 1 4 6 52 180 3
cert_coverFacet 7 932
cert_cover_5 7 3 1 4 6 7 164 932 3
cert_coverFacet 8 864
cert_cover_2 8 5 4 7 8 352 864 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0744

end
end BundlePart3

section BundlePart4
/- Source: ProjectionCertificates/R_m16e10q1_0745.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0745

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [775, 43, 587, 419, 105, 913, 737, 286, 526, 314, 124, 716, 212, 660, 788, 496, 11, 35, 259, 515, 41, 73, 97, 161, 577, 385, 641, 769, 14, 262, 518, 282, 42, 522, 290, 28, 76, 524, 84, 148, 276, 532, 196, 644, 772, 56, 104, 584, 112, 304, 208, 400, 656, 784, 224, 416, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_775, vertices_43, vertices_587, vertices_419, vertices_105, vertices_913, vertices_737, vertices_286, vertices_526, vertices_314, vertices_124, vertices_716, vertices_212, vertices_660, vertices_788, vertices_496] (by decide +kernel)
  polygons := literalFinset [vertices_11, vertices_35, vertices_259, vertices_515, vertices_41, vertices_73, vertices_97, vertices_161, vertices_577, vertices_385, vertices_641, vertices_769, vertices_14, vertices_262, vertices_518, vertices_282, vertices_42, vertices_522, vertices_290, vertices_28, vertices_76, vertices_524, vertices_84, vertices_148, vertices_276, vertices_532, vertices_196, vertices_644, vertices_772, vertices_56, vertices_104, vertices_584, vertices_112, vertices_304, vertices_208, vertices_400, vertices_656, vertices_784, vertices_224, vertices_416, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_775), (false, vertices_43), (false, vertices_587), (false, vertices_419), (false, vertices_105), (false, vertices_913), (false, vertices_737), (true, vertices_14), (true, vertices_282), (true, vertices_28), (true, vertices_76), (true, vertices_524), (true, vertices_84), (true, vertices_148), (true, vertices_276), (true, vertices_532), (true, vertices_196), (true, vertices_644), (true, vertices_56), (true, vertices_112), (true, vertices_304), (true, vertices_208)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 18 16 22 23 25 27 28 29 30
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_775) then 17 else
  if p.val = (false, vertices_43) then 0 else
  if p.val = (false, vertices_587) then 19 else
  if p.val = (false, vertices_419) then 20 else
  if p.val = (false, vertices_105) then 1 else
  if p.val = (false, vertices_913) then 24 else
  if p.val = (false, vertices_737) then 26 else
  if p.val = (true, vertices_14) then 2 else
  if p.val = (true, vertices_282) then 21 else
  if p.val = (true, vertices_28) then 3 else
  if p.val = (true, vertices_76) then 4 else
  if p.val = (true, vertices_524) then 5 else
  if p.val = (true, vertices_84) then 6 else
  if p.val = (true, vertices_148) then 7 else
  if p.val = (true, vertices_276) then 8 else
  if p.val = (true, vertices_532) then 9 else
  if p.val = (true, vertices_196) then 10 else
  if p.val = (true, vertices_644) then 11 else
  if p.val = (true, vertices_56) then 12 else
  if p.val = (true, vertices_112) then 13 else
  if p.val = (true, vertices_304) then 14 else
  if p.val = (true, vertices_208) then 15 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_43), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_105), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_14), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_28), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_76), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_524), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_84), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_148), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_276), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_532), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_196), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_644), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_56), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_112), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_304), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_208), by decide +kernel⟩
  | 16 => Sum.inl 1
  | 17 => Sum.inr ⟨(false, vertices_775), by decide +kernel⟩
  | 18 => Sum.inl 0
  | 19 => Sum.inr ⟨(false, vertices_587), by decide +kernel⟩
  | 20 => Sum.inr ⟨(false, vertices_419), by decide +kernel⟩
  | 21 => Sum.inr ⟨(true, vertices_282), by decide +kernel⟩
  | 22 => Sum.inl 2
  | 23 => Sum.inl 3
  | 24 => Sum.inr ⟨(false, vertices_913), by decide +kernel⟩
  | 25 => Sum.inl 4
  | 26 => Sum.inr ⟨(false, vertices_737), by decide +kernel⟩
  | 27 => Sum.inl 5
  | 28 => Sum.inl 6
  | 29 => Sum.inl 7
  | 30 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 2 3 7 282
cert_row_4 1 1 2 5 6 8 716 76 3
cert_row_4 2 1 2 3 4 5 124 28 3
cert_row_4 3 3 4 5 6 7 496 112 3
cert_rows
cert_pivot_2 0 8 1 3
cert_heightProof 4
cert_coverFacet 0 286
cert_cover_5 0 0 0 1 2 3 14 286 3
cert_coverFacet 1 526
cert_cover_2 1 1 0 2 8 14 526 3
cert_coverFacet 2 314
cert_cover_5 2 0 0 2 3 4 282 314 3
cert_coverFacet 3 124
cert_cover_5 3 2 1 2 3 4 28 124 3
cert_coverFacet 4 716
cert_cover_5 4 1 1 2 5 6 76 716 3
cert_coverFacet 5 212
cert_cover_2 5 3 1 5 6 84 212 3
cert_coverFacet 6 660
cert_cover_2 6 3 1 6 8 148 660 3
cert_coverFacet 7 788
cert_cover_2 7 3 1 7 8 276 788 3
cert_coverFacet 8 496
cert_cover_5 8 3 3 4 5 6 112 496 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0745

end
end BundlePart4

section BundlePart5
/- Source: ProjectionCertificates/R_m16e10q1_0746.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0746

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [651, 333, 233, 777, 369, 929, 94, 270, 662, 806, 218, 778, 308, 564, 340, 752, 73, 137, 265, 521, 97, 161, 289, 321, 641, 769, 14, 22, 262, 518, 90, 138, 266, 522, 146, 642, 770, 76, 268, 52, 84, 276, 532, 292, 548, 324, 200, 776, 112, 304, 560, 208, 336, 656, 224, 672, 800]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_651, vertices_333, vertices_233, vertices_777, vertices_369, vertices_929, vertices_94, vertices_270, vertices_662, vertices_806, vertices_218, vertices_778, vertices_308, vertices_564, vertices_340, vertices_752] (by decide +kernel)
  polygons := literalFinset [vertices_73, vertices_137, vertices_265, vertices_521, vertices_97, vertices_161, vertices_289, vertices_321, vertices_641, vertices_769, vertices_14, vertices_22, vertices_262, vertices_518, vertices_90, vertices_138, vertices_266, vertices_522, vertices_146, vertices_642, vertices_770, vertices_76, vertices_268, vertices_52, vertices_84, vertices_276, vertices_532, vertices_292, vertices_548, vertices_324, vertices_200, vertices_776, vertices_112, vertices_304, vertices_560, vertices_208, vertices_336, vertices_656, vertices_224, vertices_672, vertices_800] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_651), (false, vertices_333), (false, vertices_233), (false, vertices_777), (false, vertices_369), (false, vertices_929), (true, vertices_14), (true, vertices_22), (true, vertices_262), (true, vertices_518), (true, vertices_90), (true, vertices_266), (true, vertices_146), (true, vertices_770), (true, vertices_52), (true, vertices_84), (true, vertices_276), (true, vertices_532), (true, vertices_292), (true, vertices_548), (true, vertices_560), (true, vertices_208), (true, vertices_656)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 17 20 22 24 26 28 29 30 31
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_651) then 18 else
  if p.val = (false, vertices_333) then 21 else
  if p.val = (false, vertices_233) then 23 else
  if p.val = (false, vertices_777) then 0 else
  if p.val = (false, vertices_369) then 25 else
  if p.val = (false, vertices_929) then 27 else
  if p.val = (true, vertices_14) then 1 else
  if p.val = (true, vertices_22) then 2 else
  if p.val = (true, vertices_262) then 3 else
  if p.val = (true, vertices_518) then 4 else
  if p.val = (true, vertices_90) then 19 else
  if p.val = (true, vertices_266) then 5 else
  if p.val = (true, vertices_146) then 6 else
  if p.val = (true, vertices_770) then 7 else
  if p.val = (true, vertices_52) then 8 else
  if p.val = (true, vertices_84) then 9 else
  if p.val = (true, vertices_276) then 10 else
  if p.val = (true, vertices_532) then 11 else
  if p.val = (true, vertices_292) then 12 else
  if p.val = (true, vertices_548) then 13 else
  if p.val = (true, vertices_560) then 14 else
  if p.val = (true, vertices_208) then 15 else
  if p.val = (true, vertices_656) then 16 else
  0
cert_priority
cert_nodeAtPriority_66 777 14 22 262 518 266 146 770 52 84 276 532 292 548 560 208 656 651 90 333 233 369 929
cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 2 3 5 90
cert_row_4 1 0 1 4 7 8 806 262 2
cert_row_4 2 0 1 3 6 8 662 22 3
cert_row_4 3 3 4 5 6 8 752 112 3
cert_rows
cert_pivot_2 2 7 0 3
cert_heightProof 4
cert_coverFacet 0 94
cert_cover_5 0 0 0 1 2 3 14 94 3
cert_coverFacet 1 270
cert_cover_2 1 1 0 2 7 14 270 3
cert_coverFacet 2 662
cert_cover_5 2 2 0 1 3 6 22 662 3
cert_coverFacet 3 806
cert_cover_5 3 1 0 1 4 7 262 806 2
cert_coverFacet 4 218
cert_cover_5 4 0 0 2 3 6 90 218 3
cert_coverFacet 5 778
cert_cover_2 5 2 0 7 8 266 778 3
cert_coverFacet 6 308
cert_cover_2 6 3 1 4 7 52 308 3
cert_coverFacet 7 564
cert_cover_2 7 3 1 4 8 52 564 3
cert_coverFacet 8 340
cert_cover_2 8 3 1 5 7 84 340 3
cert_coverFacet 9 752
cert_cover_5 9 3 3 4 5 6 112 752 3
cert_coveringFacets_5
cert_coveringProof
cert_certificate 4 10
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0746

end
end BundlePart5

section BundlePart6
/- Source: ProjectionCertificates/R_m16e10q1_0747.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0747

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [835, 61, 333, 229, 281, 817, 609, 454, 666, 242, 626, 898, 172, 908, 184, 792, 13, 37, 69, 25, 265, 49, 273, 97, 545, 321, 577, 769, 114, 146, 530, 194, 322, 578, 386, 642, 770, 44, 140, 268, 164, 196, 324, 388, 56, 152, 280, 536, 168, 648, 776, 176, 560, 784, 224, 608, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_835, vertices_61, vertices_333, vertices_229, vertices_281, vertices_817, vertices_609, vertices_454, vertices_666, vertices_242, vertices_626, vertices_898, vertices_172, vertices_908, vertices_184, vertices_792] (by decide +kernel)
  polygons := literalFinset [vertices_13, vertices_37, vertices_69, vertices_25, vertices_265, vertices_49, vertices_273, vertices_97, vertices_545, vertices_321, vertices_577, vertices_769, vertices_114, vertices_146, vertices_530, vertices_194, vertices_322, vertices_578, vertices_386, vertices_642, vertices_770, vertices_44, vertices_140, vertices_268, vertices_164, vertices_196, vertices_324, vertices_388, vertices_56, vertices_152, vertices_280, vertices_536, vertices_168, vertices_648, vertices_776, vertices_176, vertices_560, vertices_784, vertices_224, vertices_608, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_835), (false, vertices_61), (false, vertices_333), (false, vertices_229), (false, vertices_281), (false, vertices_817), (false, vertices_609), (true, vertices_114), (true, vertices_146), (true, vertices_530), (true, vertices_194), (true, vertices_386), (true, vertices_642), (true, vertices_140), (true, vertices_388), (true, vertices_152), (true, vertices_536), (true, vertices_168), (true, vertices_648), (true, vertices_776), (true, vertices_176), (true, vertices_896)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 16 19 23 24 26 27 28 29 30
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_835) then 17 else
  if p.val = (false, vertices_61) then 20 else
  if p.val = (false, vertices_333) then 21 else
  if p.val = (false, vertices_229) then 22 else
  if p.val = (false, vertices_281) then 0 else
  if p.val = (false, vertices_817) then 25 else
  if p.val = (false, vertices_609) then 1 else
  if p.val = (true, vertices_114) then 18 else
  if p.val = (true, vertices_146) then 2 else
  if p.val = (true, vertices_530) then 3 else
  if p.val = (true, vertices_194) then 4 else
  if p.val = (true, vertices_386) then 5 else
  if p.val = (true, vertices_642) then 6 else
  if p.val = (true, vertices_140) then 7 else
  if p.val = (true, vertices_388) then 8 else
  if p.val = (true, vertices_152) then 9 else
  if p.val = (true, vertices_536) then 10 else
  if p.val = (true, vertices_168) then 11 else
  if p.val = (true, vertices_648) then 12 else
  if p.val = (true, vertices_776) then 13 else
  if p.val = (true, vertices_176) then 14 else
  if p.val = (true, vertices_896) then 15 else
  0
cert_priority
cert_nodeAtPriority_21 0 281 1 609 146 530 194 386 642 140 388 152 536 168 648 776 176 896 835 114 61 333 229 817
cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 3 4 5 114
cert_row_4 1 0 1 5 6 7 454 194 1
cert_row_4 2 0 2 3 6 8 666 146 1
cert_row_4 3 1 2 6 7 8 908 140 3
cert_rows
cert_pivot_2 4 5 0 1
cert_heightProof 4
cert_coverFacet 0 454
cert_cover_5 0 1 0 1 5 6 194 454 1
cert_coverFacet 1 666
cert_cover_5 1 2 0 2 3 6 146 666 1
cert_coverFacet 2 242
cert_cover_5 2 0 0 3 4 6 114 242 3
cert_coverFacet 3 626
cert_cover_5 3 0 0 3 4 8 114 626 3
cert_coverFacet 4 898
cert_cover_2 4 6 0 7 8 386 898 3
cert_coverFacet 5 172
cert_cover_2 5 2 1 4 6 44 172 3
cert_coverFacet 6 908
cert_cover_5 6 3 1 2 6 7 140 908 3
cert_coverFacet 7 184
cert_cover_2 7 3 2 4 6 56 184 3
cert_coverFacet 8 792
cert_cover_2 8 3 2 7 8 280 792 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0747

end
end BundlePart6

section BundlePart7
/- Source: ProjectionCertificates/R_m16e10q1_0748.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0748

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [203, 587, 403, 803, 309, 569, 153, 710, 898, 620, 116, 340, 932, 452, 120, 472, 75, 131, 259, 515, 25, 137, 521, 49, 145, 273, 289, 545, 194, 578, 386, 642, 770, 52, 84, 276, 100, 292, 548, 196, 324, 580, 388, 644, 56, 88, 152, 104, 552, 200, 584, 112, 336, 400, 800, 448, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_203, vertices_587, vertices_403, vertices_803, vertices_309, vertices_569, vertices_153, vertices_710, vertices_898, vertices_620, vertices_116, vertices_340, vertices_932, vertices_452, vertices_120, vertices_472] (by decide +kernel)
  polygons := literalFinset [vertices_75, vertices_131, vertices_259, vertices_515, vertices_25, vertices_137, vertices_521, vertices_49, vertices_145, vertices_273, vertices_289, vertices_545, vertices_194, vertices_578, vertices_386, vertices_642, vertices_770, vertices_52, vertices_84, vertices_276, vertices_100, vertices_292, vertices_548, vertices_196, vertices_324, vertices_580, vertices_388, vertices_644, vertices_56, vertices_88, vertices_152, vertices_104, vertices_552, vertices_200, vertices_584, vertices_112, vertices_336, vertices_400, vertices_800, vertices_448, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_203), (false, vertices_587), (false, vertices_403), (false, vertices_803), (false, vertices_309), (false, vertices_569), (false, vertices_153), (true, vertices_642), (true, vertices_84), (true, vertices_100), (true, vertices_548), (true, vertices_196), (true, vertices_324), (true, vertices_580), (true, vertices_388), (true, vertices_644), (true, vertices_88), (true, vertices_104), (true, vertices_112), (true, vertices_336), (true, vertices_448), (true, vertices_896)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 22 16 18 25 26 27 28 29 30
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_203) then 19 else
  if p.val = (false, vertices_587) then 20 else
  if p.val = (false, vertices_403) then 23 else
  if p.val = (false, vertices_803) then 24 else
  if p.val = (false, vertices_309) then 17 else
  if p.val = (false, vertices_569) then 21 else
  if p.val = (false, vertices_153) then 0 else
  if p.val = (true, vertices_642) then 1 else
  if p.val = (true, vertices_84) then 2 else
  if p.val = (true, vertices_100) then 3 else
  if p.val = (true, vertices_548) then 4 else
  if p.val = (true, vertices_196) then 5 else
  if p.val = (true, vertices_324) then 6 else
  if p.val = (true, vertices_580) then 7 else
  if p.val = (true, vertices_388) then 8 else
  if p.val = (true, vertices_644) then 9 else
  if p.val = (true, vertices_88) then 10 else
  if p.val = (true, vertices_104) then 11 else
  if p.val = (true, vertices_112) then 12 else
  if p.val = (true, vertices_336) then 13 else
  if p.val = (true, vertices_448) then 14 else
  if p.val = (true, vertices_896) then 15 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_153), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_642), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_84), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_100), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_548), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_196), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_324), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_580), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_388), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_644), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_88), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_104), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_112), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_336), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_448), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_896), by decide +kernel⟩
  | 16 => Sum.inl 1
  | 17 => Sum.inr ⟨(false, vertices_309), by decide +kernel⟩
  | 18 => Sum.inl 2
  | 19 => Sum.inr ⟨(false, vertices_203), by decide +kernel⟩
  | 20 => Sum.inr ⟨(false, vertices_587), by decide +kernel⟩
  | 21 => Sum.inr ⟨(false, vertices_569), by decide +kernel⟩
  | 22 => Sum.inl 0
  | 23 => Sum.inr ⟨(false, vertices_403), by decide +kernel⟩
  | 24 => Sum.inr ⟨(false, vertices_803), by decide +kernel⟩
  | 25 => Sum.inl 3
  | 26 => Sum.inl 4
  | 27 => Sum.inl 5
  | 28 => Sum.inl 6
  | 29 => Sum.inl 7
  | 30 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 5 6 8 710 194 1
cert_row_4 1 2 3 5 6 7 472 88 3
cert_row_4 2 1 2 4 5 8 620 100 1
cert_row_4 3 1 4 6 7 8 932 292 2
cert_rows
cert_pivot_2 0 3 2 1
cert_heightProof 4
cert_coverFacet 0 710
cert_cover_5 0 0 0 1 5 6 194 710 1
cert_coverFacet 1 898
cert_cover_2 1 6 0 7 8 386 898 3
cert_coverFacet 2 620
cert_cover_5 2 2 1 2 4 5 100 620 1
cert_coverFacet 3 116
cert_cover_2 3 3 1 4 5 52 116 3
cert_coverFacet 4 340
cert_cover_2 4 3 1 5 7 84 340 3
cert_coverFacet 5 932
cert_cover_5 5 3 1 4 6 7 292 932 2
cert_coverFacet 6 452
cert_cover_2 6 5 1 6 7 196 452 3
cert_coverFacet 7 120
cert_cover_2 7 3 2 4 5 56 120 3
cert_coverFacet 8 472
cert_cover_5 8 1 2 3 5 6 88 472 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0748

end
end BundlePart7

section BundlePart8
/- Source: ProjectionCertificates/R_m16e10q1_0749.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0749

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [803, 205, 421, 837, 241, 609, 654, 902, 314, 538, 394, 626, 604, 216, 408, 432, 69, 133, 261, 97, 161, 289, 545, 193, 577, 769, 646, 26, 138, 266, 522, 50, 530, 290, 546, 386, 770, 76, 140, 524, 580, 388, 772, 88, 152, 280, 536, 200, 392, 112, 176, 304, 208, 592, 400, 608, 416]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_803, vertices_205, vertices_421, vertices_837, vertices_241, vertices_609, vertices_654, vertices_902, vertices_314, vertices_538, vertices_394, vertices_626, vertices_604, vertices_216, vertices_408, vertices_432] (by decide +kernel)
  polygons := literalFinset [vertices_69, vertices_133, vertices_261, vertices_97, vertices_161, vertices_289, vertices_545, vertices_193, vertices_577, vertices_769, vertices_646, vertices_26, vertices_138, vertices_266, vertices_522, vertices_50, vertices_530, vertices_290, vertices_546, vertices_386, vertices_770, vertices_76, vertices_140, vertices_524, vertices_580, vertices_388, vertices_772, vertices_88, vertices_152, vertices_280, vertices_536, vertices_200, vertices_392, vertices_112, vertices_176, vertices_304, vertices_208, vertices_592, vertices_400, vertices_608, vertices_416] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_803), (false, vertices_205), (false, vertices_421), (false, vertices_837), (false, vertices_241), (false, vertices_609), (true, vertices_646), (true, vertices_26), (true, vertices_138), (true, vertices_266), (true, vertices_522), (true, vertices_50), (true, vertices_530), (true, vertices_386), (true, vertices_524), (true, vertices_88), (true, vertices_152), (true, vertices_280), (true, vertices_536), (true, vertices_392), (true, vertices_304), (true, vertices_592), (true, vertices_400)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 17 20 24 25 27 28 29 30 31
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_803) then 18 else
  if p.val = (false, vertices_205) then 21 else
  if p.val = (false, vertices_421) then 22 else
  if p.val = (false, vertices_837) then 23 else
  if p.val = (false, vertices_241) then 26 else
  if p.val = (false, vertices_609) then 0 else
  if p.val = (true, vertices_646) then 19 else
  if p.val = (true, vertices_26) then 1 else
  if p.val = (true, vertices_138) then 2 else
  if p.val = (true, vertices_266) then 3 else
  if p.val = (true, vertices_522) then 4 else
  if p.val = (true, vertices_50) then 5 else
  if p.val = (true, vertices_530) then 6 else
  if p.val = (true, vertices_386) then 7 else
  if p.val = (true, vertices_524) then 8 else
  if p.val = (true, vertices_88) then 9 else
  if p.val = (true, vertices_152) then 10 else
  if p.val = (true, vertices_280) then 11 else
  if p.val = (true, vertices_536) then 12 else
  if p.val = (true, vertices_392) then 13 else
  if p.val = (true, vertices_304) then 14 else
  if p.val = (true, vertices_592) then 15 else
  if p.val = (true, vertices_400) then 16 else
  0
cert_priority
cert_nodeAtPriority_45 609 26 138 266 522 50 530 386 524 88 152 280 536 392 304 592 400 803 646 205 421 837 241
cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 1 6 8 646
cert_row_4 1 0 2 3 4 7 314 26 3
cert_row_4 2 0 3 4 5 8 626 50 3
cert_row_4 3 1 2 3 5 8 604 76 2
cert_rows
cert_pivot_2 6 7 0 1
cert_heightProof 4
cert_coverFacet 0 654
cert_cover_5 0 0 0 1 2 6 646 654 2
cert_coverFacet 1 902
cert_cover_5 1 0 0 1 6 7 646 902 3
cert_coverFacet 2 314
cert_cover_5 2 1 0 2 3 4 26 314 3
cert_coverFacet 3 538
cert_cover_2 3 2 0 3 8 26 538 3
cert_coverFacet 4 394
cert_cover_2 4 2 0 6 7 138 394 3
cert_coverFacet 5 626
cert_cover_5 5 2 0 3 4 5 50 626 3
cert_coverFacet 6 604
cert_cover_5 6 3 1 2 3 5 76 604 2
cert_coverFacet 7 216
cert_cover_2 7 3 2 5 6 88 216 3
cert_coverFacet 8 408
cert_cover_2 8 3 2 6 7 152 408 3
cert_coverFacet 9 432
cert_cover_2 9 4 3 6 7 176 432 3
cert_coveringFacets_5
cert_coveringProof
cert_certificate 4 10
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0749

end
end BundlePart8

section BundlePart9
/- Source: ProjectionCertificates/R_m16e10q1_0750.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0750

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [419, 661, 313, 601, 681, 401, 406, 198, 326, 810, 842, 226, 610, 348, 596, 740, 25, 41, 521, 145, 273, 529, 161, 289, 385, 641, 70, 134, 262, 778, 98, 162, 290, 546, 194, 322, 578, 386, 84, 148, 276, 532, 196, 324, 580, 644, 88, 280, 296, 552, 328, 584, 592, 400, 224, 608, 672]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_419, vertices_661, vertices_313, vertices_601, vertices_681, vertices_401, vertices_406, vertices_198, vertices_326, vertices_810, vertices_842, vertices_226, vertices_610, vertices_348, vertices_596, vertices_740] (by decide +kernel)
  polygons := literalFinset [vertices_25, vertices_41, vertices_521, vertices_145, vertices_273, vertices_529, vertices_161, vertices_289, vertices_385, vertices_641, vertices_70, vertices_134, vertices_262, vertices_778, vertices_98, vertices_162, vertices_290, vertices_546, vertices_194, vertices_322, vertices_578, vertices_386, vertices_84, vertices_148, vertices_276, vertices_532, vertices_196, vertices_324, vertices_580, vertices_644, vertices_88, vertices_280, vertices_296, vertices_552, vertices_328, vertices_584, vertices_592, vertices_400, vertices_224, vertices_608, vertices_672] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_419), (false, vertices_661), (false, vertices_313), (false, vertices_601), (false, vertices_681), (false, vertices_401), (true, vertices_70), (true, vertices_134), (true, vertices_262), (true, vertices_778), (true, vertices_98), (true, vertices_546), (true, vertices_194), (true, vertices_322), (true, vertices_578), (true, vertices_84), (true, vertices_276), (true, vertices_196), (true, vertices_324), (true, vertices_580), (true, vertices_328), (true, vertices_224), (true, vertices_608)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 17 20 22 26 27 28 29 30 31
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_419) then 18 else
  if p.val = (false, vertices_661) then 21 else
  if p.val = (false, vertices_313) then 23 else
  if p.val = (false, vertices_601) then 24 else
  if p.val = (false, vertices_681) then 25 else
  if p.val = (false, vertices_401) then 0 else
  if p.val = (true, vertices_70) then 1 else
  if p.val = (true, vertices_134) then 2 else
  if p.val = (true, vertices_262) then 3 else
  if p.val = (true, vertices_778) then 19 else
  if p.val = (true, vertices_98) then 4 else
  if p.val = (true, vertices_546) then 5 else
  if p.val = (true, vertices_194) then 6 else
  if p.val = (true, vertices_322) then 7 else
  if p.val = (true, vertices_578) then 8 else
  if p.val = (true, vertices_84) then 9 else
  if p.val = (true, vertices_276) then 10 else
  if p.val = (true, vertices_196) then 11 else
  if p.val = (true, vertices_324) then 12 else
  if p.val = (true, vertices_580) then 13 else
  if p.val = (true, vertices_328) then 14 else
  if p.val = (true, vertices_224) then 15 else
  if p.val = (true, vertices_608) then 16 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_401), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_70), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_134), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_262), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_98), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_546), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_194), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_322), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_578), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_84), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_276), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_196), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_324), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_580), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_328), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_224), by decide +kernel⟩
  | 16 => Sum.inr ⟨(true, vertices_608), by decide +kernel⟩
  | 17 => Sum.inl 0
  | 18 => Sum.inr ⟨(false, vertices_419), by decide +kernel⟩
  | 19 => Sum.inr ⟨(true, vertices_778), by decide +kernel⟩
  | 20 => Sum.inl 1
  | 21 => Sum.inr ⟨(false, vertices_661), by decide +kernel⟩
  | 22 => Sum.inl 2
  | 23 => Sum.inr ⟨(false, vertices_313), by decide +kernel⟩
  | 24 => Sum.inr ⟨(false, vertices_601), by decide +kernel⟩
  | 25 => Sum.inr ⟨(false, vertices_681), by decide +kernel⟩
  | 26 => Sum.inl 3
  | 27 => Sum.inl 4
  | 28 => Sum.inl 5
  | 29 => Sum.inl 6
  | 30 => Sum.inl 7
  | 31 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 1 4 5 6 8 740 196 1
cert_row_2 1 0 2 7 8 778
cert_row_4 2 0 1 3 6 7 406 134 2
cert_row_4 3 1 2 3 5 7 348 84 1
cert_rows
cert_pivot_2 4 8 0 1
cert_heightProof 4
cert_coverFacet 0 406
cert_cover_5 0 2 0 1 3 6 134 406 2
cert_coverFacet 1 198
cert_cover_2 1 1 0 5 6 70 198 3
cert_coverFacet 2 326
cert_cover_2 2 1 0 5 7 70 326 3
cert_coverFacet 3 810
cert_cover_5 3 1 0 2 4 7 778 810 2
cert_coverFacet 4 842
cert_cover_5 4 1 0 2 5 7 778 842 2
cert_coverFacet 5 226
cert_cover_2 5 4 0 5 6 98 226 3
cert_coverFacet 6 610
cert_cover_2 6 4 0 5 8 98 610 3
cert_coverFacet 7 348
cert_cover_5 7 3 1 2 3 5 84 348 1
cert_coverFacet 8 596
cert_cover_2 8 3 1 5 8 84 596 3
cert_coverFacet 9 740
cert_cover_5 9 0 1 4 5 6 196 740 1
cert_coveringFacets_5
cert_coveringProof
cert_certificate 4 10
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0750

end
end BundlePart9

section BundlePart10
/- Source: ProjectionCertificates/R_m16e10q1_0751.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0751

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [835, 157, 781, 453, 121, 585, 241, 542, 58, 106, 586, 818, 482, 660, 932, 688, 13, 133, 261, 25, 73, 521, 113, 145, 193, 321, 577, 769, 26, 42, 74, 522, 50, 530, 98, 290, 322, 578, 770, 28, 524, 148, 532, 388, 644, 772, 56, 104, 584, 176, 560, 656, 224, 416, 672, 800, 448]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_835, vertices_157, vertices_781, vertices_453, vertices_121, vertices_585, vertices_241, vertices_542, vertices_58, vertices_106, vertices_586, vertices_818, vertices_482, vertices_660, vertices_932, vertices_688] (by decide +kernel)
  polygons := literalFinset [vertices_13, vertices_133, vertices_261, vertices_25, vertices_73, vertices_521, vertices_113, vertices_145, vertices_193, vertices_321, vertices_577, vertices_769, vertices_26, vertices_42, vertices_74, vertices_522, vertices_50, vertices_530, vertices_98, vertices_290, vertices_322, vertices_578, vertices_770, vertices_28, vertices_524, vertices_148, vertices_532, vertices_388, vertices_644, vertices_772, vertices_56, vertices_104, vertices_584, vertices_176, vertices_560, vertices_656, vertices_224, vertices_416, vertices_672, vertices_800, vertices_448] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_835), (false, vertices_157), (false, vertices_781), (false, vertices_453), (false, vertices_121), (false, vertices_585), (false, vertices_241), (true, vertices_26), (true, vertices_42), (true, vertices_74), (true, vertices_522), (true, vertices_50), (true, vertices_530), (true, vertices_98), (true, vertices_290), (true, vertices_532), (true, vertices_644), (true, vertices_560), (true, vertices_656), (true, vertices_416), (true, vertices_672), (true, vertices_800)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 16 18 22 23 26 27 28 29 30
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_835) then 17 else
  if p.val = (false, vertices_157) then 19 else
  if p.val = (false, vertices_781) then 20 else
  if p.val = (false, vertices_453) then 21 else
  if p.val = (false, vertices_121) then 24 else
  if p.val = (false, vertices_585) then 0 else
  if p.val = (false, vertices_241) then 25 else
  if p.val = (true, vertices_26) then 1 else
  if p.val = (true, vertices_42) then 2 else
  if p.val = (true, vertices_74) then 3 else
  if p.val = (true, vertices_522) then 4 else
  if p.val = (true, vertices_50) then 5 else
  if p.val = (true, vertices_530) then 6 else
  if p.val = (true, vertices_98) then 7 else
  if p.val = (true, vertices_290) then 8 else
  if p.val = (true, vertices_532) then 9 else
  if p.val = (true, vertices_644) then 10 else
  if p.val = (true, vertices_560) then 11 else
  if p.val = (true, vertices_656) then 12 else
  if p.val = (true, vertices_416) then 13 else
  if p.val = (true, vertices_672) then 14 else
  if p.val = (true, vertices_800) then 15 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_585), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_26), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_42), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_74), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_522), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_50), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_530), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_98), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_290), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_532), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_644), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_560), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_656), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_416), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_672), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_800), by decide +kernel⟩
  | 16 => Sum.inl 0
  | 17 => Sum.inr ⟨(false, vertices_835), by decide +kernel⟩
  | 18 => Sum.inl 1
  | 19 => Sum.inr ⟨(false, vertices_157), by decide +kernel⟩
  | 20 => Sum.inr ⟨(false, vertices_781), by decide +kernel⟩
  | 21 => Sum.inr ⟨(false, vertices_453), by decide +kernel⟩
  | 22 => Sum.inl 2
  | 23 => Sum.inl 3
  | 24 => Sum.inr ⟨(false, vertices_121), by decide +kernel⟩
  | 25 => Sum.inr ⟨(false, vertices_241), by decide +kernel⟩
  | 26 => Sum.inl 4
  | 27 => Sum.inl 5
  | 28 => Sum.inl 6
  | 29 => Sum.inl 7
  | 30 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 2 3 8 542 26 1
cert_row_4 1 0 3 4 7 8 818 50 3
cert_row_4 2 0 4 5 6 7 482 98 3
cert_row_4 3 1 4 6 7 8 932 388 1
cert_rows
cert_pivot_2 2 3 0 1
cert_heightProof 4
cert_coverFacet 0 542
cert_cover_5 0 0 0 1 2 3 26 542 1
cert_coverFacet 1 58
cert_cover_2 1 2 0 3 4 26 58 3
cert_coverFacet 2 106
cert_cover_2 2 2 0 4 5 42 106 3
cert_coverFacet 3 586
cert_cover_2 3 2 0 5 8 74 586 3
cert_coverFacet 4 818
cert_cover_5 4 1 0 3 4 7 50 818 3
cert_coverFacet 5 482
cert_cover_5 5 2 0 4 5 6 98 482 3
cert_coverFacet 6 660
cert_cover_2 6 3 1 6 8 148 660 3
cert_coverFacet 7 932
cert_cover_5 7 3 1 4 6 7 388 932 1
cert_coverFacet 8 688
cert_cover_2 8 4 3 6 8 176 688 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0751

end
end BundlePart10

section BundlePart11
/- Source: ProjectionCertificates/R_m16e10q1_0752.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0752

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [279, 659, 835, 181, 293, 681, 801, 282, 538, 618, 330, 236, 468, 868, 472, 664, 19, 259, 515, 21, 37, 261, 145, 161, 289, 545, 641, 769, 26, 74, 266, 522, 274, 530, 322, 578, 148, 276, 100, 164, 292, 196, 324, 152, 280, 536, 104, 168, 552, 200, 328, 648, 464, 656, 608, 800, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_279, vertices_659, vertices_835, vertices_181, vertices_293, vertices_681, vertices_801, vertices_282, vertices_538, vertices_618, vertices_330, vertices_236, vertices_468, vertices_868, vertices_472, vertices_664] (by decide +kernel)
  polygons := literalFinset [vertices_19, vertices_259, vertices_515, vertices_21, vertices_37, vertices_261, vertices_145, vertices_161, vertices_289, vertices_545, vertices_641, vertices_769, vertices_26, vertices_74, vertices_266, vertices_522, vertices_274, vertices_530, vertices_322, vertices_578, vertices_148, vertices_276, vertices_100, vertices_164, vertices_292, vertices_196, vertices_324, vertices_152, vertices_280, vertices_536, vertices_104, vertices_168, vertices_552, vertices_200, vertices_328, vertices_648, vertices_464, vertices_656, vertices_608, vertices_800, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_279), (false, vertices_659), (false, vertices_835), (false, vertices_181), (false, vertices_293), (false, vertices_681), (false, vertices_801), (true, vertices_26), (true, vertices_74), (true, vertices_266), (true, vertices_522), (true, vertices_100), (true, vertices_196), (true, vertices_324), (true, vertices_152), (true, vertices_280), (true, vertices_536), (true, vertices_104), (true, vertices_200), (true, vertices_328), (true, vertices_464), (true, vertices_608)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 16 20 22 24 26 27 28 29 30
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_279) then 17 else
  if p.val = (false, vertices_659) then 18 else
  if p.val = (false, vertices_835) then 19 else
  if p.val = (false, vertices_181) then 21 else
  if p.val = (false, vertices_293) then 0 else
  if p.val = (false, vertices_681) then 23 else
  if p.val = (false, vertices_801) then 1 else
  if p.val = (true, vertices_26) then 2 else
  if p.val = (true, vertices_74) then 3 else
  if p.val = (true, vertices_266) then 4 else
  if p.val = (true, vertices_522) then 5 else
  if p.val = (true, vertices_100) then 6 else
  if p.val = (true, vertices_196) then 7 else
  if p.val = (true, vertices_324) then 8 else
  if p.val = (true, vertices_152) then 9 else
  if p.val = (true, vertices_280) then 10 else
  if p.val = (true, vertices_536) then 11 else
  if p.val = (true, vertices_104) then 12 else
  if p.val = (true, vertices_200) then 13 else
  if p.val = (true, vertices_328) then 14 else
  if p.val = (true, vertices_464) then 25 else
  if p.val = (true, vertices_608) then 15 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_293), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_801), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_26), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_74), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_266), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_522), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_100), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_196), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_324), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_152), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_280), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_536), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_104), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_200), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_328), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_608), by decide +kernel⟩
  | 16 => Sum.inl 0
  | 17 => Sum.inr ⟨(false, vertices_279), by decide +kernel⟩
  | 18 => Sum.inr ⟨(false, vertices_659), by decide +kernel⟩
  | 19 => Sum.inr ⟨(false, vertices_835), by decide +kernel⟩
  | 20 => Sum.inl 1
  | 21 => Sum.inr ⟨(false, vertices_181), by decide +kernel⟩
  | 22 => Sum.inl 2
  | 23 => Sum.inr ⟨(false, vertices_681), by decide +kernel⟩
  | 24 => Sum.inl 3
  | 25 => Sum.inr ⟨(true, vertices_464), by decide +kernel⟩
  | 26 => Sum.inl 4
  | 27 => Sum.inl 5
  | 28 => Sum.inl 6
  | 29 => Sum.inl 7
  | 30 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 3 5 6 7 464
cert_row_4 1 0 2 4 5 8 618 74 2
cert_row_4 2 1 2 4 5 6 236 100 1
cert_row_4 3 1 4 5 7 8 868 100 3
cert_rows
cert_pivot_2 3 0 2 1
cert_heightProof 4
cert_coverFacet 0 282
cert_cover_2 0 2 0 3 7 26 282 3
cert_coverFacet 1 538
cert_cover_2 1 2 0 3 8 26 538 3
cert_coverFacet 2 618
cert_cover_5 2 1 0 2 4 5 74 618 2
cert_coverFacet 3 330
cert_cover_2 3 2 0 5 7 74 330 3
cert_coverFacet 4 236
cert_cover_5 4 2 1 2 4 5 100 236 1
cert_coverFacet 5 468
cert_cover_5 5 0 1 3 5 6 148 468 2
cert_coverFacet 6 868
cert_cover_5 6 3 1 4 5 7 100 868 3
cert_coverFacet 7 472
cert_cover_5 7 0 2 3 5 6 152 472 2
cert_coverFacet 8 664
cert_cover_2 8 3 2 6 8 152 664 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0752

end
end BundlePart11

section BundlePart12
/- Source: ProjectionCertificates/R_m16e10q1_0753.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0753

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [611, 405, 361, 721, 337, 929, 110, 142, 550, 902, 602, 666, 316, 156, 804, 344, 81, 145, 273, 97, 289, 545, 321, 577, 385, 641, 14, 38, 134, 518, 538, 74, 138, 98, 546, 578, 642, 28, 44, 140, 148, 276, 292, 548, 388, 772, 88, 152, 280, 104, 296, 328, 336, 592, 656, 800, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_611, vertices_405, vertices_361, vertices_721, vertices_337, vertices_929, vertices_110, vertices_142, vertices_550, vertices_902, vertices_602, vertices_666, vertices_316, vertices_156, vertices_804, vertices_344] (by decide +kernel)
  polygons := literalFinset [vertices_81, vertices_145, vertices_273, vertices_97, vertices_289, vertices_545, vertices_321, vertices_577, vertices_385, vertices_641, vertices_14, vertices_38, vertices_134, vertices_518, vertices_538, vertices_74, vertices_138, vertices_98, vertices_546, vertices_578, vertices_642, vertices_28, vertices_44, vertices_140, vertices_148, vertices_276, vertices_292, vertices_548, vertices_388, vertices_772, vertices_88, vertices_152, vertices_280, vertices_104, vertices_296, vertices_328, vertices_336, vertices_592, vertices_656, vertices_800, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_611), (false, vertices_405), (false, vertices_361), (false, vertices_721), (false, vertices_337), (false, vertices_929), (true, vertices_14), (true, vertices_38), (true, vertices_134), (true, vertices_518), (true, vertices_538), (true, vertices_74), (true, vertices_138), (true, vertices_642), (true, vertices_28), (true, vertices_44), (true, vertices_140), (true, vertices_292), (true, vertices_548), (true, vertices_772), (true, vertices_88), (true, vertices_152), (true, vertices_280)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 17 20 22 24 26 28 29 30 31
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_611) then 18 else
  if p.val = (false, vertices_405) then 21 else
  if p.val = (false, vertices_361) then 23 else
  if p.val = (false, vertices_721) then 25 else
  if p.val = (false, vertices_337) then 0 else
  if p.val = (false, vertices_929) then 27 else
  if p.val = (true, vertices_14) then 1 else
  if p.val = (true, vertices_38) then 2 else
  if p.val = (true, vertices_134) then 3 else
  if p.val = (true, vertices_518) then 4 else
  if p.val = (true, vertices_538) then 19 else
  if p.val = (true, vertices_74) then 5 else
  if p.val = (true, vertices_138) then 6 else
  if p.val = (true, vertices_642) then 7 else
  if p.val = (true, vertices_28) then 8 else
  if p.val = (true, vertices_44) then 9 else
  if p.val = (true, vertices_140) then 10 else
  if p.val = (true, vertices_292) then 11 else
  if p.val = (true, vertices_548) then 12 else
  if p.val = (true, vertices_772) then 13 else
  if p.val = (true, vertices_88) then 14 else
  if p.val = (true, vertices_152) then 15 else
  if p.val = (true, vertices_280) then 16 else
  0
cert_priority
cert_nodeAtPriority_66 337 14 38 134 518 74 138 642 28 44 140 292 548 772 88 152 280 611 538 405 361 721 929
cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 2 4 5 110 14 3
cert_row_4 1 0 1 6 7 8 902 134 3
cert_row_2 2 0 2 3 8 538
cert_row_4 3 1 2 3 4 7 316 28 3
cert_rows
cert_pivot_2 5 6 0 1
cert_heightProof 4
cert_coverFacet 0 110
cert_cover_5 0 0 0 1 2 4 14 110 3
cert_coverFacet 1 142
cert_cover_2 1 1 0 2 6 14 142 3
cert_coverFacet 2 550
cert_cover_2 2 1 0 4 8 38 550 3
cert_coverFacet 3 902
cert_cover_5 3 1 0 1 6 7 134 902 3
cert_coverFacet 4 602
cert_cover_5 4 2 0 2 3 5 538 602 3
cert_coverFacet 5 666
cert_cover_5 5 2 0 2 3 6 538 666 3
cert_coverFacet 6 316
cert_cover_5 6 3 1 2 3 4 28 316 3
cert_coverFacet 7 156
cert_cover_2 7 2 1 3 6 28 156 3
cert_coverFacet 8 804
cert_cover_2 8 4 1 7 8 292 804 3
cert_coverFacet 9 344
cert_cover_2 9 3 2 5 7 88 344 3
cert_coveringFacets_5
cert_coveringProof
cert_certificate 4 10
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0753

end
end BundlePart12

section BundlePart13
/- Source: ProjectionCertificates/R_m16e10q1_0754.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0754

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [527, 269, 677, 453, 617, 329, 241, 286, 902, 538, 626, 306, 930, 472, 600, 432, 13, 133, 261, 517, 73, 265, 521, 97, 161, 545, 193, 321, 14, 262, 518, 26, 522, 50, 274, 530, 290, 546, 898, 268, 388, 644, 88, 280, 536, 328, 584, 112, 176, 304, 208, 592, 400, 608, 416, 672, 448]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_527, vertices_269, vertices_677, vertices_453, vertices_617, vertices_329, vertices_241, vertices_286, vertices_902, vertices_538, vertices_626, vertices_306, vertices_930, vertices_472, vertices_600, vertices_432] (by decide +kernel)
  polygons := literalFinset [vertices_13, vertices_133, vertices_261, vertices_517, vertices_73, vertices_265, vertices_521, vertices_97, vertices_161, vertices_545, vertices_193, vertices_321, vertices_14, vertices_262, vertices_518, vertices_26, vertices_522, vertices_50, vertices_274, vertices_530, vertices_290, vertices_546, vertices_898, vertices_268, vertices_388, vertices_644, vertices_88, vertices_280, vertices_536, vertices_328, vertices_584, vertices_112, vertices_176, vertices_304, vertices_208, vertices_592, vertices_400, vertices_608, vertices_416, vertices_672, vertices_448] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_527), (false, vertices_269), (false, vertices_677), (false, vertices_453), (false, vertices_617), (false, vertices_329), (false, vertices_241), (true, vertices_262), (true, vertices_26), (true, vertices_50), (true, vertices_274), (true, vertices_530), (true, vertices_290), (true, vertices_546), (true, vertices_898), (true, vertices_88), (true, vertices_280), (true, vertices_536), (true, vertices_304), (true, vertices_592), (true, vertices_400), (true, vertices_416)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 16 19 22 24 26 27 28 29 30
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_527) then 17 else
  if p.val = (false, vertices_269) then 0 else
  if p.val = (false, vertices_677) then 20 else
  if p.val = (false, vertices_453) then 21 else
  if p.val = (false, vertices_617) then 23 else
  if p.val = (false, vertices_329) then 1 else
  if p.val = (false, vertices_241) then 25 else
  if p.val = (true, vertices_262) then 2 else
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
cert_nodeAtPriority_50 1 269 0 329 262 26 50 274 530 290 546 88 280 536 304 592 400 416 527 898 677 453 617 241
cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 2 3 7 286 14 3
cert_row_4 1 0 3 4 5 8 626 50 3
cert_row_2 2 0 6 7 8 898
cert_row_4 3 2 3 5 6 7 472 88 3
cert_rows
cert_pivot_2 1 4 0 2
cert_heightProof 4
cert_coverFacet 0 286
cert_cover_5 0 0 0 1 2 3 14 286 3
cert_coverFacet 1 902
cert_cover_5 1 2 0 1 6 7 262 902 2
cert_coverFacet 2 538
cert_cover_2 2 2 0 3 8 26 538 3
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
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0754

end
end BundlePart13

section BundlePart14
/- Source: ProjectionCertificates/R_m16e10q1_0755.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0755

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [451, 173, 805, 197, 325, 569, 905, 342, 602, 818, 706, 898, 244, 308, 248, 712, 37, 69, 133, 261, 41, 137, 521, 545, 193, 321, 385, 769, 82, 274, 530, 194, 322, 578, 386, 642, 770, 52, 84, 276, 164, 292, 196, 324, 56, 88, 536, 168, 200, 584, 648, 240, 304, 560, 800, 704, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_451, vertices_173, vertices_805, vertices_197, vertices_325, vertices_569, vertices_905, vertices_342, vertices_602, vertices_818, vertices_706, vertices_898, vertices_244, vertices_308, vertices_248, vertices_712] (by decide +kernel)
  polygons := literalFinset [vertices_37, vertices_69, vertices_133, vertices_261, vertices_41, vertices_137, vertices_521, vertices_545, vertices_193, vertices_321, vertices_385, vertices_769, vertices_82, vertices_274, vertices_530, vertices_194, vertices_322, vertices_578, vertices_386, vertices_642, vertices_770, vertices_52, vertices_84, vertices_276, vertices_164, vertices_292, vertices_196, vertices_324, vertices_56, vertices_88, vertices_536, vertices_168, vertices_200, vertices_584, vertices_648, vertices_240, vertices_304, vertices_560, vertices_800, vertices_704, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_451), (false, vertices_173), (false, vertices_805), (false, vertices_197), (false, vertices_325), (false, vertices_569), (false, vertices_905), (true, vertices_82), (true, vertices_274), (true, vertices_530), (true, vertices_578), (true, vertices_642), (true, vertices_770), (true, vertices_52), (true, vertices_84), (true, vertices_276), (true, vertices_88), (true, vertices_200), (true, vertices_584), (true, vertices_240), (true, vertices_304), (true, vertices_704)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 16 18 21 24 26 27 28 29 30
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_451) then 17 else
  if p.val = (false, vertices_173) then 19 else
  if p.val = (false, vertices_805) then 20 else
  if p.val = (false, vertices_197) then 0 else
  if p.val = (false, vertices_325) then 1 else
  if p.val = (false, vertices_569) then 22 else
  if p.val = (false, vertices_905) then 23 else
  if p.val = (true, vertices_82) then 2 else
  if p.val = (true, vertices_274) then 3 else
  if p.val = (true, vertices_530) then 4 else
  if p.val = (true, vertices_578) then 5 else
  if p.val = (true, vertices_642) then 6 else
  if p.val = (true, vertices_770) then 7 else
  if p.val = (true, vertices_52) then 8 else
  if p.val = (true, vertices_84) then 9 else
  if p.val = (true, vertices_276) then 10 else
  if p.val = (true, vertices_88) then 11 else
  if p.val = (true, vertices_200) then 12 else
  if p.val = (true, vertices_584) then 13 else
  if p.val = (true, vertices_240) then 25 else
  if p.val = (true, vertices_304) then 14 else
  if p.val = (true, vertices_704) then 15 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_197), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_325), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_82), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_274), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_530), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_578), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_642), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_770), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_52), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_84), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_276), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_88), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_200), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_584), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_304), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_704), by decide +kernel⟩
  | 16 => Sum.inl 0
  | 17 => Sum.inr ⟨(false, vertices_451), by decide +kernel⟩
  | 18 => Sum.inl 1
  | 19 => Sum.inr ⟨(false, vertices_173), by decide +kernel⟩
  | 20 => Sum.inr ⟨(false, vertices_805), by decide +kernel⟩
  | 21 => Sum.inl 2
  | 22 => Sum.inr ⟨(false, vertices_569), by decide +kernel⟩
  | 23 => Sum.inr ⟨(false, vertices_905), by decide +kernel⟩
  | 24 => Sum.inl 3
  | 25 => Sum.inr ⟨(true, vertices_240), by decide +kernel⟩
  | 26 => Sum.inl 4
  | 27 => Sum.inl 5
  | 28 => Sum.inl 6
  | 29 => Sum.inl 7
  | 30 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 3 4 5 6 240
cert_row_4 1 0 1 3 5 7 342 82 1
cert_row_4 2 0 2 3 5 8 602 82 1
cert_row_4 3 0 3 4 7 8 818 274 2
cert_rows
cert_pivot_2 6 1 2 0
cert_heightProof 4
cert_coverFacet 0 342
cert_cover_5 0 1 0 1 3 5 82 342 1
cert_coverFacet 1 602
cert_cover_5 1 2 0 2 3 5 82 602 1
cert_coverFacet 2 818
cert_cover_5 2 3 0 3 4 7 274 818 2
cert_coverFacet 3 706
cert_cover_2 3 5 0 6 8 194 706 3
cert_coverFacet 4 898
cert_cover_2 4 6 0 7 8 386 898 3
cert_coverFacet 5 244
cert_cover_5 5 0 1 3 4 5 52 244 3
cert_coverFacet 6 308
cert_cover_2 6 3 1 4 7 52 308 3
cert_coverFacet 7 248
cert_cover_5 7 0 2 3 4 5 56 248 3
cert_coverFacet 8 712
cert_cover_2 8 5 2 6 8 200 712 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0755

end
end BundlePart14

section BundlePart15
/- Source: ProjectionCertificates/R_m16e10q1_0756.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0756

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [43, 395, 563, 771, 453, 233, 865, 286, 58, 850, 668, 396, 340, 596, 740, 696, 11, 35, 259, 515, 41, 137, 97, 545, 193, 321, 385, 769, 26, 42, 266, 50, 274, 530, 770, 28, 140, 268, 84, 276, 532, 196, 324, 580, 388, 644, 56, 664, 168, 392, 560, 336, 592, 224, 608, 672, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_43, vertices_395, vertices_563, vertices_771, vertices_453, vertices_233, vertices_865, vertices_286, vertices_58, vertices_850, vertices_668, vertices_396, vertices_340, vertices_596, vertices_740, vertices_696] (by decide +kernel)
  polygons := literalFinset [vertices_11, vertices_35, vertices_259, vertices_515, vertices_41, vertices_137, vertices_97, vertices_545, vertices_193, vertices_321, vertices_385, vertices_769, vertices_26, vertices_42, vertices_266, vertices_50, vertices_274, vertices_530, vertices_770, vertices_28, vertices_140, vertices_268, vertices_84, vertices_276, vertices_532, vertices_196, vertices_324, vertices_580, vertices_388, vertices_644, vertices_56, vertices_664, vertices_168, vertices_392, vertices_560, vertices_336, vertices_592, vertices_224, vertices_608, vertices_672, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_43), (false, vertices_395), (false, vertices_563), (false, vertices_771), (false, vertices_453), (false, vertices_233), (false, vertices_865), (true, vertices_26), (true, vertices_274), (true, vertices_28), (true, vertices_140), (true, vertices_268), (true, vertices_84), (true, vertices_276), (true, vertices_532), (true, vertices_580), (true, vertices_644), (true, vertices_56), (true, vertices_664), (true, vertices_336), (true, vertices_592), (true, vertices_672)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 16 19 21 24 25 27 28 29 30
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_43) then 0 else
  if p.val = (false, vertices_395) then 17 else
  if p.val = (false, vertices_563) then 18 else
  if p.val = (false, vertices_771) then 1 else
  if p.val = (false, vertices_453) then 20 else
  if p.val = (false, vertices_233) then 22 else
  if p.val = (false, vertices_865) then 26 else
  if p.val = (true, vertices_26) then 2 else
  if p.val = (true, vertices_274) then 3 else
  if p.val = (true, vertices_28) then 4 else
  if p.val = (true, vertices_140) then 5 else
  if p.val = (true, vertices_268) then 6 else
  if p.val = (true, vertices_84) then 7 else
  if p.val = (true, vertices_276) then 8 else
  if p.val = (true, vertices_532) then 9 else
  if p.val = (true, vertices_580) then 10 else
  if p.val = (true, vertices_644) then 11 else
  if p.val = (true, vertices_56) then 12 else
  if p.val = (true, vertices_664) then 23 else
  if p.val = (true, vertices_336) then 13 else
  if p.val = (true, vertices_592) then 14 else
  if p.val = (true, vertices_672) then 15 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_43), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_771), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_26), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_274), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_28), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_140), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_268), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_84), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_276), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_532), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_580), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_644), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_56), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_336), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_592), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_672), by decide +kernel⟩
  | 16 => Sum.inl 0
  | 17 => Sum.inr ⟨(false, vertices_395), by decide +kernel⟩
  | 18 => Sum.inr ⟨(false, vertices_563), by decide +kernel⟩
  | 19 => Sum.inl 1
  | 20 => Sum.inr ⟨(false, vertices_453), by decide +kernel⟩
  | 21 => Sum.inl 2
  | 22 => Sum.inr ⟨(false, vertices_233), by decide +kernel⟩
  | 23 => Sum.inr ⟨(true, vertices_664), by decide +kernel⟩
  | 24 => Sum.inl 3
  | 25 => Sum.inl 4
  | 26 => Sum.inr ⟨(false, vertices_865), by decide +kernel⟩
  | 27 => Sum.inl 5
  | 28 => Sum.inl 6
  | 29 => Sum.inl 7
  | 30 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 1 4 5 6 8 740 196 1
cert_row_2 1 2 3 6 8 664
cert_row_4 2 0 1 2 3 7 286 26 1
cert_row_4 3 0 3 5 7 8 850 274 2
cert_rows
cert_pivot_2 4 6 1 0
cert_heightProof 4
cert_coverFacet 0 286
cert_cover_5 0 2 0 1 2 3 26 286 1
cert_coverFacet 1 58
cert_cover_2 1 2 0 3 4 26 58 3
cert_coverFacet 2 850
cert_cover_5 2 3 0 3 5 7 274 850 2
cert_coverFacet 3 668
cert_cover_5 3 1 1 2 3 6 28 668 3
cert_coverFacet 4 396
cert_cover_2 4 2 1 6 7 140 396 3
cert_coverFacet 5 340
cert_cover_2 5 3 1 5 7 84 340 3
cert_coverFacet 6 596
cert_cover_2 6 3 1 5 8 84 596 3
cert_coverFacet 7 740
cert_cover_5 7 0 1 4 5 6 196 740 1
cert_coverFacet 8 696
cert_cover_5 8 1 2 3 4 6 56 696 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0756

end
end BundlePart15

section BundlePart16
/- Source: ProjectionCertificates/R_m16e10q1_0757.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0757

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [451, 29, 45, 341, 229, 569, 433, 782, 410, 666, 738, 834, 284, 620, 836, 688, 13, 21, 37, 69, 25, 41, 49, 273, 161, 193, 321, 385, 154, 266, 522, 194, 322, 578, 386, 642, 770, 28, 44, 268, 524, 276, 100, 324, 580, 772, 280, 536, 552, 176, 560, 400, 656, 224, 608, 672, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_451, vertices_29, vertices_45, vertices_341, vertices_229, vertices_569, vertices_433, vertices_782, vertices_410, vertices_666, vertices_738, vertices_834, vertices_284, vertices_620, vertices_836, vertices_688] (by decide +kernel)
  polygons := literalFinset [vertices_13, vertices_21, vertices_37, vertices_69, vertices_25, vertices_41, vertices_49, vertices_273, vertices_161, vertices_193, vertices_321, vertices_385, vertices_154, vertices_266, vertices_522, vertices_194, vertices_322, vertices_578, vertices_386, vertices_642, vertices_770, vertices_28, vertices_44, vertices_268, vertices_524, vertices_276, vertices_100, vertices_324, vertices_580, vertices_772, vertices_280, vertices_536, vertices_552, vertices_176, vertices_560, vertices_400, vertices_656, vertices_224, vertices_608, vertices_672, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_451), (false, vertices_29), (false, vertices_45), (false, vertices_341), (false, vertices_229), (false, vertices_569), (false, vertices_433), (true, vertices_154), (true, vertices_266), (true, vertices_522), (true, vertices_578), (true, vertices_642), (true, vertices_770), (true, vertices_268), (true, vertices_524), (true, vertices_580), (true, vertices_772), (true, vertices_280), (true, vertices_656), (true, vertices_608), (true, vertices_672), (true, vertices_832)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 16 19 22 24 26 27 28 29 30
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_451) then 17 else
  if p.val = (false, vertices_29) then 0 else
  if p.val = (false, vertices_45) then 1 else
  if p.val = (false, vertices_341) then 20 else
  if p.val = (false, vertices_229) then 21 else
  if p.val = (false, vertices_569) then 23 else
  if p.val = (false, vertices_433) then 25 else
  if p.val = (true, vertices_154) then 18 else
  if p.val = (true, vertices_266) then 2 else
  if p.val = (true, vertices_522) then 3 else
  if p.val = (true, vertices_578) then 4 else
  if p.val = (true, vertices_642) then 5 else
  if p.val = (true, vertices_770) then 6 else
  if p.val = (true, vertices_268) then 7 else
  if p.val = (true, vertices_524) then 8 else
  if p.val = (true, vertices_580) then 9 else
  if p.val = (true, vertices_772) then 10 else
  if p.val = (true, vertices_280) then 11 else
  if p.val = (true, vertices_656) then 12 else
  if p.val = (true, vertices_608) then 13 else
  if p.val = (true, vertices_672) then 14 else
  if p.val = (true, vertices_832) then 15 else
  0
cert_priority
cert_nodeAtPriority_50 1 29 0 45 266 522 578 642 770 268 524 580 772 280 656 608 672 832 451 154 341 229 569 433
cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 2 3 6 154
cert_row_4 1 0 1 2 7 8 782 266 1
cert_row_4 2 0 4 5 6 8 738 194 1
cert_row_4 3 1 2 4 5 8 620 44 3
cert_rows
cert_pivot_2 3 7 0 1
cert_heightProof 4
cert_coverFacet 0 782
cert_cover_5 0 1 0 1 2 7 266 782 1
cert_coverFacet 1 410
cert_cover_5 1 0 0 2 3 7 154 410 3
cert_coverFacet 2 666
cert_cover_5 2 0 0 2 3 8 154 666 3
cert_coverFacet 3 738
cert_cover_5 3 2 0 4 5 6 194 738 1
cert_coverFacet 4 834
cert_cover_2 4 5 0 7 8 322 834 3
cert_coverFacet 5 284
cert_cover_2 5 2 1 3 7 28 284 3
cert_coverFacet 6 620
cert_cover_5 6 3 1 2 4 5 44 620 3
cert_coverFacet 7 836
cert_cover_2 7 5 1 7 8 324 836 3
cert_coverFacet 8 688
cert_cover_2 8 4 3 6 8 176 688 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0757

end
end BundlePart16

section BundlePart17
/- Source: ProjectionCertificates/R_m16e10q1_0758.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0758

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [419, 93, 525, 581, 233, 809, 961, 158, 174, 534, 550, 818, 466, 556, 852, 216, 13, 69, 517, 41, 73, 521, 161, 289, 193, 577, 385, 769, 142, 22, 38, 518, 146, 274, 530, 162, 290, 546, 386, 28, 44, 524, 84, 532, 548, 580, 88, 152, 168, 552, 200, 208, 336, 784, 800, 448, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_419, vertices_93, vertices_525, vertices_581, vertices_233, vertices_809, vertices_961, vertices_158, vertices_174, vertices_534, vertices_550, vertices_818, vertices_466, vertices_556, vertices_852, vertices_216] (by decide +kernel)
  polygons := literalFinset [vertices_13, vertices_69, vertices_517, vertices_41, vertices_73, vertices_521, vertices_161, vertices_289, vertices_193, vertices_577, vertices_385, vertices_769, vertices_142, vertices_22, vertices_38, vertices_518, vertices_146, vertices_274, vertices_530, vertices_162, vertices_290, vertices_546, vertices_386, vertices_28, vertices_44, vertices_524, vertices_84, vertices_532, vertices_548, vertices_580, vertices_88, vertices_152, vertices_168, vertices_552, vertices_200, vertices_208, vertices_336, vertices_784, vertices_800, vertices_448, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_419), (false, vertices_93), (false, vertices_525), (false, vertices_581), (false, vertices_233), (false, vertices_809), (false, vertices_961), (true, vertices_142), (true, vertices_22), (true, vertices_38), (true, vertices_518), (true, vertices_146), (true, vertices_274), (true, vertices_530), (true, vertices_546), (true, vertices_44), (true, vertices_532), (true, vertices_548), (true, vertices_152), (true, vertices_208), (true, vertices_336), (true, vertices_784)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 16 19 21 24 25 26 28 29 30
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_419) then 17 else
  if p.val = (false, vertices_93) then 20 else
  if p.val = (false, vertices_525) then 0 else
  if p.val = (false, vertices_581) then 1 else
  if p.val = (false, vertices_233) then 22 else
  if p.val = (false, vertices_809) then 23 else
  if p.val = (false, vertices_961) then 27 else
  if p.val = (true, vertices_142) then 18 else
  if p.val = (true, vertices_22) then 2 else
  if p.val = (true, vertices_38) then 3 else
  if p.val = (true, vertices_518) then 4 else
  if p.val = (true, vertices_146) then 5 else
  if p.val = (true, vertices_274) then 6 else
  if p.val = (true, vertices_530) then 7 else
  if p.val = (true, vertices_546) then 8 else
  if p.val = (true, vertices_44) then 9 else
  if p.val = (true, vertices_532) then 10 else
  if p.val = (true, vertices_548) then 11 else
  if p.val = (true, vertices_152) then 12 else
  if p.val = (true, vertices_208) then 13 else
  if p.val = (true, vertices_336) then 14 else
  if p.val = (true, vertices_784) then 15 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_525), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_581), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_22), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_38), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_518), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_146), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_274), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_530), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_546), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_44), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_532), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_548), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_152), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_208), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_336), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_784), by decide +kernel⟩
  | 16 => Sum.inl 0
  | 17 => Sum.inr ⟨(false, vertices_419), by decide +kernel⟩
  | 18 => Sum.inr ⟨(true, vertices_142), by decide +kernel⟩
  | 19 => Sum.inl 1
  | 20 => Sum.inr ⟨(false, vertices_93), by decide +kernel⟩
  | 21 => Sum.inl 2
  | 22 => Sum.inr ⟨(false, vertices_233), by decide +kernel⟩
  | 23 => Sum.inr ⟨(false, vertices_809), by decide +kernel⟩
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
cert_row_2 0 0 1 2 6 142
cert_row_4 1 0 3 4 7 8 818 274 2
cert_row_4 2 0 3 5 6 7 466 146 2
cert_row_4 3 1 3 5 7 8 852 84 3
cert_rows
cert_pivot_2 2 4 0 1
cert_heightProof 4
cert_coverFacet 0 158
cert_cover_5 0 0 0 1 2 3 142 158 3
cert_coverFacet 1 174
cert_cover_5 1 0 0 1 2 4 142 174 3
cert_coverFacet 2 534
cert_cover_2 2 1 0 3 8 22 534 3
cert_coverFacet 3 550
cert_cover_2 3 1 0 4 8 38 550 3
cert_coverFacet 4 818
cert_cover_5 4 1 0 3 4 7 274 818 2
cert_coverFacet 5 466
cert_cover_5 5 2 0 3 5 6 146 466 2
cert_coverFacet 6 556
cert_cover_2 6 2 1 4 8 44 556 3
cert_coverFacet 7 852
cert_cover_5 7 3 1 3 5 7 84 852 3
cert_coverFacet 8 216
cert_cover_2 8 3 2 5 6 88 216 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0758

end
end BundlePart17

section BundlePart18
/- Source: ProjectionCertificates/R_m16e10q1_0759.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0759

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [171, 267, 355, 653, 841, 625, 673, 158, 286, 690, 306, 780, 372, 212, 964, 720, 11, 35, 259, 137, 265, 521, 97, 161, 545, 321, 577, 641, 30, 138, 266, 50, 146, 274, 162, 290, 140, 268, 524, 84, 148, 276, 196, 324, 644, 772, 776, 112, 304, 560, 208, 592, 656, 352, 672, 704, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_171, vertices_267, vertices_355, vertices_653, vertices_841, vertices_625, vertices_673, vertices_158, vertices_286, vertices_690, vertices_306, vertices_780, vertices_372, vertices_212, vertices_964, vertices_720] (by decide +kernel)
  polygons := literalFinset [vertices_11, vertices_35, vertices_259, vertices_137, vertices_265, vertices_521, vertices_97, vertices_161, vertices_545, vertices_321, vertices_577, vertices_641, vertices_30, vertices_138, vertices_266, vertices_50, vertices_146, vertices_274, vertices_162, vertices_290, vertices_140, vertices_268, vertices_524, vertices_84, vertices_148, vertices_276, vertices_196, vertices_324, vertices_644, vertices_772, vertices_776, vertices_112, vertices_304, vertices_560, vertices_208, vertices_592, vertices_656, vertices_352, vertices_672, vertices_704, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_171), (false, vertices_267), (false, vertices_355), (false, vertices_653), (false, vertices_841), (false, vertices_625), (false, vertices_673), (true, vertices_30), (true, vertices_50), (true, vertices_146), (true, vertices_274), (true, vertices_268), (true, vertices_84), (true, vertices_148), (true, vertices_276), (true, vertices_196), (true, vertices_324), (true, vertices_772), (true, vertices_304), (true, vertices_208), (true, vertices_656), (true, vertices_704)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 16 20 22 24 26 27 28 29 30
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_171) then 17 else
  if p.val = (false, vertices_267) then 0 else
  if p.val = (false, vertices_355) then 18 else
  if p.val = (false, vertices_653) then 21 else
  if p.val = (false, vertices_841) then 23 else
  if p.val = (false, vertices_625) then 25 else
  if p.val = (false, vertices_673) then 1 else
  if p.val = (true, vertices_30) then 19 else
  if p.val = (true, vertices_50) then 2 else
  if p.val = (true, vertices_146) then 3 else
  if p.val = (true, vertices_274) then 4 else
  if p.val = (true, vertices_268) then 5 else
  if p.val = (true, vertices_84) then 6 else
  if p.val = (true, vertices_148) then 7 else
  if p.val = (true, vertices_276) then 8 else
  if p.val = (true, vertices_196) then 9 else
  if p.val = (true, vertices_324) then 10 else
  if p.val = (true, vertices_772) then 11 else
  if p.val = (true, vertices_304) then 12 else
  if p.val = (true, vertices_208) then 13 else
  if p.val = (true, vertices_656) then 14 else
  if p.val = (true, vertices_704) then 15 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_267), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_673), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_50), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_146), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_274), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_268), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_84), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_148), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_276), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_196), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_324), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_772), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_304), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_208), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_656), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_704), by decide +kernel⟩
  | 16 => Sum.inl 0
  | 17 => Sum.inr ⟨(false, vertices_171), by decide +kernel⟩
  | 18 => Sum.inr ⟨(false, vertices_355), by decide +kernel⟩
  | 19 => Sum.inr ⟨(true, vertices_30), by decide +kernel⟩
  | 20 => Sum.inl 1
  | 21 => Sum.inr ⟨(false, vertices_653), by decide +kernel⟩
  | 22 => Sum.inl 2
  | 23 => Sum.inr ⟨(false, vertices_841), by decide +kernel⟩
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
cert_row_2 0 0 1 2 3 30
cert_row_4 1 0 3 4 6 8 690 50 3
cert_row_4 2 1 3 4 5 7 372 84 2
cert_row_4 3 1 5 6 7 8 964 196 3
cert_rows
cert_pivot_2 2 0 3 1
cert_heightProof 4
cert_coverFacet 0 158
cert_cover_5 0 0 0 1 2 6 30 158 3
cert_coverFacet 1 286
cert_cover_5 1 0 0 1 2 7 30 286 3
cert_coverFacet 2 690
cert_cover_5 2 1 0 3 4 6 50 690 3
cert_coverFacet 3 306
cert_cover_2 3 3 0 4 7 50 306 3
cert_coverFacet 4 780
cert_cover_2 4 2 1 7 8 268 780 3
cert_coverFacet 5 372
cert_cover_5 5 2 1 3 4 5 84 372 2
cert_coverFacet 6 212
cert_cover_2 6 3 1 5 6 84 212 3
cert_coverFacet 7 964
cert_cover_5 7 3 1 5 6 7 196 964 3
cert_coverFacet 8 720
cert_cover_2 8 5 3 6 8 208 720 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0759

end
end BundlePart18

section BundlePart19
/- Source: ProjectionCertificates/R_m16e10q1_0760.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0760

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [279, 395, 531, 707, 565, 453, 581, 186, 282, 690, 620, 372, 312, 360, 680, 968, 19, 131, 259, 515, 21, 69, 261, 517, 529, 193, 577, 385, 26, 138, 266, 178, 274, 530, 642, 52, 276, 100, 548, 324, 580, 56, 280, 104, 168, 296, 552, 328, 584, 392, 648, 304, 560, 352, 672, 448, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_279, vertices_395, vertices_531, vertices_707, vertices_565, vertices_453, vertices_581, vertices_186, vertices_282, vertices_690, vertices_620, vertices_372, vertices_312, vertices_360, vertices_680, vertices_968] (by decide +kernel)
  polygons := literalFinset [vertices_19, vertices_131, vertices_259, vertices_515, vertices_21, vertices_69, vertices_261, vertices_517, vertices_529, vertices_193, vertices_577, vertices_385, vertices_26, vertices_138, vertices_266, vertices_178, vertices_274, vertices_530, vertices_642, vertices_52, vertices_276, vertices_100, vertices_548, vertices_324, vertices_580, vertices_56, vertices_280, vertices_104, vertices_168, vertices_296, vertices_552, vertices_328, vertices_584, vertices_392, vertices_648, vertices_304, vertices_560, vertices_352, vertices_672, vertices_448, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_279), (false, vertices_395), (false, vertices_531), (false, vertices_707), (false, vertices_565), (false, vertices_453), (false, vertices_581), (true, vertices_26), (true, vertices_178), (true, vertices_100), (true, vertices_56), (true, vertices_280), (true, vertices_104), (true, vertices_168), (true, vertices_296), (true, vertices_552), (true, vertices_328), (true, vertices_584), (true, vertices_648), (true, vertices_304), (true, vertices_352), (true, vertices_672)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 22 16 20 25 26 27 28 29 30
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_279) then 17 else
  if p.val = (false, vertices_395) then 21 else
  if p.val = (false, vertices_531) then 0 else
  if p.val = (false, vertices_707) then 23 else
  if p.val = (false, vertices_565) then 18 else
  if p.val = (false, vertices_453) then 19 else
  if p.val = (false, vertices_581) then 1 else
  if p.val = (true, vertices_26) then 2 else
  if p.val = (true, vertices_178) then 24 else
  if p.val = (true, vertices_100) then 3 else
  if p.val = (true, vertices_56) then 4 else
  if p.val = (true, vertices_280) then 5 else
  if p.val = (true, vertices_104) then 6 else
  if p.val = (true, vertices_168) then 7 else
  if p.val = (true, vertices_296) then 8 else
  if p.val = (true, vertices_552) then 9 else
  if p.val = (true, vertices_328) then 10 else
  if p.val = (true, vertices_584) then 11 else
  if p.val = (true, vertices_648) then 12 else
  if p.val = (true, vertices_304) then 13 else
  if p.val = (true, vertices_352) then 14 else
  if p.val = (true, vertices_672) then 15 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_531), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_581), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_26), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_100), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_56), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_280), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_104), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_168), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_296), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_552), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_328), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_584), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_648), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_304), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_352), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_672), by decide +kernel⟩
  | 16 => Sum.inl 1
  | 17 => Sum.inr ⟨(false, vertices_279), by decide +kernel⟩
  | 18 => Sum.inr ⟨(false, vertices_565), by decide +kernel⟩
  | 19 => Sum.inr ⟨(false, vertices_453), by decide +kernel⟩
  | 20 => Sum.inl 2
  | 21 => Sum.inr ⟨(false, vertices_395), by decide +kernel⟩
  | 22 => Sum.inl 0
  | 23 => Sum.inr ⟨(false, vertices_707), by decide +kernel⟩
  | 24 => Sum.inr ⟨(true, vertices_178), by decide +kernel⟩
  | 25 => Sum.inl 3
  | 26 => Sum.inl 4
  | 27 => Sum.inl 5
  | 28 => Sum.inl 6
  | 29 => Sum.inl 7
  | 30 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 3 4 6 178
cert_row_4 1 1 3 4 5 7 372 52 3
cert_row_4 2 1 2 4 5 8 620 100 1
cert_row_4 3 2 5 6 7 8 968 328 2
cert_rows
cert_pivot_2 0 3 1 2
cert_heightProof 4
cert_coverFacet 0 186
cert_cover_5 0 0 0 2 3 4 26 186 3
cert_coverFacet 1 282
cert_cover_2 1 2 0 3 7 26 282 3
cert_coverFacet 2 690
cert_cover_5 2 0 0 3 4 8 178 690 3
cert_coverFacet 3 620
cert_cover_5 3 2 1 2 4 5 100 620 1
cert_coverFacet 4 372
cert_cover_5 4 1 1 3 4 5 52 372 3
cert_coverFacet 5 312
cert_cover_2 5 3 2 4 7 56 312 3
cert_coverFacet 6 360
cert_cover_2 6 4 2 5 7 104 360 3
cert_coverFacet 7 680
cert_cover_2 7 4 2 6 8 168 680 3
cert_coverFacet 8 968
cert_cover_5 8 3 2 5 6 7 328 968 2
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0760

end
end BundlePart19

section BundlePart20
/- Source: ProjectionCertificates/R_m16e10q1_0761.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0761

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [151, 395, 595, 771, 117, 837, 389, 810, 650, 658, 236, 460, 180, 696, 360, 880, 19, 131, 259, 515, 21, 69, 133, 261, 81, 577, 385, 769, 138, 266, 522, 146, 530, 642, 770, 204, 52, 148, 100, 164, 324, 388, 104, 168, 296, 552, 328, 392, 648, 112, 176, 560, 592, 656, 352, 800, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_151, vertices_395, vertices_595, vertices_771, vertices_117, vertices_837, vertices_389, vertices_810, vertices_650, vertices_658, vertices_236, vertices_460, vertices_180, vertices_696, vertices_360, vertices_880] (by decide +kernel)
  polygons := literalFinset [vertices_19, vertices_131, vertices_259, vertices_515, vertices_21, vertices_69, vertices_133, vertices_261, vertices_81, vertices_577, vertices_385, vertices_769, vertices_138, vertices_266, vertices_522, vertices_146, vertices_530, vertices_642, vertices_770, vertices_204, vertices_52, vertices_148, vertices_100, vertices_164, vertices_324, vertices_388, vertices_104, vertices_168, vertices_296, vertices_552, vertices_328, vertices_392, vertices_648, vertices_112, vertices_176, vertices_560, vertices_592, vertices_656, vertices_352, vertices_800, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_151), (false, vertices_395), (false, vertices_595), (false, vertices_771), (false, vertices_117), (false, vertices_837), (false, vertices_389), (true, vertices_522), (true, vertices_642), (true, vertices_204), (true, vertices_164), (true, vertices_104), (true, vertices_168), (true, vertices_296), (true, vertices_552), (true, vertices_328), (true, vertices_648), (true, vertices_176), (true, vertices_560), (true, vertices_656), (true, vertices_352), (true, vertices_800)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 16 22 20 25 26 27 28 29 30
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_151) then 17 else
  if p.val = (false, vertices_395) then 18 else
  if p.val = (false, vertices_595) then 19 else
  if p.val = (false, vertices_771) then 0 else
  if p.val = (false, vertices_117) then 23 else
  if p.val = (false, vertices_837) then 24 else
  if p.val = (false, vertices_389) then 1 else
  if p.val = (true, vertices_522) then 2 else
  if p.val = (true, vertices_642) then 3 else
  if p.val = (true, vertices_204) then 21 else
  if p.val = (true, vertices_164) then 4 else
  if p.val = (true, vertices_104) then 5 else
  if p.val = (true, vertices_168) then 6 else
  if p.val = (true, vertices_296) then 7 else
  if p.val = (true, vertices_552) then 8 else
  if p.val = (true, vertices_328) then 9 else
  if p.val = (true, vertices_648) then 10 else
  if p.val = (true, vertices_176) then 11 else
  if p.val = (true, vertices_560) then 12 else
  if p.val = (true, vertices_656) then 13 else
  if p.val = (true, vertices_352) then 14 else
  if p.val = (true, vertices_800) then 15 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_771), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_389), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_522), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_642), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_164), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_104), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_168), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_296), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_552), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_328), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_648), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_176), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_560), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_656), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_352), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_800), by decide +kernel⟩
  | 16 => Sum.inl 0
  | 17 => Sum.inr ⟨(false, vertices_151), by decide +kernel⟩
  | 18 => Sum.inr ⟨(false, vertices_395), by decide +kernel⟩
  | 19 => Sum.inr ⟨(false, vertices_595), by decide +kernel⟩
  | 20 => Sum.inl 2
  | 21 => Sum.inr ⟨(true, vertices_204), by decide +kernel⟩
  | 22 => Sum.inl 1
  | 23 => Sum.inr ⟨(false, vertices_117), by decide +kernel⟩
  | 24 => Sum.inr ⟨(false, vertices_837), by decide +kernel⟩
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
cert_row_4 1 0 2 4 7 8 810 266 2
cert_row_4 2 2 3 4 6 8 696 168 1
cert_row_4 3 3 4 5 7 8 880 112 3
cert_rows
cert_pivot_2 1 0 2 3
cert_heightProof 4
cert_coverFacet 0 810
cert_cover_5 0 1 0 2 4 7 266 810 2
cert_coverFacet 1 650
cert_cover_2 1 2 0 6 8 138 650 3
cert_coverFacet 2 658
cert_cover_2 2 3 0 6 8 146 658 3
cert_coverFacet 3 236
cert_cover_5 3 0 1 2 4 5 204 236 2
cert_coverFacet 4 460
cert_cover_5 4 0 1 2 5 7 204 460 3
cert_coverFacet 5 180
cert_cover_2 5 3 1 4 6 52 180 3
cert_coverFacet 6 696
cert_cover_5 6 2 2 3 4 6 168 696 1
cert_coverFacet 7 360
cert_cover_2 7 4 2 5 7 104 360 3
cert_coverFacet 8 880
cert_cover_5 8 3 3 4 5 7 112 880 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0761

end
end BundlePart20

section BundlePart21
/- Source: ProjectionCertificates/R_m16e10q1_0762.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0762

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [279, 531, 899, 565, 709, 325, 457, 186, 538, 714, 434, 620, 372, 568, 360, 424, 19, 259, 515, 21, 69, 261, 517, 529, 193, 321, 385, 641, 26, 138, 522, 178, 274, 530, 386, 642, 52, 276, 100, 548, 324, 580, 56, 536, 104, 168, 296, 552, 200, 328, 584, 392, 304, 560, 352, 416, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_279, vertices_531, vertices_899, vertices_565, vertices_709, vertices_325, vertices_457, vertices_186, vertices_538, vertices_714, vertices_434, vertices_620, vertices_372, vertices_568, vertices_360, vertices_424] (by decide +kernel)
  polygons := literalFinset [vertices_19, vertices_259, vertices_515, vertices_21, vertices_69, vertices_261, vertices_517, vertices_529, vertices_193, vertices_321, vertices_385, vertices_641, vertices_26, vertices_138, vertices_522, vertices_178, vertices_274, vertices_530, vertices_386, vertices_642, vertices_52, vertices_276, vertices_100, vertices_548, vertices_324, vertices_580, vertices_56, vertices_536, vertices_104, vertices_168, vertices_296, vertices_552, vertices_200, vertices_328, vertices_584, vertices_392, vertices_304, vertices_560, vertices_352, vertices_416, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_279), (false, vertices_531), (false, vertices_899), (false, vertices_565), (false, vertices_709), (false, vertices_325), (false, vertices_457), (true, vertices_26), (true, vertices_138), (true, vertices_522), (true, vertices_178), (true, vertices_100), (true, vertices_56), (true, vertices_536), (true, vertices_104), (true, vertices_168), (true, vertices_296), (true, vertices_552), (true, vertices_584), (true, vertices_304), (true, vertices_352), (true, vertices_416)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 16 20 23 25 26 27 28 29 30
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_279) then 17 else
  if p.val = (false, vertices_531) then 0 else
  if p.val = (false, vertices_899) then 18 else
  if p.val = (false, vertices_565) then 21 else
  if p.val = (false, vertices_709) then 22 else
  if p.val = (false, vertices_325) then 1 else
  if p.val = (false, vertices_457) then 24 else
  if p.val = (true, vertices_26) then 2 else
  if p.val = (true, vertices_138) then 3 else
  if p.val = (true, vertices_522) then 4 else
  if p.val = (true, vertices_178) then 19 else
  if p.val = (true, vertices_100) then 5 else
  if p.val = (true, vertices_56) then 6 else
  if p.val = (true, vertices_536) then 7 else
  if p.val = (true, vertices_104) then 8 else
  if p.val = (true, vertices_168) then 9 else
  if p.val = (true, vertices_296) then 10 else
  if p.val = (true, vertices_552) then 11 else
  if p.val = (true, vertices_584) then 12 else
  if p.val = (true, vertices_304) then 13 else
  if p.val = (true, vertices_352) then 14 else
  if p.val = (true, vertices_416) then 15 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_531), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_325), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_26), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_138), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_522), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_100), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_56), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_536), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_104), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_168), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_296), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_552), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_584), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_304), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_352), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_416), by decide +kernel⟩
  | 16 => Sum.inl 0
  | 17 => Sum.inr ⟨(false, vertices_279), by decide +kernel⟩
  | 18 => Sum.inr ⟨(false, vertices_899), by decide +kernel⟩
  | 19 => Sum.inr ⟨(true, vertices_178), by decide +kernel⟩
  | 20 => Sum.inl 1
  | 21 => Sum.inr ⟨(false, vertices_565), by decide +kernel⟩
  | 22 => Sum.inr ⟨(false, vertices_709), by decide +kernel⟩
  | 23 => Sum.inl 2
  | 24 => Sum.inr ⟨(false, vertices_457), by decide +kernel⟩
  | 25 => Sum.inl 3
  | 26 => Sum.inl 4
  | 27 => Sum.inl 5
  | 28 => Sum.inl 6
  | 29 => Sum.inl 7
  | 30 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 1 3 4 5 7 372 52 3
cert_row_2 1 0 3 4 6 178
cert_row_4 2 0 2 5 6 8 714 138 2
cert_row_4 3 1 2 4 5 8 620 100 1
cert_rows
cert_pivot_2 7 3 0 1
cert_heightProof 4
cert_coverFacet 0 186
cert_cover_5 0 1 0 2 3 4 26 186 3
cert_coverFacet 1 538
cert_cover_2 1 2 0 3 8 26 538 3
cert_coverFacet 2 714
cert_cover_5 2 2 0 2 5 6 138 714 2
cert_coverFacet 3 434
cert_cover_5 3 1 0 3 4 7 178 434 3
cert_coverFacet 4 620
cert_cover_5 4 3 1 2 4 5 100 620 1
cert_coverFacet 5 372
cert_cover_5 5 0 1 3 4 5 52 372 3
cert_coverFacet 6 568
cert_cover_2 6 3 2 4 8 56 568 3
cert_coverFacet 7 360
cert_cover_2 7 4 2 5 7 104 360 3
cert_coverFacet 8 424
cert_cover_2 8 4 2 6 7 168 424 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0762

end
end BundlePart21

section BundlePart22
/- Source: ProjectionCertificates/R_m16e10q1_0763.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0763

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [775, 557, 165, 453, 185, 201, 841, 310, 566, 218, 594, 402, 962, 420, 632, 432, 37, 133, 261, 517, 41, 73, 137, 521, 161, 193, 321, 769, 54, 262, 518, 82, 146, 274, 530, 194, 578, 386, 770, 164, 292, 548, 388, 56, 88, 152, 552, 200, 584, 176, 304, 560, 592, 400, 416, 448, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_775, vertices_557, vertices_165, vertices_453, vertices_185, vertices_201, vertices_841, vertices_310, vertices_566, vertices_218, vertices_594, vertices_402, vertices_962, vertices_420, vertices_632, vertices_432] (by decide +kernel)
  polygons := literalFinset [vertices_37, vertices_133, vertices_261, vertices_517, vertices_41, vertices_73, vertices_137, vertices_521, vertices_161, vertices_193, vertices_321, vertices_769, vertices_54, vertices_262, vertices_518, vertices_82, vertices_146, vertices_274, vertices_530, vertices_194, vertices_578, vertices_386, vertices_770, vertices_164, vertices_292, vertices_548, vertices_388, vertices_56, vertices_88, vertices_152, vertices_552, vertices_200, vertices_584, vertices_176, vertices_304, vertices_560, vertices_592, vertices_400, vertices_416, vertices_448, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_775), (false, vertices_557), (false, vertices_165), (false, vertices_453), (false, vertices_185), (false, vertices_201), (false, vertices_841), (true, vertices_54), (true, vertices_82), (true, vertices_146), (true, vertices_274), (true, vertices_530), (true, vertices_194), (true, vertices_578), (true, vertices_386), (true, vertices_292), (true, vertices_88), (true, vertices_304), (true, vertices_560), (true, vertices_592), (true, vertices_400), (true, vertices_416)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 16 19 22 25 26 27 28 29 30
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_775) then 17 else
  if p.val = (false, vertices_557) then 20 else
  if p.val = (false, vertices_165) then 0 else
  if p.val = (false, vertices_453) then 21 else
  if p.val = (false, vertices_185) then 23 else
  if p.val = (false, vertices_201) then 1 else
  if p.val = (false, vertices_841) then 24 else
  if p.val = (true, vertices_54) then 18 else
  if p.val = (true, vertices_82) then 2 else
  if p.val = (true, vertices_146) then 3 else
  if p.val = (true, vertices_274) then 4 else
  if p.val = (true, vertices_530) then 5 else
  if p.val = (true, vertices_194) then 6 else
  if p.val = (true, vertices_578) then 7 else
  if p.val = (true, vertices_386) then 8 else
  if p.val = (true, vertices_292) then 9 else
  if p.val = (true, vertices_88) then 10 else
  if p.val = (true, vertices_304) then 11 else
  if p.val = (true, vertices_560) then 12 else
  if p.val = (true, vertices_592) then 13 else
  if p.val = (true, vertices_400) then 14 else
  if p.val = (true, vertices_416) then 15 else
  0
cert_priority
cert_nodeAtPriority_39 0 165 1 201 82 146 274 530 194 578 386 292 88 304 560 592 400 416 775 54 557 453 185 841
cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 1 3 4 54
cert_row_4 1 0 5 6 7 8 962 194 3
cert_row_4 2 0 2 3 5 6 218 82 1
cert_row_4 3 2 3 4 5 8 632 56 3
cert_rows
cert_pivot_2 1 7 0 2
cert_heightProof 4
cert_coverFacet 0 310
cert_cover_5 0 0 0 1 3 7 54 310 3
cert_coverFacet 1 566
cert_cover_5 1 0 0 1 3 8 54 566 3
cert_coverFacet 2 218
cert_cover_5 2 2 0 2 3 5 82 218 1
cert_coverFacet 3 594
cert_cover_2 3 3 0 5 8 82 594 3
cert_coverFacet 4 402
cert_cover_2 4 3 0 6 7 146 402 3
cert_coverFacet 5 962
cert_cover_5 5 1 0 5 6 7 194 962 3
cert_coverFacet 6 420
cert_cover_2 6 4 1 6 7 164 420 3
cert_coverFacet 7 632
cert_cover_5 7 3 2 3 4 5 56 632 3
cert_coverFacet 8 432
cert_cover_2 8 4 3 6 7 176 432 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0763

end
end BundlePart22

section BundlePart23
/- Source: ProjectionCertificates/R_m16e10q1_0764.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0764

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [775, 179, 403, 611, 233, 961, 542, 278, 562, 188, 204, 332, 780, 468, 568, 872, 147, 35, 259, 515, 97, 161, 193, 577, 385, 769, 22, 262, 518, 50, 274, 530, 546, 28, 76, 140, 268, 524, 148, 276, 196, 324, 772, 56, 536, 104, 168, 552, 200, 328, 776, 176, 560, 400, 608, 448, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_775, vertices_179, vertices_403, vertices_611, vertices_233, vertices_961, vertices_542, vertices_278, vertices_562, vertices_188, vertices_204, vertices_332, vertices_780, vertices_468, vertices_568, vertices_872] (by decide +kernel)
  polygons := literalFinset [vertices_147, vertices_35, vertices_259, vertices_515, vertices_97, vertices_161, vertices_193, vertices_577, vertices_385, vertices_769, vertices_22, vertices_262, vertices_518, vertices_50, vertices_274, vertices_530, vertices_546, vertices_28, vertices_76, vertices_140, vertices_268, vertices_524, vertices_148, vertices_276, vertices_196, vertices_324, vertices_772, vertices_56, vertices_536, vertices_104, vertices_168, vertices_552, vertices_200, vertices_328, vertices_776, vertices_176, vertices_560, vertices_400, vertices_608, vertices_448, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_775), (false, vertices_179), (false, vertices_403), (false, vertices_611), (false, vertices_233), (false, vertices_961), (true, vertices_22), (true, vertices_530), (true, vertices_28), (true, vertices_76), (true, vertices_140), (true, vertices_268), (true, vertices_524), (true, vertices_148), (true, vertices_276), (true, vertices_196), (true, vertices_324), (true, vertices_56), (true, vertices_536), (true, vertices_552), (true, vertices_328), (true, vertices_776), (true, vertices_560)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 19 17 23 25 26 27 29 30 31
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_775) then 18 else
  if p.val = (false, vertices_179) then 20 else
  if p.val = (false, vertices_403) then 21 else
  if p.val = (false, vertices_611) then 22 else
  if p.val = (false, vertices_233) then 24 else
  if p.val = (false, vertices_961) then 28 else
  if p.val = (true, vertices_22) then 0 else
  if p.val = (true, vertices_530) then 1 else
  if p.val = (true, vertices_28) then 2 else
  if p.val = (true, vertices_76) then 3 else
  if p.val = (true, vertices_140) then 4 else
  if p.val = (true, vertices_268) then 5 else
  if p.val = (true, vertices_524) then 6 else
  if p.val = (true, vertices_148) then 7 else
  if p.val = (true, vertices_276) then 8 else
  if p.val = (true, vertices_196) then 9 else
  if p.val = (true, vertices_324) then 10 else
  if p.val = (true, vertices_56) then 11 else
  if p.val = (true, vertices_536) then 12 else
  if p.val = (true, vertices_552) then 13 else
  if p.val = (true, vertices_328) then 14 else
  if p.val = (true, vertices_776) then 15 else
  if p.val = (true, vertices_560) then 16 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_22), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_530), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_28), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_76), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_140), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_268), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_524), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_148), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_276), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_196), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_324), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_56), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_536), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_552), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_328), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_776), by decide +kernel⟩
  | 16 => Sum.inr ⟨(true, vertices_560), by decide +kernel⟩
  | 17 => Sum.inl 1
  | 18 => Sum.inr ⟨(false, vertices_775), by decide +kernel⟩
  | 19 => Sum.inl 0
  | 20 => Sum.inr ⟨(false, vertices_179), by decide +kernel⟩
  | 21 => Sum.inr ⟨(false, vertices_403), by decide +kernel⟩
  | 22 => Sum.inr ⟨(false, vertices_611), by decide +kernel⟩
  | 23 => Sum.inl 2
  | 24 => Sum.inr ⟨(false, vertices_233), by decide +kernel⟩
  | 25 => Sum.inl 3
  | 26 => Sum.inl 4
  | 27 => Sum.inl 5
  | 28 => Sum.inr ⟨(false, vertices_961), by decide +kernel⟩
  | 29 => Sum.inl 6
  | 30 => Sum.inl 7
  | 31 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 2 3 8 542 22 2
cert_row_4 1 2 4 5 7 8 872 104 3
cert_row_4 2 1 2 3 4 6 188 28 3
cert_row_4 3 1 3 5 6 7 468 148 2
cert_rows
cert_pivot_2 0 8 2 1
cert_heightProof 4
cert_coverFacet 0 542
cert_cover_5 0 0 0 1 2 3 22 542 2
cert_coverFacet 1 278
cert_cover_2 1 1 0 3 7 22 278 3
cert_coverFacet 2 562
cert_cover_2 2 3 0 4 8 50 562 3
cert_coverFacet 3 188
cert_cover_5 3 2 1 2 3 4 28 188 3
cert_coverFacet 4 204
cert_cover_2 4 2 1 5 6 76 204 3
cert_coverFacet 5 332
cert_cover_2 5 2 1 5 7 76 332 3
cert_coverFacet 6 780
cert_cover_2 6 2 1 7 8 268 780 3
cert_coverFacet 7 468
cert_cover_5 7 3 1 3 5 6 148 468 2
cert_coverFacet 8 568
cert_cover_2 8 3 2 4 8 56 568 3
cert_coverFacet 9 872
cert_cover_5 9 1 2 4 5 7 104 872 3
cert_coveringFacets_5
cert_coveringProof
cert_certificate 4 10
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0764

end
end BundlePart23

section BundlePart24
/- Source: ProjectionCertificates/R_m16e10q1_0765.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0765

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [203, 587, 557, 185, 625, 465, 270, 526, 598, 454, 426, 300, 340, 788, 804, 944, 75, 41, 137, 521, 49, 81, 145, 545, 193, 577, 14, 70, 262, 518, 138, 266, 522, 194, 578, 386, 44, 268, 524, 84, 276, 532, 292, 548, 324, 772, 168, 296, 176, 560, 336, 592, 400, 784, 416, 800, 448]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_203, vertices_587, vertices_557, vertices_185, vertices_625, vertices_465, vertices_270, vertices_526, vertices_598, vertices_454, vertices_426, vertices_300, vertices_340, vertices_788, vertices_804, vertices_944] (by decide +kernel)
  polygons := literalFinset [vertices_75, vertices_41, vertices_137, vertices_521, vertices_49, vertices_81, vertices_145, vertices_545, vertices_193, vertices_577, vertices_14, vertices_70, vertices_262, vertices_518, vertices_138, vertices_266, vertices_522, vertices_194, vertices_578, vertices_386, vertices_44, vertices_268, vertices_524, vertices_84, vertices_276, vertices_532, vertices_292, vertices_548, vertices_324, vertices_772, vertices_168, vertices_296, vertices_176, vertices_560, vertices_336, vertices_592, vertices_400, vertices_784, vertices_416, vertices_800, vertices_448] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_203), (false, vertices_587), (false, vertices_557), (false, vertices_185), (false, vertices_625), (false, vertices_465), (true, vertices_14), (true, vertices_70), (true, vertices_262), (true, vertices_518), (true, vertices_266), (true, vertices_386), (true, vertices_268), (true, vertices_84), (true, vertices_276), (true, vertices_532), (true, vertices_292), (true, vertices_324), (true, vertices_772), (true, vertices_296), (true, vertices_784), (true, vertices_416), (true, vertices_800)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 17 20 22 24 27 28 29 30 31
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_203) then 18 else
  if p.val = (false, vertices_587) then 19 else
  if p.val = (false, vertices_557) then 21 else
  if p.val = (false, vertices_185) then 23 else
  if p.val = (false, vertices_625) then 25 else
  if p.val = (false, vertices_465) then 26 else
  if p.val = (true, vertices_14) then 0 else
  if p.val = (true, vertices_70) then 1 else
  if p.val = (true, vertices_262) then 2 else
  if p.val = (true, vertices_518) then 3 else
  if p.val = (true, vertices_266) then 4 else
  if p.val = (true, vertices_386) then 5 else
  if p.val = (true, vertices_268) then 6 else
  if p.val = (true, vertices_84) then 7 else
  if p.val = (true, vertices_276) then 8 else
  if p.val = (true, vertices_532) then 9 else
  if p.val = (true, vertices_292) then 10 else
  if p.val = (true, vertices_324) then 11 else
  if p.val = (true, vertices_772) then 12 else
  if p.val = (true, vertices_296) then 13 else
  if p.val = (true, vertices_784) then 14 else
  if p.val = (true, vertices_416) then 15 else
  if p.val = (true, vertices_800) then 16 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_14), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_70), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_262), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_518), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_266), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_386), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_268), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_84), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_276), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_532), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_292), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_324), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_772), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_296), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_784), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_416), by decide +kernel⟩
  | 16 => Sum.inr ⟨(true, vertices_800), by decide +kernel⟩
  | 17 => Sum.inl 0
  | 18 => Sum.inr ⟨(false, vertices_203), by decide +kernel⟩
  | 19 => Sum.inr ⟨(false, vertices_587), by decide +kernel⟩
  | 20 => Sum.inl 1
  | 21 => Sum.inr ⟨(false, vertices_557), by decide +kernel⟩
  | 22 => Sum.inl 2
  | 23 => Sum.inr ⟨(false, vertices_185), by decide +kernel⟩
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
cert_row_4 0 0 2 4 6 7 426 138 2
cert_row_4 1 3 4 6 7 8 944 176 3
cert_row_4 2 0 1 3 5 8 598 70 2
cert_row_4 3 0 1 5 6 7 454 70 3
cert_rows
cert_pivot_2 2 4 3 0
cert_heightProof 4
cert_coverFacet 0 270
cert_cover_2 0 1 0 2 7 14 270 3
cert_coverFacet 1 526
cert_cover_2 1 1 0 2 8 14 526 3
cert_coverFacet 2 598
cert_cover_5 2 2 0 1 3 5 70 598 2
cert_coverFacet 3 454
cert_cover_5 3 3 0 1 5 6 70 454 3
cert_coverFacet 4 426
cert_cover_5 4 0 0 2 4 6 138 426 2
cert_coverFacet 5 300
cert_cover_2 5 2 1 4 7 44 300 3
cert_coverFacet 6 340
cert_cover_2 6 3 1 5 7 84 340 3
cert_coverFacet 7 788
cert_cover_2 7 3 1 7 8 276 788 3
cert_coverFacet 8 804
cert_cover_2 8 4 1 7 8 292 804 3
cert_coverFacet 9 944
cert_cover_5 9 1 3 4 6 7 176 944 3
cert_coveringFacets_5
cert_coveringProof
cert_certificate 4 10
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0765

end
end BundlePart24

section BundlePart25
/- Source: ProjectionCertificates/R_m16e10q1_0766.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0766

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [787, 803, 597, 405, 357, 617, 662, 186, 282, 362, 674, 716, 452, 408, 680, 456, 771, 21, 69, 261, 273, 529, 97, 289, 545, 577, 26, 42, 266, 146, 274, 530, 162, 290, 546, 642, 148, 532, 196, 324, 580, 388, 644, 152, 280, 104, 168, 552, 200, 328, 584, 392, 648, 400, 352, 672, 448]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_787, vertices_803, vertices_597, vertices_405, vertices_357, vertices_617, vertices_662, vertices_186, vertices_282, vertices_362, vertices_674, vertices_716, vertices_452, vertices_408, vertices_680, vertices_456] (by decide +kernel)
  polygons := literalFinset [vertices_771, vertices_21, vertices_69, vertices_261, vertices_273, vertices_529, vertices_97, vertices_289, vertices_545, vertices_577, vertices_26, vertices_42, vertices_266, vertices_146, vertices_274, vertices_530, vertices_162, vertices_290, vertices_546, vertices_642, vertices_148, vertices_532, vertices_196, vertices_324, vertices_580, vertices_388, vertices_644, vertices_152, vertices_280, vertices_104, vertices_168, vertices_552, vertices_200, vertices_328, vertices_584, vertices_392, vertices_648, vertices_400, vertices_352, vertices_672, vertices_448] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_787), (false, vertices_803), (false, vertices_597), (false, vertices_405), (false, vertices_357), (false, vertices_617), (true, vertices_26), (true, vertices_42), (true, vertices_266), (true, vertices_146), (true, vertices_162), (true, vertices_642), (true, vertices_196), (true, vertices_644), (true, vertices_152), (true, vertices_280), (true, vertices_168), (true, vertices_200), (true, vertices_328), (true, vertices_392), (true, vertices_648), (true, vertices_672), (true, vertices_448)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 17 20 24 26 27 28 29 30 31
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_787) then 18 else
  if p.val = (false, vertices_803) then 19 else
  if p.val = (false, vertices_597) then 21 else
  if p.val = (false, vertices_405) then 22 else
  if p.val = (false, vertices_357) then 23 else
  if p.val = (false, vertices_617) then 25 else
  if p.val = (true, vertices_26) then 0 else
  if p.val = (true, vertices_42) then 1 else
  if p.val = (true, vertices_266) then 2 else
  if p.val = (true, vertices_146) then 3 else
  if p.val = (true, vertices_162) then 4 else
  if p.val = (true, vertices_642) then 5 else
  if p.val = (true, vertices_196) then 6 else
  if p.val = (true, vertices_644) then 7 else
  if p.val = (true, vertices_152) then 8 else
  if p.val = (true, vertices_280) then 9 else
  if p.val = (true, vertices_168) then 10 else
  if p.val = (true, vertices_200) then 11 else
  if p.val = (true, vertices_328) then 12 else
  if p.val = (true, vertices_392) then 13 else
  if p.val = (true, vertices_648) then 14 else
  if p.val = (true, vertices_672) then 15 else
  if p.val = (true, vertices_448) then 16 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_26), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_42), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_266), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_146), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_162), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_642), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_196), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_644), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_152), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_280), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_168), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_200), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_328), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_392), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_648), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_672), by decide +kernel⟩
  | 16 => Sum.inr ⟨(true, vertices_448), by decide +kernel⟩
  | 17 => Sum.inl 0
  | 18 => Sum.inr ⟨(false, vertices_787), by decide +kernel⟩
  | 19 => Sum.inr ⟨(false, vertices_803), by decide +kernel⟩
  | 20 => Sum.inl 1
  | 21 => Sum.inr ⟨(false, vertices_597), by decide +kernel⟩
  | 22 => Sum.inr ⟨(false, vertices_405), by decide +kernel⟩
  | 23 => Sum.inr ⟨(false, vertices_357), by decide +kernel⟩
  | 24 => Sum.inl 2
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
cert_row_4 0 0 2 4 5 7 362 42 3
cert_row_4 1 0 2 3 4 6 186 26 3
cert_row_4 2 0 1 3 6 8 662 146 1
cert_row_4 3 1 2 5 6 8 716 196 1
cert_rows
cert_pivot_2 7 4 0 1
cert_heightProof 4
cert_coverFacet 0 662
cert_cover_5 0 2 0 1 3 6 146 662 1
cert_coverFacet 1 186
cert_cover_5 1 1 0 2 3 4 26 186 3
cert_coverFacet 2 282
cert_cover_2 2 2 0 3 7 26 282 3
cert_coverFacet 3 362
cert_cover_5 3 0 0 2 4 5 42 362 3
cert_coverFacet 4 674
cert_cover_2 4 4 0 6 8 162 674 3
cert_coverFacet 5 716
cert_cover_5 5 3 1 2 5 6 196 716 1
cert_coverFacet 6 452
cert_cover_2 6 5 1 6 7 196 452 3
cert_coverFacet 7 408
cert_cover_2 7 3 2 6 7 152 408 3
cert_coverFacet 8 680
cert_cover_2 8 4 2 6 8 168 680 3
cert_coverFacet 9 456
cert_cover_2 9 5 2 6 7 200 456 3
cert_coveringFacets_5
cert_coveringProof
cert_certificate 4 10
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0766

end
end BundlePart25

section BundlePart26
/- Source: ProjectionCertificates/R_m16e10q1_0767.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0767

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [787, 803, 341, 661, 613, 361, 406, 186, 538, 618, 418, 716, 452, 664, 424, 456, 771, 21, 69, 517, 273, 529, 97, 289, 545, 321, 26, 42, 522, 146, 274, 530, 162, 290, 546, 386, 148, 276, 196, 324, 580, 388, 644, 152, 536, 104, 168, 296, 200, 328, 584, 392, 648, 656, 608, 416, 448]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_787, vertices_803, vertices_341, vertices_661, vertices_613, vertices_361, vertices_406, vertices_186, vertices_538, vertices_618, vertices_418, vertices_716, vertices_452, vertices_664, vertices_424, vertices_456] (by decide +kernel)
  polygons := literalFinset [vertices_771, vertices_21, vertices_69, vertices_517, vertices_273, vertices_529, vertices_97, vertices_289, vertices_545, vertices_321, vertices_26, vertices_42, vertices_522, vertices_146, vertices_274, vertices_530, vertices_162, vertices_290, vertices_546, vertices_386, vertices_148, vertices_276, vertices_196, vertices_324, vertices_580, vertices_388, vertices_644, vertices_152, vertices_536, vertices_104, vertices_168, vertices_296, vertices_200, vertices_328, vertices_584, vertices_392, vertices_648, vertices_656, vertices_608, vertices_416, vertices_448] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_787), (false, vertices_803), (false, vertices_341), (false, vertices_661), (false, vertices_613), (false, vertices_361), (true, vertices_26), (true, vertices_42), (true, vertices_522), (true, vertices_146), (true, vertices_162), (true, vertices_386), (true, vertices_196), (true, vertices_388), (true, vertices_152), (true, vertices_536), (true, vertices_168), (true, vertices_200), (true, vertices_584), (true, vertices_392), (true, vertices_648), (true, vertices_416), (true, vertices_448)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 17 20 24 26 27 28 29 30 31
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_787) then 18 else
  if p.val = (false, vertices_803) then 19 else
  if p.val = (false, vertices_341) then 21 else
  if p.val = (false, vertices_661) then 22 else
  if p.val = (false, vertices_613) then 23 else
  if p.val = (false, vertices_361) then 25 else
  if p.val = (true, vertices_26) then 0 else
  if p.val = (true, vertices_42) then 1 else
  if p.val = (true, vertices_522) then 2 else
  if p.val = (true, vertices_146) then 3 else
  if p.val = (true, vertices_162) then 4 else
  if p.val = (true, vertices_386) then 5 else
  if p.val = (true, vertices_196) then 6 else
  if p.val = (true, vertices_388) then 7 else
  if p.val = (true, vertices_152) then 8 else
  if p.val = (true, vertices_536) then 9 else
  if p.val = (true, vertices_168) then 10 else
  if p.val = (true, vertices_200) then 11 else
  if p.val = (true, vertices_584) then 12 else
  if p.val = (true, vertices_392) then 13 else
  if p.val = (true, vertices_648) then 14 else
  if p.val = (true, vertices_416) then 15 else
  if p.val = (true, vertices_448) then 16 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_26), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_42), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_522), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_146), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_162), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_386), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_196), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_388), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_152), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_536), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_168), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_200), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_584), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_392), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_648), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_416), by decide +kernel⟩
  | 16 => Sum.inr ⟨(true, vertices_448), by decide +kernel⟩
  | 17 => Sum.inl 0
  | 18 => Sum.inr ⟨(false, vertices_787), by decide +kernel⟩
  | 19 => Sum.inr ⟨(false, vertices_803), by decide +kernel⟩
  | 20 => Sum.inl 1
  | 21 => Sum.inr ⟨(false, vertices_341), by decide +kernel⟩
  | 22 => Sum.inr ⟨(false, vertices_661), by decide +kernel⟩
  | 23 => Sum.inr ⟨(false, vertices_613), by decide +kernel⟩
  | 24 => Sum.inl 2
  | 25 => Sum.inr ⟨(false, vertices_361), by decide +kernel⟩
  | 26 => Sum.inl 3
  | 27 => Sum.inl 4
  | 28 => Sum.inl 5
  | 29 => Sum.inl 6
  | 30 => Sum.inl 7
  | 31 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 3 6 7 406 146 1
cert_row_4 1 0 2 3 4 6 186 26 3
cert_row_4 2 0 2 4 5 8 618 42 3
cert_row_4 3 1 2 5 6 8 716 196 1
cert_rows
cert_pivot_2 7 3 0 1
cert_heightProof 4
cert_coverFacet 0 406
cert_cover_5 0 0 0 1 3 6 146 406 1
cert_coverFacet 1 186
cert_cover_5 1 1 0 2 3 4 26 186 3
cert_coverFacet 2 538
cert_cover_2 2 2 0 3 8 26 538 3
cert_coverFacet 3 618
cert_cover_5 3 2 0 2 4 5 42 618 3
cert_coverFacet 4 418
cert_cover_2 4 4 0 6 7 162 418 3
cert_coverFacet 5 716
cert_cover_5 5 3 1 2 5 6 196 716 1
cert_coverFacet 6 452
cert_cover_2 6 5 1 6 7 196 452 3
cert_coverFacet 7 664
cert_cover_2 7 3 2 6 8 152 664 3
cert_coverFacet 8 424
cert_cover_2 8 4 2 6 7 168 424 3
cert_coverFacet 9 456
cert_cover_2 9 5 2 6 7 200 456 3
cert_coveringFacets_5
cert_coveringProof
cert_certificate 4 10
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0767

end
end BundlePart26

section BundlePart27
/- Source: ProjectionCertificates/R_m16e10q1_0768.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0768

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [271, 539, 419, 547, 525, 677, 453, 282, 626, 306, 220, 668, 332, 376, 720, 992, 11, 35, 259, 515, 13, 133, 261, 517, 521, 161, 545, 385, 26, 266, 50, 274, 530, 290, 546, 156, 76, 268, 524, 196, 324, 644, 88, 280, 536, 328, 112, 304, 208, 592, 656, 352, 608, 416, 672, 448, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_271, vertices_539, vertices_419, vertices_547, vertices_525, vertices_677, vertices_453, vertices_282, vertices_626, vertices_306, vertices_220, vertices_668, vertices_332, vertices_376, vertices_720, vertices_992] (by decide +kernel)
  polygons := literalFinset [vertices_11, vertices_35, vertices_259, vertices_515, vertices_13, vertices_133, vertices_261, vertices_517, vertices_521, vertices_161, vertices_545, vertices_385, vertices_26, vertices_266, vertices_50, vertices_274, vertices_530, vertices_290, vertices_546, vertices_156, vertices_76, vertices_268, vertices_524, vertices_196, vertices_324, vertices_644, vertices_88, vertices_280, vertices_536, vertices_328, vertices_112, vertices_304, vertices_208, vertices_592, vertices_656, vertices_352, vertices_608, vertices_416, vertices_672, vertices_448, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_271), (false, vertices_539), (false, vertices_419), (false, vertices_547), (false, vertices_525), (false, vertices_677), (false, vertices_453), (true, vertices_50), (true, vertices_274), (true, vertices_156), (true, vertices_76), (true, vertices_88), (true, vertices_280), (true, vertices_328), (true, vertices_112), (true, vertices_304), (true, vertices_208), (true, vertices_592), (true, vertices_656), (true, vertices_352), (true, vertices_608), (true, vertices_704)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 16 22 20 25 26 27 28 29 30
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_271) then 17 else
  if p.val = (false, vertices_539) then 18 else
  if p.val = (false, vertices_419) then 19 else
  if p.val = (false, vertices_547) then 0 else
  if p.val = (false, vertices_525) then 1 else
  if p.val = (false, vertices_677) then 23 else
  if p.val = (false, vertices_453) then 24 else
  if p.val = (true, vertices_50) then 2 else
  if p.val = (true, vertices_274) then 3 else
  if p.val = (true, vertices_156) then 21 else
  if p.val = (true, vertices_76) then 4 else
  if p.val = (true, vertices_88) then 5 else
  if p.val = (true, vertices_280) then 6 else
  if p.val = (true, vertices_328) then 7 else
  if p.val = (true, vertices_112) then 8 else
  if p.val = (true, vertices_304) then 9 else
  if p.val = (true, vertices_208) then 10 else
  if p.val = (true, vertices_592) then 11 else
  if p.val = (true, vertices_656) then 12 else
  if p.val = (true, vertices_352) then 13 else
  if p.val = (true, vertices_608) then 14 else
  if p.val = (true, vertices_704) then 15 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_547), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_525), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_50), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_274), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_76), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_88), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_280), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_328), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_112), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_304), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_208), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_592), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_656), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_352), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_608), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_704), by decide +kernel⟩
  | 16 => Sum.inl 0
  | 17 => Sum.inr ⟨(false, vertices_271), by decide +kernel⟩
  | 18 => Sum.inr ⟨(false, vertices_539), by decide +kernel⟩
  | 19 => Sum.inr ⟨(false, vertices_419), by decide +kernel⟩
  | 20 => Sum.inl 2
  | 21 => Sum.inr ⟨(true, vertices_156), by decide +kernel⟩
  | 22 => Sum.inl 1
  | 23 => Sum.inr ⟨(false, vertices_677), by decide +kernel⟩
  | 24 => Sum.inr ⟨(false, vertices_453), by decide +kernel⟩
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
cert_row_4 1 0 3 4 5 8 626 50 3
cert_row_4 2 2 3 4 5 7 376 88 2
cert_row_4 3 4 5 6 7 8 992 352 2
cert_rows
cert_pivot_2 1 0 2 4
cert_heightProof 4
cert_coverFacet 0 282
cert_cover_2 0 2 0 3 7 26 282 3
cert_coverFacet 1 626
cert_cover_5 1 1 0 3 4 5 50 626 3
cert_coverFacet 2 306
cert_cover_2 2 3 0 4 7 50 306 3
cert_coverFacet 3 220
cert_cover_5 3 0 1 2 3 5 156 220 3
cert_coverFacet 4 668
cert_cover_5 4 0 1 2 3 8 156 668 3
cert_coverFacet 5 332
cert_cover_2 5 2 1 5 7 76 332 3
cert_coverFacet 6 376
cert_cover_5 6 2 2 3 4 5 88 376 2
cert_coverFacet 7 720
cert_cover_2 7 5 3 6 8 208 720 3
cert_coverFacet 8 992
cert_cover_5 8 3 4 5 6 7 352 992 2
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0768

end
end BundlePart27

section BundlePart28
/- Source: ProjectionCertificates/R_m16e10q1_0769.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0769

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [171, 115, 147, 653, 617, 849, 657, 214, 454, 866, 418, 796, 428, 340, 660, 808, 19, 35, 131, 41, 137, 521, 81, 145, 529, 97, 577, 641, 198, 82, 146, 98, 162, 290, 322, 386, 140, 268, 524, 84, 148, 276, 532, 324, 388, 644, 168, 296, 552, 776, 336, 656, 784, 608, 416, 800, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_171, vertices_115, vertices_147, vertices_653, vertices_617, vertices_849, vertices_657, vertices_214, vertices_454, vertices_866, vertices_418, vertices_796, vertices_428, vertices_340, vertices_660, vertices_808] (by decide +kernel)
  polygons := literalFinset [vertices_19, vertices_35, vertices_131, vertices_41, vertices_137, vertices_521, vertices_81, vertices_145, vertices_529, vertices_97, vertices_577, vertices_641, vertices_198, vertices_82, vertices_146, vertices_98, vertices_162, vertices_290, vertices_322, vertices_386, vertices_140, vertices_268, vertices_524, vertices_84, vertices_148, vertices_276, vertices_532, vertices_324, vertices_388, vertices_644, vertices_168, vertices_296, vertices_552, vertices_776, vertices_336, vertices_656, vertices_784, vertices_608, vertices_416, vertices_800, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_171), (false, vertices_115), (false, vertices_147), (false, vertices_653), (false, vertices_617), (false, vertices_849), (false, vertices_657), (true, vertices_198), (true, vertices_290), (true, vertices_322), (true, vertices_386), (true, vertices_268), (true, vertices_84), (true, vertices_148), (true, vertices_276), (true, vertices_532), (true, vertices_324), (true, vertices_388), (true, vertices_296), (true, vertices_776), (true, vertices_416), (true, vertices_800)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 16 20 22 24 26 27 28 29 30
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_171) then 17 else
  if p.val = (false, vertices_115) then 18 else
  if p.val = (false, vertices_147) then 0 else
  if p.val = (false, vertices_653) then 21 else
  if p.val = (false, vertices_617) then 23 else
  if p.val = (false, vertices_849) then 25 else
  if p.val = (false, vertices_657) then 1 else
  if p.val = (true, vertices_198) then 19 else
  if p.val = (true, vertices_290) then 2 else
  if p.val = (true, vertices_322) then 3 else
  if p.val = (true, vertices_386) then 4 else
  if p.val = (true, vertices_268) then 5 else
  if p.val = (true, vertices_84) then 6 else
  if p.val = (true, vertices_148) then 7 else
  if p.val = (true, vertices_276) then 8 else
  if p.val = (true, vertices_532) then 9 else
  if p.val = (true, vertices_324) then 10 else
  if p.val = (true, vertices_388) then 11 else
  if p.val = (true, vertices_296) then 12 else
  if p.val = (true, vertices_776) then 13 else
  if p.val = (true, vertices_416) then 14 else
  if p.val = (true, vertices_800) then 15 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_147), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_657), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_290), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_322), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_386), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_268), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_84), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_148), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_276), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_532), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_324), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_388), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_296), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_776), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_416), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_800), by decide +kernel⟩
  | 16 => Sum.inl 0
  | 17 => Sum.inr ⟨(false, vertices_171), by decide +kernel⟩
  | 18 => Sum.inr ⟨(false, vertices_115), by decide +kernel⟩
  | 19 => Sum.inr ⟨(true, vertices_198), by decide +kernel⟩
  | 20 => Sum.inl 1
  | 21 => Sum.inr ⟨(false, vertices_653), by decide +kernel⟩
  | 22 => Sum.inl 2
  | 23 => Sum.inr ⟨(false, vertices_617), by decide +kernel⟩
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
cert_row_4 0 1 2 3 7 8 796 268 2
cert_row_4 1 0 4 5 7 8 866 98 3
cert_row_2 2 0 1 5 6 198
cert_row_4 3 1 2 4 6 7 428 140 2
cert_rows
cert_pivot_2 3 8 0 1
cert_heightProof 4
cert_coverFacet 0 214
cert_cover_5 0 2 0 1 3 5 198 214 2
cert_coverFacet 1 454
cert_cover_5 1 2 0 1 5 7 198 454 3
cert_coverFacet 2 866
cert_cover_5 2 1 0 4 5 7 98 866 3
cert_coverFacet 3 418
cert_cover_2 3 4 0 6 7 162 418 3
cert_coverFacet 4 796
cert_cover_5 4 0 1 2 3 7 268 796 2
cert_coverFacet 5 428
cert_cover_5 5 3 1 2 4 6 140 428 2
cert_coverFacet 6 340
cert_cover_2 6 3 1 5 7 84 340 3
cert_coverFacet 7 660
cert_cover_2 7 3 1 6 8 148 660 3
cert_coverFacet 8 808
cert_cover_2 8 4 2 7 8 296 808 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0769

end
end BundlePart28

section BundlePart29
/- Source: ProjectionCertificates/R_m16e10q1_0770.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0770

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [775, 651, 211, 275, 617, 201, 849, 310, 150, 646, 684, 180, 868, 440, 472, 360, 19, 131, 259, 515, 73, 137, 521, 81, 273, 193, 577, 769, 22, 134, 262, 518, 146, 274, 642, 52, 148, 164, 292, 548, 644, 772, 408, 104, 168, 296, 552, 200, 328, 648, 176, 304, 208, 336, 352, 608, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_775, vertices_651, vertices_211, vertices_275, vertices_617, vertices_201, vertices_849, vertices_310, vertices_150, vertices_646, vertices_684, vertices_180, vertices_868, vertices_440, vertices_472, vertices_360] (by decide +kernel)
  polygons := literalFinset [vertices_19, vertices_131, vertices_259, vertices_515, vertices_73, vertices_137, vertices_521, vertices_81, vertices_273, vertices_193, vertices_577, vertices_769, vertices_22, vertices_134, vertices_262, vertices_518, vertices_146, vertices_274, vertices_642, vertices_52, vertices_148, vertices_164, vertices_292, vertices_548, vertices_644, vertices_772, vertices_408, vertices_104, vertices_168, vertices_296, vertices_552, vertices_200, vertices_328, vertices_648, vertices_176, vertices_304, vertices_208, vertices_336, vertices_352, vertices_608, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_775), (false, vertices_651), (false, vertices_211), (false, vertices_275), (false, vertices_617), (false, vertices_201), (false, vertices_849), (true, vertices_22), (true, vertices_134), (true, vertices_52), (true, vertices_148), (true, vertices_164), (true, vertices_292), (true, vertices_548), (true, vertices_644), (true, vertices_408), (true, vertices_168), (true, vertices_296), (true, vertices_328), (true, vertices_176), (true, vertices_304), (true, vertices_352)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 16 20 21 24 26 27 28 29 30
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_775) then 17 else
  if p.val = (false, vertices_651) then 18 else
  if p.val = (false, vertices_211) then 19 else
  if p.val = (false, vertices_275) then 0 else
  if p.val = (false, vertices_617) then 22 else
  if p.val = (false, vertices_201) then 1 else
  if p.val = (false, vertices_849) then 25 else
  if p.val = (true, vertices_22) then 2 else
  if p.val = (true, vertices_134) then 3 else
  if p.val = (true, vertices_52) then 4 else
  if p.val = (true, vertices_148) then 5 else
  if p.val = (true, vertices_164) then 6 else
  if p.val = (true, vertices_292) then 7 else
  if p.val = (true, vertices_548) then 8 else
  if p.val = (true, vertices_644) then 9 else
  if p.val = (true, vertices_408) then 23 else
  if p.val = (true, vertices_168) then 10 else
  if p.val = (true, vertices_296) then 11 else
  if p.val = (true, vertices_328) then 12 else
  if p.val = (true, vertices_176) then 13 else
  if p.val = (true, vertices_304) then 14 else
  if p.val = (true, vertices_352) then 15 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_275), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_201), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_22), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_134), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_52), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_148), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_164), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_292), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_548), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_644), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_168), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_296), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_328), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_176), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_304), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_352), by decide +kernel⟩
  | 16 => Sum.inl 0
  | 17 => Sum.inr ⟨(false, vertices_775), by decide +kernel⟩
  | 18 => Sum.inr ⟨(false, vertices_651), by decide +kernel⟩
  | 19 => Sum.inr ⟨(false, vertices_211), by decide +kernel⟩
  | 20 => Sum.inl 1
  | 21 => Sum.inl 2
  | 22 => Sum.inr ⟨(false, vertices_617), by decide +kernel⟩
  | 23 => Sum.inr ⟨(true, vertices_408), by decide +kernel⟩
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
cert_row_4 0 0 1 3 4 7 310 22 3
cert_row_2 1 2 3 6 7 408
cert_row_4 2 1 2 4 6 8 684 164 1
cert_row_4 3 1 4 5 7 8 868 292 2
cert_rows
cert_pivot_2 0 3 2 1
cert_heightProof 4
cert_coverFacet 0 310
cert_cover_5 0 0 0 1 3 4 22 310 3
cert_coverFacet 1 150
cert_cover_2 1 1 0 3 6 22 150 3
cert_coverFacet 2 646
cert_cover_2 2 1 0 6 8 134 646 3
cert_coverFacet 3 684
cert_cover_5 3 2 1 2 4 6 164 684 1
cert_coverFacet 4 180
cert_cover_2 4 3 1 4 6 52 180 3
cert_coverFacet 5 868
cert_cover_5 5 3 1 4 5 7 292 868 2
cert_coverFacet 6 440
cert_cover_5 6 1 2 3 4 6 408 440 2
cert_coverFacet 7 472
cert_cover_5 7 1 2 3 5 6 408 472 2
cert_coverFacet 8 360
cert_cover_2 8 4 2 5 7 104 360 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0770

end
end BundlePart29

-- Public target certificates; internal witness data stays private.
namespace Nonrational.TerminalVerification
open Papers.RationalityTen.ChirotopeDensity.FiniteProjection
open Nonrational.TerminalData
set_option maxRecDepth 100000
set_option maxHeartbeats 0

public theorem projection_4623 : Certifies 4623 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0741.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_4624 : Certifies 4624 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0742.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_4625 : Certifies 4625 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0743.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_4626 : Certifies 4626 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0744.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_4627 : Certifies 4627 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0745.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_4628 : Certifies 4628 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0746.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_4629 : Certifies 4629 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0747.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_4630 : Certifies 4630 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0748.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_4631 : Certifies 4631 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0749.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_4632 : Certifies 4632 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0750.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_4633 : Certifies 4633 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0751.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_4634 : Certifies 4634 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0752.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_4635 : Certifies 4635 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0753.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_4636 : Certifies 4636 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0754.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_4637 : Certifies 4637 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0755.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_4638 : Certifies 4638 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0756.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_4639 : Certifies 4639 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0757.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_4640 : Certifies 4640 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0758.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_4641 : Certifies 4641 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0759.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_4642 : Certifies 4642 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0760.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_4643 : Certifies 4643 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0761.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_4644 : Certifies 4644 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0762.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_4645 : Certifies 4645 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0763.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_4646 : Certifies 4646 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0764.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_4647 : Certifies 4647 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0765.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_4648 : Certifies 4648 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0766.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_4649 : Certifies 4649 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0767.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_4650 : Certifies 4650 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0768.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_4651 : Certifies 4651 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0769.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_4652 : Certifies 4652 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0770.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem certified_B153 (j : Fin 30) :
    Certifies (4623 + j.val) := by
  fin_cases j
  · exact projection_4623
  · exact projection_4624
  · exact projection_4625
  · exact projection_4626
  · exact projection_4627
  · exact projection_4628
  · exact projection_4629
  · exact projection_4630
  · exact projection_4631
  · exact projection_4632
  · exact projection_4633
  · exact projection_4634
  · exact projection_4635
  · exact projection_4636
  · exact projection_4637
  · exact projection_4638
  · exact projection_4639
  · exact projection_4640
  · exact projection_4641
  · exact projection_4642
  · exact projection_4643
  · exact projection_4644
  · exact projection_4645
  · exact projection_4646
  · exact projection_4647
  · exact projection_4648
  · exact projection_4649
  · exact projection_4650
  · exact projection_4651
  · exact projection_4652

end Nonrational.TerminalVerification
-- Explicit facial frame witnesses, with lexical vector tracking.
