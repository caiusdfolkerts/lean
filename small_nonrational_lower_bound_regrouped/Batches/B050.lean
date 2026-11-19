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
/- Source: ProjectionCertificates/R_one_six_1305.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1305

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 647, 91, 835, 805, 369, 206, 706, 188, 676, 472, 944, 960, 7, 27, 67, 515, 37, 517, 49, 81, 289, 321, 769, 14, 134, 74, 194, 578, 642, 60, 140, 164, 548, 644, 88, 152, 200, 176, 304, 336, 400, 672, 800, 448, 704, 832, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_647, vertices_91, vertices_835, vertices_805, vertices_369, vertices_206, vertices_706, vertices_188, vertices_676, vertices_472, vertices_944, vertices_960] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_27, vertices_67, vertices_515, vertices_37, vertices_517, vertices_49, vertices_81, vertices_289, vertices_321, vertices_769, vertices_14, vertices_134, vertices_74, vertices_194, vertices_578, vertices_642, vertices_60, vertices_140, vertices_164, vertices_548, vertices_644, vertices_88, vertices_152, vertices_200, vertices_176, vertices_304, vertices_336, vertices_400, vertices_672, vertices_800, vertices_448, vertices_704, vertices_832, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_647), (false, vertices_91), (false, vertices_835), (false, vertices_805), (false, vertices_369), (true, vertices_194), (true, vertices_140), (true, vertices_164), (true, vertices_152), (true, vertices_200), (true, vertices_176), (true, vertices_400), (true, vertices_672), (true, vertices_448), (true, vertices_704), (true, vertices_896)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 14 11 18 19 21 22 23 24 25
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 15 else
  if p.val = (false, vertices_647) then 12 else
  if p.val = (false, vertices_91) then 16 else
  if p.val = (false, vertices_835) then 17 else
  if p.val = (false, vertices_805) then 13 else
  if p.val = (false, vertices_369) then 20 else
  if p.val = (true, vertices_194) then 0 else
  if p.val = (true, vertices_140) then 1 else
  if p.val = (true, vertices_164) then 2 else
  if p.val = (true, vertices_152) then 3 else
  if p.val = (true, vertices_200) then 4 else
  if p.val = (true, vertices_176) then 5 else
  if p.val = (true, vertices_400) then 6 else
  if p.val = (true, vertices_672) then 7 else
  if p.val = (true, vertices_448) then 8 else
  if p.val = (true, vertices_704) then 9 else
  if p.val = (true, vertices_896) then 10 else
  0
cert_priority
cert_nodeAtPriority_58 0 194 1 140 164 152 200 176 400 672 448 704 896 647 805 91 835 369
cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 2 5 6 206 14 3
cert_row_2 1 1 2 3 4 60
cert_row_4 2 2 3 5 6 7 472 88 3
cert_row_4 3 3 4 6 7 8 944 176 3
cert_rows
cert_pivot_2 0 1 2 3
cert_heightProof 4
cert_coverFacet 0 206
cert_cover_5 0 0 0 1 2 5 14 206 3
cert_coverFacet 1 706
cert_cover_2 1 5 0 6 8 194 706 3
cert_coverFacet 2 188
cert_cover_5 2 1 1 2 3 6 60 188 3
cert_coverFacet 3 676
cert_cover_2 3 4 1 6 8 164 676 3
cert_coverFacet 4 472
cert_cover_5 4 2 2 3 5 6 88 472 3
cert_coverFacet 5 944
cert_cover_5 5 3 3 4 6 7 176 944 3
cert_coverFacet 6 960
cert_cover_2 6 6 5 7 8 448 960 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1305

end
end BundlePart0

section BundlePart1
/- Source: ProjectionCertificates/R_one_six_1306.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1306

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 91, 173, 457, 369, 929, 206, 662, 594, 962, 820, 676, 848, 27, 45, 73, 137, 49, 81, 161, 289, 321, 385, 14, 22, 134, 74, 82, 530, 194, 578, 642, 140, 52, 532, 164, 548, 644, 200, 304, 336, 592, 784, 672, 800, 448, 832, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_91, vertices_173, vertices_457, vertices_369, vertices_929, vertices_206, vertices_662, vertices_594, vertices_962, vertices_820, vertices_676, vertices_848] (by decide +kernel)
  polygons := literalFinset [vertices_27, vertices_45, vertices_73, vertices_137, vertices_49, vertices_81, vertices_161, vertices_289, vertices_321, vertices_385, vertices_14, vertices_22, vertices_134, vertices_74, vertices_82, vertices_530, vertices_194, vertices_578, vertices_642, vertices_140, vertices_52, vertices_532, vertices_164, vertices_548, vertices_644, vertices_200, vertices_304, vertices_336, vertices_592, vertices_784, vertices_672, vertices_800, vertices_448, vertices_832, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_91), (false, vertices_173), (false, vertices_457), (false, vertices_369), (false, vertices_929), (true, vertices_134), (true, vertices_530), (true, vertices_194), (true, vertices_578), (true, vertices_642), (true, vertices_532), (true, vertices_548), (true, vertices_644), (true, vertices_592), (true, vertices_784), (true, vertices_832)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 11 13 16 18 20 22 23 24 25
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 14 else
  if p.val = (false, vertices_91) then 12 else
  if p.val = (false, vertices_173) then 15 else
  if p.val = (false, vertices_457) then 17 else
  if p.val = (false, vertices_369) then 19 else
  if p.val = (false, vertices_929) then 21 else
  if p.val = (true, vertices_134) then 0 else
  if p.val = (true, vertices_530) then 1 else
  if p.val = (true, vertices_194) then 2 else
  if p.val = (true, vertices_578) then 3 else
  if p.val = (true, vertices_642) then 4 else
  if p.val = (true, vertices_532) then 5 else
  if p.val = (true, vertices_548) then 6 else
  if p.val = (true, vertices_644) then 7 else
  if p.val = (true, vertices_592) then 8 else
  if p.val = (true, vertices_784) then 9 else
  if p.val = (true, vertices_832) then 10 else
  0
cert_priority
cert_nodeAtPriority_16 134 530 194 578 642 532 548 644 592 784 832
cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 2 5 6 206 14 3
cert_row_4 1 0 5 6 7 8 962 194 3
cert_row_4 2 0 1 3 6 8 662 22 3
cert_row_4 3 1 3 4 7 8 820 52 3
cert_rows
cert_pivot_2 2 5 0 1
cert_heightProof 4
cert_coverFacet 0 206
cert_cover_5 0 0 0 1 2 5 14 206 3
cert_coverFacet 1 662
cert_cover_5 1 2 0 1 3 6 22 662 3
cert_coverFacet 2 594
cert_cover_2 2 3 0 5 8 82 594 3
cert_coverFacet 3 962
cert_cover_5 3 1 0 5 6 7 194 962 3
cert_coverFacet 4 820
cert_cover_5 4 3 1 3 4 7 52 820 3
cert_coverFacet 5 676
cert_cover_2 5 4 1 6 8 164 676 3
cert_coverFacet 6 848
cert_cover_2 6 5 3 7 8 336 848 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1306

end
end BundlePart1

section BundlePart2
/- Source: ProjectionCertificates/R_one_six_1307.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1307

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 91, 173, 457, 369, 929, 206, 662, 338, 786, 962, 820, 676, 27, 45, 73, 137, 49, 81, 161, 289, 321, 385, 14, 22, 134, 74, 82, 274, 530, 194, 322, 642, 770, 140, 52, 532, 164, 548, 644, 200, 304, 336, 784, 672, 800, 448, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_91, vertices_173, vertices_457, vertices_369, vertices_929, vertices_206, vertices_662, vertices_338, vertices_786, vertices_962, vertices_820, vertices_676] (by decide +kernel)
  polygons := literalFinset [vertices_27, vertices_45, vertices_73, vertices_137, vertices_49, vertices_81, vertices_161, vertices_289, vertices_321, vertices_385, vertices_14, vertices_22, vertices_134, vertices_74, vertices_82, vertices_274, vertices_530, vertices_194, vertices_322, vertices_642, vertices_770, vertices_140, vertices_52, vertices_532, vertices_164, vertices_548, vertices_644, vertices_200, vertices_304, vertices_336, vertices_784, vertices_672, vertices_800, vertices_448, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_91), (false, vertices_173), (false, vertices_457), (false, vertices_369), (false, vertices_929), (true, vertices_134), (true, vertices_274), (true, vertices_530), (true, vertices_194), (true, vertices_322), (true, vertices_642), (true, vertices_770), (true, vertices_532), (true, vertices_548), (true, vertices_644), (true, vertices_784)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 11 13 16 18 20 22 23 24 25
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 14 else
  if p.val = (false, vertices_91) then 12 else
  if p.val = (false, vertices_173) then 15 else
  if p.val = (false, vertices_457) then 17 else
  if p.val = (false, vertices_369) then 19 else
  if p.val = (false, vertices_929) then 21 else
  if p.val = (true, vertices_134) then 0 else
  if p.val = (true, vertices_274) then 1 else
  if p.val = (true, vertices_530) then 2 else
  if p.val = (true, vertices_194) then 3 else
  if p.val = (true, vertices_322) then 4 else
  if p.val = (true, vertices_642) then 5 else
  if p.val = (true, vertices_770) then 6 else
  if p.val = (true, vertices_532) then 7 else
  if p.val = (true, vertices_548) then 8 else
  if p.val = (true, vertices_644) then 9 else
  if p.val = (true, vertices_784) then 10 else
  0
cert_priority
cert_nodeAtPriority_16 134 274 530 194 322 642 770 532 548 644 784
cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 2 5 6 206 14 3
cert_row_4 1 0 5 6 7 8 962 194 3
cert_row_4 2 0 1 3 6 8 662 22 3
cert_row_4 3 1 3 4 7 8 820 52 3
cert_rows
cert_pivot_2 2 5 0 1
cert_heightProof 4
cert_coverFacet 0 206
cert_cover_5 0 0 0 1 2 5 14 206 3
cert_coverFacet 1 662
cert_cover_5 1 2 0 1 3 6 22 662 3
cert_coverFacet 2 338
cert_cover_2 2 3 0 5 7 82 338 3
cert_coverFacet 3 786
cert_cover_2 3 3 0 7 8 274 786 3
cert_coverFacet 4 962
cert_cover_5 4 1 0 5 6 7 194 962 3
cert_coverFacet 5 820
cert_cover_5 5 3 1 3 4 7 52 820 3
cert_coverFacet 6 676
cert_cover_2 6 4 1 6 8 164 676 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1307

end
end BundlePart2

section BundlePart3
/- Source: ProjectionCertificates/R_one_six_1308.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1308

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 91, 173, 457, 369, 929, 206, 790, 646, 338, 962, 692, 816, 27, 45, 73, 137, 49, 81, 161, 289, 321, 385, 14, 22, 134, 518, 74, 82, 274, 194, 322, 642, 770, 140, 52, 532, 164, 644, 200, 304, 560, 336, 784, 672, 800, 448, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_91, vertices_173, vertices_457, vertices_369, vertices_929, vertices_206, vertices_790, vertices_646, vertices_338, vertices_962, vertices_692, vertices_816] (by decide +kernel)
  polygons := literalFinset [vertices_27, vertices_45, vertices_73, vertices_137, vertices_49, vertices_81, vertices_161, vertices_289, vertices_321, vertices_385, vertices_14, vertices_22, vertices_134, vertices_518, vertices_74, vertices_82, vertices_274, vertices_194, vertices_322, vertices_642, vertices_770, vertices_140, vertices_52, vertices_532, vertices_164, vertices_644, vertices_200, vertices_304, vertices_560, vertices_336, vertices_784, vertices_672, vertices_800, vertices_448, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_91), (false, vertices_173), (false, vertices_457), (false, vertices_369), (false, vertices_929), (true, vertices_134), (true, vertices_518), (true, vertices_274), (true, vertices_194), (true, vertices_322), (true, vertices_642), (true, vertices_770), (true, vertices_532), (true, vertices_644), (true, vertices_560), (true, vertices_784)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 11 13 16 18 20 22 23 24 25
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 14 else
  if p.val = (false, vertices_91) then 12 else
  if p.val = (false, vertices_173) then 15 else
  if p.val = (false, vertices_457) then 17 else
  if p.val = (false, vertices_369) then 19 else
  if p.val = (false, vertices_929) then 21 else
  if p.val = (true, vertices_134) then 0 else
  if p.val = (true, vertices_518) then 1 else
  if p.val = (true, vertices_274) then 2 else
  if p.val = (true, vertices_194) then 3 else
  if p.val = (true, vertices_322) then 4 else
  if p.val = (true, vertices_642) then 5 else
  if p.val = (true, vertices_770) then 6 else
  if p.val = (true, vertices_532) then 7 else
  if p.val = (true, vertices_644) then 8 else
  if p.val = (true, vertices_560) then 9 else
  if p.val = (true, vertices_784) then 10 else
  0
cert_priority
cert_nodeAtPriority_16 134 518 274 194 322 642 770 532 644 560 784
cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 2 5 6 206 14 3
cert_row_4 1 0 5 6 7 8 962 194 3
cert_row_4 2 0 1 3 7 8 790 22 3
cert_row_4 3 1 3 4 6 8 692 52 3
cert_rows
cert_pivot_2 2 5 0 1
cert_heightProof 4
cert_coverFacet 0 206
cert_cover_5 0 0 0 1 2 5 14 206 3
cert_coverFacet 1 790
cert_cover_5 1 2 0 1 3 7 22 790 3
cert_coverFacet 2 646
cert_cover_2 2 1 0 6 8 134 646 3
cert_coverFacet 3 338
cert_cover_2 3 3 0 5 7 82 338 3
cert_coverFacet 4 962
cert_cover_5 4 1 0 5 6 7 194 962 3
cert_coverFacet 5 692
cert_cover_5 5 3 1 3 4 6 52 692 3
cert_coverFacet 6 816
cert_cover_2 6 4 3 7 8 304 816 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1308

end
end BundlePart3

section BundlePart4
/- Source: ProjectionCertificates/R_one_six_1309.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1309

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 583, 91, 805, 369, 961, 526, 714, 188, 652, 676, 472, 944, 7, 27, 67, 37, 517, 49, 81, 289, 321, 577, 769, 14, 518, 74, 522, 578, 60, 140, 524, 164, 548, 644, 88, 152, 200, 648, 176, 304, 336, 400, 672, 800, 448, 704, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_583, vertices_91, vertices_805, vertices_369, vertices_961, vertices_526, vertices_714, vertices_188, vertices_652, vertices_676, vertices_472, vertices_944] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_27, vertices_67, vertices_37, vertices_517, vertices_49, vertices_81, vertices_289, vertices_321, vertices_577, vertices_769, vertices_14, vertices_518, vertices_74, vertices_522, vertices_578, vertices_60, vertices_140, vertices_524, vertices_164, vertices_548, vertices_644, vertices_88, vertices_152, vertices_200, vertices_648, vertices_176, vertices_304, vertices_336, vertices_400, vertices_672, vertices_800, vertices_448, vertices_704, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_583), (false, vertices_91), (false, vertices_805), (false, vertices_369), (false, vertices_961), (true, vertices_522), (true, vertices_140), (true, vertices_524), (true, vertices_164), (true, vertices_644), (true, vertices_152), (true, vertices_200), (true, vertices_648), (true, vertices_176), (true, vertices_400), (true, vertices_672)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 11 14 17 18 20 21 23 24 25
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 15 else
  if p.val = (false, vertices_583) then 12 else
  if p.val = (false, vertices_91) then 13 else
  if p.val = (false, vertices_805) then 16 else
  if p.val = (false, vertices_369) then 19 else
  if p.val = (false, vertices_961) then 22 else
  if p.val = (true, vertices_522) then 0 else
  if p.val = (true, vertices_140) then 1 else
  if p.val = (true, vertices_524) then 2 else
  if p.val = (true, vertices_164) then 3 else
  if p.val = (true, vertices_644) then 4 else
  if p.val = (true, vertices_152) then 5 else
  if p.val = (true, vertices_200) then 6 else
  if p.val = (true, vertices_648) then 7 else
  if p.val = (true, vertices_176) then 8 else
  if p.val = (true, vertices_400) then 9 else
  if p.val = (true, vertices_672) then 10 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_522), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_140), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_524), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_164), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_644), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_152), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_200), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_648), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_176), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_400), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_672), by decide +kernel⟩
  | 11 => Sum.inl 0
  | 12 => Sum.inr ⟨(false, vertices_583), by decide +kernel⟩
  | 13 => Sum.inr ⟨(false, vertices_91), by decide +kernel⟩
  | 14 => Sum.inl 1
  | 15 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 16 => Sum.inr ⟨(false, vertices_805), by decide +kernel⟩
  | 17 => Sum.inl 2
  | 18 => Sum.inl 3
  | 19 => Sum.inr ⟨(false, vertices_369), by decide +kernel⟩
  | 20 => Sum.inl 4
  | 21 => Sum.inl 5
  | 22 => Sum.inr ⟨(false, vertices_961), by decide +kernel⟩
  | 23 => Sum.inl 6
  | 24 => Sum.inl 7
  | 25 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 1 2 3 4 60
cert_row_4 1 0 2 5 6 8 714 74 3
cert_row_4 2 2 3 5 6 7 472 88 3
cert_row_4 3 3 4 6 7 8 944 176 3
cert_rows
cert_pivot_2 1 0 2 3
cert_heightProof 4
cert_coverFacet 0 526
cert_cover_2 0 1 0 2 8 14 526 3
cert_coverFacet 1 714
cert_cover_5 1 1 0 2 5 6 74 714 3
cert_coverFacet 2 188
cert_cover_5 2 0 1 2 3 6 60 188 3
cert_coverFacet 3 652
cert_cover_2 3 2 1 6 8 140 652 3
cert_coverFacet 4 676
cert_cover_2 4 4 1 6 8 164 676 3
cert_coverFacet 5 472
cert_cover_5 5 2 2 3 5 6 88 472 3
cert_coverFacet 6 944
cert_cover_5 6 3 3 4 6 7 176 944 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1309

end
end BundlePart4

section BundlePart5
/- Source: ProjectionCertificates/R_one_six_1310.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1310

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 583, 91, 805, 433, 849, 526, 714, 188, 652, 676, 472, 992, 7, 27, 67, 37, 517, 49, 81, 273, 289, 577, 769, 14, 518, 74, 522, 578, 60, 140, 524, 164, 548, 644, 88, 152, 200, 648, 176, 336, 400, 416, 672, 800, 448, 704, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_583, vertices_91, vertices_805, vertices_433, vertices_849, vertices_526, vertices_714, vertices_188, vertices_652, vertices_676, vertices_472, vertices_992] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_27, vertices_67, vertices_37, vertices_517, vertices_49, vertices_81, vertices_273, vertices_289, vertices_577, vertices_769, vertices_14, vertices_518, vertices_74, vertices_522, vertices_578, vertices_60, vertices_140, vertices_524, vertices_164, vertices_548, vertices_644, vertices_88, vertices_152, vertices_200, vertices_648, vertices_176, vertices_336, vertices_400, vertices_416, vertices_672, vertices_800, vertices_448, vertices_704, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_583), (false, vertices_91), (false, vertices_805), (false, vertices_433), (false, vertices_849), (true, vertices_522), (true, vertices_140), (true, vertices_524), (true, vertices_164), (true, vertices_644), (true, vertices_152), (true, vertices_200), (true, vertices_648), (true, vertices_672), (true, vertices_448), (true, vertices_704)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 11 14 17 18 21 22 23 24 25
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 15 else
  if p.val = (false, vertices_583) then 12 else
  if p.val = (false, vertices_91) then 13 else
  if p.val = (false, vertices_805) then 16 else
  if p.val = (false, vertices_433) then 19 else
  if p.val = (false, vertices_849) then 20 else
  if p.val = (true, vertices_522) then 0 else
  if p.val = (true, vertices_140) then 1 else
  if p.val = (true, vertices_524) then 2 else
  if p.val = (true, vertices_164) then 3 else
  if p.val = (true, vertices_644) then 4 else
  if p.val = (true, vertices_152) then 5 else
  if p.val = (true, vertices_200) then 6 else
  if p.val = (true, vertices_648) then 7 else
  if p.val = (true, vertices_672) then 8 else
  if p.val = (true, vertices_448) then 9 else
  if p.val = (true, vertices_704) then 10 else
  0
cert_priority
cert_nodeAtPriority_35 522 140 524 164 644 152 200 648 672 448 704 583 91 63 805 433 849
cert_priority_injective
cert_incidenceProof
cert_row_2 0 1 2 3 4 60
cert_row_4 1 0 2 5 6 8 714 74 3
cert_row_4 2 2 3 5 6 7 472 88 3
cert_row_4 3 4 5 6 7 8 992 416 1
cert_rows
cert_pivot_2 1 0 2 4
cert_heightProof 4
cert_coverFacet 0 526
cert_cover_2 0 1 0 2 8 14 526 3
cert_coverFacet 1 714
cert_cover_5 1 1 0 2 5 6 74 714 3
cert_coverFacet 2 188
cert_cover_5 2 0 1 2 3 6 60 188 3
cert_coverFacet 3 652
cert_cover_2 3 2 1 6 8 140 652 3
cert_coverFacet 4 676
cert_cover_2 4 4 1 6 8 164 676 3
cert_coverFacet 5 472
cert_cover_5 5 2 2 3 5 6 88 472 3
cert_coverFacet 6 992
cert_cover_5 6 3 4 5 6 7 416 992 1
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1310

end
end BundlePart5

section BundlePart6
/- Source: ProjectionCertificates/R_one_six_1311.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1311

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 583, 91, 805, 369, 961, 142, 646, 714, 188, 676, 472, 944, 7, 27, 67, 37, 517, 49, 81, 289, 321, 577, 769, 14, 134, 518, 74, 138, 578, 642, 60, 140, 164, 548, 644, 88, 152, 200, 176, 304, 336, 400, 672, 800, 448, 704, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_583, vertices_91, vertices_805, vertices_369, vertices_961, vertices_142, vertices_646, vertices_714, vertices_188, vertices_676, vertices_472, vertices_944] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_27, vertices_67, vertices_37, vertices_517, vertices_49, vertices_81, vertices_289, vertices_321, vertices_577, vertices_769, vertices_14, vertices_134, vertices_518, vertices_74, vertices_138, vertices_578, vertices_642, vertices_60, vertices_140, vertices_164, vertices_548, vertices_644, vertices_88, vertices_152, vertices_200, vertices_176, vertices_304, vertices_336, vertices_400, vertices_672, vertices_800, vertices_448, vertices_704, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_583), (false, vertices_91), (false, vertices_805), (false, vertices_369), (false, vertices_961), (true, vertices_134), (true, vertices_138), (true, vertices_642), (true, vertices_140), (true, vertices_164), (true, vertices_644), (true, vertices_152), (true, vertices_200), (true, vertices_176), (true, vertices_400), (true, vertices_672)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 11 14 17 18 20 21 23 24 25
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 15 else
  if p.val = (false, vertices_583) then 12 else
  if p.val = (false, vertices_91) then 13 else
  if p.val = (false, vertices_805) then 16 else
  if p.val = (false, vertices_369) then 19 else
  if p.val = (false, vertices_961) then 22 else
  if p.val = (true, vertices_134) then 0 else
  if p.val = (true, vertices_138) then 1 else
  if p.val = (true, vertices_642) then 2 else
  if p.val = (true, vertices_140) then 3 else
  if p.val = (true, vertices_164) then 4 else
  if p.val = (true, vertices_644) then 5 else
  if p.val = (true, vertices_152) then 6 else
  if p.val = (true, vertices_200) then 7 else
  if p.val = (true, vertices_176) then 8 else
  if p.val = (true, vertices_400) then 9 else
  if p.val = (true, vertices_672) then 10 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_134), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_138), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_642), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_140), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_164), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_644), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_152), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_200), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_176), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_400), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_672), by decide +kernel⟩
  | 11 => Sum.inl 0
  | 12 => Sum.inr ⟨(false, vertices_583), by decide +kernel⟩
  | 13 => Sum.inr ⟨(false, vertices_91), by decide +kernel⟩
  | 14 => Sum.inl 1
  | 15 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 16 => Sum.inr ⟨(false, vertices_805), by decide +kernel⟩
  | 17 => Sum.inl 2
  | 18 => Sum.inl 3
  | 19 => Sum.inr ⟨(false, vertices_369), by decide +kernel⟩
  | 20 => Sum.inl 4
  | 21 => Sum.inl 5
  | 22 => Sum.inr ⟨(false, vertices_961), by decide +kernel⟩
  | 23 => Sum.inl 6
  | 24 => Sum.inl 7
  | 25 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 1 2 3 4 60
cert_row_4 1 0 2 5 6 8 714 74 3
cert_row_4 2 2 3 5 6 7 472 88 3
cert_row_4 3 3 4 6 7 8 944 176 3
cert_rows
cert_pivot_2 1 0 2 3
cert_heightProof 4
cert_coverFacet 0 142
cert_cover_2 0 1 0 2 6 14 142 3
cert_coverFacet 1 646
cert_cover_2 1 1 0 6 8 134 646 3
cert_coverFacet 2 714
cert_cover_5 2 1 0 2 5 6 74 714 3
cert_coverFacet 3 188
cert_cover_5 3 0 1 2 3 6 60 188 3
cert_coverFacet 4 676
cert_cover_2 4 4 1 6 8 164 676 3
cert_coverFacet 5 472
cert_cover_5 5 2 2 3 5 6 88 472 3
cert_coverFacet 6 944
cert_cover_5 6 3 3 4 6 7 176 944 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1311

end
end BundlePart6

section BundlePart7
/- Source: ProjectionCertificates/R_one_six_1312.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1312

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 583, 91, 805, 433, 849, 142, 646, 714, 188, 676, 472, 992, 7, 27, 67, 37, 517, 49, 81, 273, 289, 577, 769, 14, 134, 518, 74, 138, 578, 642, 60, 140, 164, 548, 644, 88, 152, 200, 176, 336, 400, 416, 672, 800, 448, 704, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_583, vertices_91, vertices_805, vertices_433, vertices_849, vertices_142, vertices_646, vertices_714, vertices_188, vertices_676, vertices_472, vertices_992] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_27, vertices_67, vertices_37, vertices_517, vertices_49, vertices_81, vertices_273, vertices_289, vertices_577, vertices_769, vertices_14, vertices_134, vertices_518, vertices_74, vertices_138, vertices_578, vertices_642, vertices_60, vertices_140, vertices_164, vertices_548, vertices_644, vertices_88, vertices_152, vertices_200, vertices_176, vertices_336, vertices_400, vertices_416, vertices_672, vertices_800, vertices_448, vertices_704, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_583), (false, vertices_91), (false, vertices_805), (false, vertices_433), (false, vertices_849), (true, vertices_134), (true, vertices_138), (true, vertices_642), (true, vertices_140), (true, vertices_164), (true, vertices_644), (true, vertices_152), (true, vertices_200), (true, vertices_672), (true, vertices_448), (true, vertices_704)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 11 14 17 18 21 22 23 24 25
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 15 else
  if p.val = (false, vertices_583) then 12 else
  if p.val = (false, vertices_91) then 13 else
  if p.val = (false, vertices_805) then 16 else
  if p.val = (false, vertices_433) then 19 else
  if p.val = (false, vertices_849) then 20 else
  if p.val = (true, vertices_134) then 0 else
  if p.val = (true, vertices_138) then 1 else
  if p.val = (true, vertices_642) then 2 else
  if p.val = (true, vertices_140) then 3 else
  if p.val = (true, vertices_164) then 4 else
  if p.val = (true, vertices_644) then 5 else
  if p.val = (true, vertices_152) then 6 else
  if p.val = (true, vertices_200) then 7 else
  if p.val = (true, vertices_672) then 8 else
  if p.val = (true, vertices_448) then 9 else
  if p.val = (true, vertices_704) then 10 else
  0
cert_priority
cert_nodeAtPriority_35 134 138 642 140 164 644 152 200 672 448 704 583 91 63 805 433 849
cert_priority_injective
cert_incidenceProof
cert_row_2 0 1 2 3 4 60
cert_row_4 1 0 2 5 6 8 714 74 3
cert_row_4 2 2 3 5 6 7 472 88 3
cert_row_4 3 4 5 6 7 8 992 416 1
cert_rows
cert_pivot_2 1 0 2 4
cert_heightProof 4
cert_coverFacet 0 142
cert_cover_2 0 1 0 2 6 14 142 3
cert_coverFacet 1 646
cert_cover_2 1 1 0 6 8 134 646 3
cert_coverFacet 2 714
cert_cover_5 2 1 0 2 5 6 74 714 3
cert_coverFacet 3 188
cert_cover_5 3 0 1 2 3 6 60 188 3
cert_coverFacet 4 676
cert_cover_2 4 4 1 6 8 164 676 3
cert_coverFacet 5 472
cert_cover_5 5 2 2 3 5 6 88 472 3
cert_coverFacet 6 992
cert_cover_5 6 3 4 5 6 7 416 992 1
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1312

end
end BundlePart7

section BundlePart8
/- Source: ProjectionCertificates/R_one_six_1313.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1313

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 647, 91, 835, 805, 369, 142, 714, 188, 676, 472, 944, 960, 7, 27, 67, 515, 37, 517, 49, 81, 289, 321, 769, 14, 134, 74, 138, 578, 642, 60, 140, 164, 548, 644, 88, 152, 200, 176, 304, 336, 400, 672, 800, 448, 704, 832, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_647, vertices_91, vertices_835, vertices_805, vertices_369, vertices_142, vertices_714, vertices_188, vertices_676, vertices_472, vertices_944, vertices_960] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_27, vertices_67, vertices_515, vertices_37, vertices_517, vertices_49, vertices_81, vertices_289, vertices_321, vertices_769, vertices_14, vertices_134, vertices_74, vertices_138, vertices_578, vertices_642, vertices_60, vertices_140, vertices_164, vertices_548, vertices_644, vertices_88, vertices_152, vertices_200, vertices_176, vertices_304, vertices_336, vertices_400, vertices_672, vertices_800, vertices_448, vertices_704, vertices_832, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_647), (false, vertices_91), (false, vertices_835), (false, vertices_805), (false, vertices_369), (true, vertices_138), (true, vertices_140), (true, vertices_164), (true, vertices_152), (true, vertices_200), (true, vertices_176), (true, vertices_400), (true, vertices_672), (true, vertices_448), (true, vertices_704), (true, vertices_896)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 14 11 18 19 21 22 23 24 25
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 15 else
  if p.val = (false, vertices_647) then 12 else
  if p.val = (false, vertices_91) then 16 else
  if p.val = (false, vertices_835) then 17 else
  if p.val = (false, vertices_805) then 13 else
  if p.val = (false, vertices_369) then 20 else
  if p.val = (true, vertices_138) then 0 else
  if p.val = (true, vertices_140) then 1 else
  if p.val = (true, vertices_164) then 2 else
  if p.val = (true, vertices_152) then 3 else
  if p.val = (true, vertices_200) then 4 else
  if p.val = (true, vertices_176) then 5 else
  if p.val = (true, vertices_400) then 6 else
  if p.val = (true, vertices_672) then 7 else
  if p.val = (true, vertices_448) then 8 else
  if p.val = (true, vertices_704) then 9 else
  if p.val = (true, vertices_896) then 10 else
  0
cert_priority
cert_nodeAtPriority_58 0 138 1 140 164 152 200 176 400 672 448 704 896 647 805 91 835 369
cert_priority_injective
cert_incidenceProof
cert_row_2 0 1 2 3 4 60
cert_row_4 1 0 2 5 6 8 714 74 3
cert_row_4 2 2 3 5 6 7 472 88 3
cert_row_4 3 3 4 6 7 8 944 176 3
cert_rows
cert_pivot_2 1 0 2 3
cert_heightProof 4
cert_coverFacet 0 142
cert_cover_2 0 1 0 2 6 14 142 3
cert_coverFacet 1 714
cert_cover_5 1 1 0 2 5 6 74 714 3
cert_coverFacet 2 188
cert_cover_5 2 0 1 2 3 6 60 188 3
cert_coverFacet 3 676
cert_cover_2 3 4 1 6 8 164 676 3
cert_coverFacet 4 472
cert_cover_5 4 2 2 3 5 6 88 472 3
cert_coverFacet 5 944
cert_cover_5 5 3 3 4 6 7 176 944 3
cert_coverFacet 6 960
cert_cover_2 6 6 5 7 8 448 960 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1313

end
end BundlePart8

section BundlePart9
/- Source: ProjectionCertificates/R_one_six_1314.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1314

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 647, 91, 835, 805, 369, 142, 714, 188, 420, 964, 472, 432, 7, 27, 67, 515, 37, 517, 49, 81, 289, 321, 769, 14, 134, 74, 138, 578, 642, 60, 140, 164, 292, 388, 644, 772, 88, 152, 200, 176, 304, 336, 400, 416, 448, 704, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_647, vertices_91, vertices_835, vertices_805, vertices_369, vertices_142, vertices_714, vertices_188, vertices_420, vertices_964, vertices_472, vertices_432] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_27, vertices_67, vertices_515, vertices_37, vertices_517, vertices_49, vertices_81, vertices_289, vertices_321, vertices_769, vertices_14, vertices_134, vertices_74, vertices_138, vertices_578, vertices_642, vertices_60, vertices_140, vertices_164, vertices_292, vertices_388, vertices_644, vertices_772, vertices_88, vertices_152, vertices_200, vertices_176, vertices_304, vertices_336, vertices_400, vertices_416, vertices_448, vertices_704, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_647), (false, vertices_91), (false, vertices_835), (false, vertices_805), (false, vertices_369), (true, vertices_138), (true, vertices_140), (true, vertices_164), (true, vertices_388), (true, vertices_152), (true, vertices_200), (true, vertices_176), (true, vertices_400), (true, vertices_416), (true, vertices_448), (true, vertices_704)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 14 11 18 19 21 22 23 24 25
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 15 else
  if p.val = (false, vertices_647) then 12 else
  if p.val = (false, vertices_91) then 16 else
  if p.val = (false, vertices_835) then 17 else
  if p.val = (false, vertices_805) then 13 else
  if p.val = (false, vertices_369) then 20 else
  if p.val = (true, vertices_138) then 0 else
  if p.val = (true, vertices_140) then 1 else
  if p.val = (true, vertices_164) then 2 else
  if p.val = (true, vertices_388) then 3 else
  if p.val = (true, vertices_152) then 4 else
  if p.val = (true, vertices_200) then 5 else
  if p.val = (true, vertices_176) then 6 else
  if p.val = (true, vertices_400) then 7 else
  if p.val = (true, vertices_416) then 8 else
  if p.val = (true, vertices_448) then 9 else
  if p.val = (true, vertices_704) then 10 else
  0
cert_priority
cert_nodeAtPriority_58 0 138 1 140 164 388 152 200 176 400 416 448 704 647 805 91 835 369
cert_priority_injective
cert_incidenceProof
cert_row_2 0 1 2 3 4 60
cert_row_4 1 0 2 5 6 8 714 74 3
cert_row_4 2 1 5 6 7 8 964 388 1
cert_row_4 3 2 3 5 6 7 472 88 3
cert_rows
cert_pivot_2 4 0 1 2
cert_heightProof 4
cert_coverFacet 0 142
cert_cover_2 0 1 0 2 6 14 142 3
cert_coverFacet 1 714
cert_cover_5 1 1 0 2 5 6 74 714 3
cert_coverFacet 2 188
cert_cover_5 2 0 1 2 3 6 60 188 3
cert_coverFacet 3 420
cert_cover_2 3 4 1 6 7 164 420 3
cert_coverFacet 4 964
cert_cover_5 4 2 1 5 6 7 388 964 1
cert_coverFacet 5 472
cert_cover_5 5 3 2 3 5 6 88 472 3
cert_coverFacet 6 432
cert_cover_2 6 4 3 6 7 176 432 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1314

end
end BundlePart9

section BundlePart10
/- Source: ProjectionCertificates/R_one_six_1315.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1315

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 583, 91, 805, 433, 849, 142, 902, 714, 188, 420, 472, 960, 7, 27, 67, 37, 517, 49, 81, 273, 289, 577, 769, 14, 134, 518, 74, 138, 578, 642, 60, 140, 164, 292, 388, 772, 88, 152, 200, 176, 336, 400, 416, 448, 704, 832, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_583, vertices_91, vertices_805, vertices_433, vertices_849, vertices_142, vertices_902, vertices_714, vertices_188, vertices_420, vertices_472, vertices_960] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_27, vertices_67, vertices_37, vertices_517, vertices_49, vertices_81, vertices_273, vertices_289, vertices_577, vertices_769, vertices_14, vertices_134, vertices_518, vertices_74, vertices_138, vertices_578, vertices_642, vertices_60, vertices_140, vertices_164, vertices_292, vertices_388, vertices_772, vertices_88, vertices_152, vertices_200, vertices_176, vertices_336, vertices_400, vertices_416, vertices_448, vertices_704, vertices_832, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_583), (false, vertices_91), (false, vertices_805), (false, vertices_433), (false, vertices_849), (true, vertices_134), (true, vertices_138), (true, vertices_642), (true, vertices_140), (true, vertices_164), (true, vertices_388), (true, vertices_152), (true, vertices_200), (true, vertices_448), (true, vertices_704), (true, vertices_896)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 11 14 17 18 21 22 23 24 25
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 15 else
  if p.val = (false, vertices_583) then 12 else
  if p.val = (false, vertices_91) then 13 else
  if p.val = (false, vertices_805) then 16 else
  if p.val = (false, vertices_433) then 19 else
  if p.val = (false, vertices_849) then 20 else
  if p.val = (true, vertices_134) then 0 else
  if p.val = (true, vertices_138) then 1 else
  if p.val = (true, vertices_642) then 2 else
  if p.val = (true, vertices_140) then 3 else
  if p.val = (true, vertices_164) then 4 else
  if p.val = (true, vertices_388) then 5 else
  if p.val = (true, vertices_152) then 6 else
  if p.val = (true, vertices_200) then 7 else
  if p.val = (true, vertices_448) then 8 else
  if p.val = (true, vertices_704) then 9 else
  if p.val = (true, vertices_896) then 10 else
  0
cert_priority
cert_nodeAtPriority_35 134 138 642 140 164 388 152 200 448 704 896 583 91 63 805 433 849
cert_priority_injective
cert_incidenceProof
cert_row_2 0 1 2 3 4 60
cert_row_4 1 0 1 6 7 8 902 134 3
cert_row_4 2 0 2 5 6 8 714 74 3
cert_row_4 3 2 3 5 6 7 472 88 3
cert_rows
cert_pivot_2 4 1 0 2
cert_heightProof 4
cert_coverFacet 0 142
cert_cover_2 0 1 0 2 6 14 142 3
cert_coverFacet 1 902
cert_cover_5 1 1 0 1 6 7 134 902 3
cert_coverFacet 2 714
cert_cover_5 2 2 0 2 5 6 74 714 3
cert_coverFacet 3 188
cert_cover_5 3 0 1 2 3 6 60 188 3
cert_coverFacet 4 420
cert_cover_2 4 4 1 6 7 164 420 3
cert_coverFacet 5 472
cert_cover_5 5 3 2 3 5 6 88 472 3
cert_coverFacet 6 960
cert_cover_2 6 6 5 7 8 448 960 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1315

end
end BundlePart10

section BundlePart11
/- Source: ProjectionCertificates/R_one_six_1316.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1316

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 583, 91, 805, 369, 961, 142, 902, 714, 188, 420, 472, 432, 7, 27, 67, 37, 517, 49, 81, 289, 321, 577, 769, 14, 134, 518, 74, 138, 578, 642, 60, 140, 164, 292, 388, 772, 88, 152, 200, 176, 304, 336, 400, 416, 448, 704, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_583, vertices_91, vertices_805, vertices_369, vertices_961, vertices_142, vertices_902, vertices_714, vertices_188, vertices_420, vertices_472, vertices_432] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_27, vertices_67, vertices_37, vertices_517, vertices_49, vertices_81, vertices_289, vertices_321, vertices_577, vertices_769, vertices_14, vertices_134, vertices_518, vertices_74, vertices_138, vertices_578, vertices_642, vertices_60, vertices_140, vertices_164, vertices_292, vertices_388, vertices_772, vertices_88, vertices_152, vertices_200, vertices_176, vertices_304, vertices_336, vertices_400, vertices_416, vertices_448, vertices_704, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_583), (false, vertices_91), (false, vertices_805), (false, vertices_369), (false, vertices_961), (true, vertices_134), (true, vertices_138), (true, vertices_642), (true, vertices_140), (true, vertices_164), (true, vertices_388), (true, vertices_152), (true, vertices_200), (true, vertices_176), (true, vertices_400), (true, vertices_416)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 11 14 17 18 20 21 23 24 25
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 15 else
  if p.val = (false, vertices_583) then 12 else
  if p.val = (false, vertices_91) then 13 else
  if p.val = (false, vertices_805) then 16 else
  if p.val = (false, vertices_369) then 19 else
  if p.val = (false, vertices_961) then 22 else
  if p.val = (true, vertices_134) then 0 else
  if p.val = (true, vertices_138) then 1 else
  if p.val = (true, vertices_642) then 2 else
  if p.val = (true, vertices_140) then 3 else
  if p.val = (true, vertices_164) then 4 else
  if p.val = (true, vertices_388) then 5 else
  if p.val = (true, vertices_152) then 6 else
  if p.val = (true, vertices_200) then 7 else
  if p.val = (true, vertices_176) then 8 else
  if p.val = (true, vertices_400) then 9 else
  if p.val = (true, vertices_416) then 10 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_134), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_138), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_642), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_140), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_164), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_388), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_152), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_200), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_176), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_400), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_416), by decide +kernel⟩
  | 11 => Sum.inl 0
  | 12 => Sum.inr ⟨(false, vertices_583), by decide +kernel⟩
  | 13 => Sum.inr ⟨(false, vertices_91), by decide +kernel⟩
  | 14 => Sum.inl 1
  | 15 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 16 => Sum.inr ⟨(false, vertices_805), by decide +kernel⟩
  | 17 => Sum.inl 2
  | 18 => Sum.inl 3
  | 19 => Sum.inr ⟨(false, vertices_369), by decide +kernel⟩
  | 20 => Sum.inl 4
  | 21 => Sum.inl 5
  | 22 => Sum.inr ⟨(false, vertices_961), by decide +kernel⟩
  | 23 => Sum.inl 6
  | 24 => Sum.inl 7
  | 25 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 1 2 3 4 60
cert_row_4 1 0 1 6 7 8 902 134 3
cert_row_4 2 0 2 5 6 8 714 74 3
cert_row_4 3 2 3 5 6 7 472 88 3
cert_rows
cert_pivot_2 4 1 0 2
cert_heightProof 4
cert_coverFacet 0 142
cert_cover_2 0 1 0 2 6 14 142 3
cert_coverFacet 1 902
cert_cover_5 1 1 0 1 6 7 134 902 3
cert_coverFacet 2 714
cert_cover_5 2 2 0 2 5 6 74 714 3
cert_coverFacet 3 188
cert_cover_5 3 0 1 2 3 6 60 188 3
cert_coverFacet 4 420
cert_cover_2 4 4 1 6 7 164 420 3
cert_coverFacet 5 472
cert_cover_5 5 3 2 3 5 6 88 472 3
cert_coverFacet 6 432
cert_cover_2 6 4 3 6 7 176 432 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1316

end
end BundlePart11

section BundlePart12
/- Source: ProjectionCertificates/R_one_six_1317.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1317

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 391, 75, 835, 181, 617, 929, 94, 326, 468, 696, 856, 912, 7, 11, 67, 259, 53, 133, 41, 73, 161, 545, 577, 385, 769, 30, 70, 262, 74, 322, 84, 148, 324, 388, 56, 88, 536, 552, 584, 176, 336, 400, 656, 784, 672, 832, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_391, vertices_75, vertices_835, vertices_181, vertices_617, vertices_929, vertices_94, vertices_326, vertices_468, vertices_696, vertices_856, vertices_912] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_67, vertices_259, vertices_53, vertices_133, vertices_41, vertices_73, vertices_161, vertices_545, vertices_577, vertices_385, vertices_769, vertices_30, vertices_70, vertices_262, vertices_74, vertices_322, vertices_84, vertices_148, vertices_324, vertices_388, vertices_56, vertices_88, vertices_536, vertices_552, vertices_584, vertices_176, vertices_336, vertices_400, vertices_656, vertices_784, vertices_672, vertices_832, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_391), (false, vertices_75), (false, vertices_835), (false, vertices_181), (false, vertices_617), (false, vertices_929), (true, vertices_70), (true, vertices_84), (true, vertices_324), (true, vertices_88), (true, vertices_536), (true, vertices_336), (true, vertices_400), (true, vertices_656), (true, vertices_784)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 10 13 16 18 19 21 22 23 24
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 14 else
  if p.val = (false, vertices_391) then 11 else
  if p.val = (false, vertices_75) then 0 else
  if p.val = (false, vertices_835) then 12 else
  if p.val = (false, vertices_181) then 15 else
  if p.val = (false, vertices_617) then 17 else
  if p.val = (false, vertices_929) then 20 else
  if p.val = (true, vertices_70) then 1 else
  if p.val = (true, vertices_84) then 2 else
  if p.val = (true, vertices_324) then 3 else
  if p.val = (true, vertices_88) then 4 else
  if p.val = (true, vertices_536) then 5 else
  if p.val = (true, vertices_336) then 6 else
  if p.val = (true, vertices_400) then 7 else
  if p.val = (true, vertices_656) then 8 else
  if p.val = (true, vertices_784) then 9 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_75), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_70), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_84), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_324), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_88), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_536), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_336), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_400), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_656), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_784), by decide +kernel⟩
  | 10 => Sum.inl 0
  | 11 => Sum.inr ⟨(false, vertices_391), by decide +kernel⟩
  | 12 => Sum.inr ⟨(false, vertices_835), by decide +kernel⟩
  | 13 => Sum.inl 1
  | 14 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 15 => Sum.inr ⟨(false, vertices_181), by decide +kernel⟩
  | 16 => Sum.inl 2
  | 17 => Sum.inr ⟨(false, vertices_617), by decide +kernel⟩
  | 18 => Sum.inl 3
  | 19 => Sum.inl 4
  | 20 => Sum.inr ⟨(false, vertices_929), by decide +kernel⟩
  | 21 => Sum.inl 5
  | 22 => Sum.inl 6
  | 23 => Sum.inl 7
  | 24 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 1 2 3 30
cert_row_4 1 1 3 5 6 7 468 84 3
cert_row_4 2 2 3 4 6 8 696 56 3
cert_row_4 3 2 3 5 7 8 856 88 3
cert_rows
cert_pivot_2 0 1 4 2
cert_heightProof 4
cert_coverFacet 0 94
cert_cover_5 0 0 0 1 2 5 30 94 3
cert_coverFacet 1 326
cert_cover_2 1 1 0 5 7 70 326 3
cert_coverFacet 2 468
cert_cover_5 2 1 1 3 5 6 84 468 3
cert_coverFacet 3 696
cert_cover_5 3 2 2 3 4 6 56 696 3
cert_coverFacet 4 856
cert_cover_5 4 3 2 3 5 7 88 856 3
cert_coverFacet 5 912
cert_cover_2 5 6 3 7 8 400 912 3
cert_coveringFacets
cert_coveringProof_6
cert_certificate 4 6
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1317

end
end BundlePart12

section BundlePart13
/- Source: ProjectionCertificates/R_one_six_1318.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1318

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 391, 75, 835, 181, 617, 929, 94, 326, 468, 440, 856, 808, 7, 11, 67, 259, 53, 133, 41, 73, 161, 545, 577, 385, 769, 30, 70, 262, 74, 322, 84, 148, 324, 388, 56, 88, 280, 296, 552, 584, 776, 176, 336, 400, 416, 800, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_391, vertices_75, vertices_835, vertices_181, vertices_617, vertices_929, vertices_94, vertices_326, vertices_468, vertices_440, vertices_856, vertices_808] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_67, vertices_259, vertices_53, vertices_133, vertices_41, vertices_73, vertices_161, vertices_545, vertices_577, vertices_385, vertices_769, vertices_30, vertices_70, vertices_262, vertices_74, vertices_322, vertices_84, vertices_148, vertices_324, vertices_388, vertices_56, vertices_88, vertices_280, vertices_296, vertices_552, vertices_584, vertices_776, vertices_176, vertices_336, vertices_400, vertices_416, vertices_800, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_391), (false, vertices_75), (false, vertices_835), (false, vertices_181), (false, vertices_617), (false, vertices_929), (true, vertices_70), (true, vertices_84), (true, vertices_324), (true, vertices_88), (true, vertices_280), (true, vertices_296), (true, vertices_776), (true, vertices_336), (true, vertices_400)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 10 13 16 18 19 21 22 23 24
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 14 else
  if p.val = (false, vertices_391) then 11 else
  if p.val = (false, vertices_75) then 0 else
  if p.val = (false, vertices_835) then 12 else
  if p.val = (false, vertices_181) then 15 else
  if p.val = (false, vertices_617) then 17 else
  if p.val = (false, vertices_929) then 20 else
  if p.val = (true, vertices_70) then 1 else
  if p.val = (true, vertices_84) then 2 else
  if p.val = (true, vertices_324) then 3 else
  if p.val = (true, vertices_88) then 4 else
  if p.val = (true, vertices_280) then 5 else
  if p.val = (true, vertices_296) then 6 else
  if p.val = (true, vertices_776) then 7 else
  if p.val = (true, vertices_336) then 8 else
  if p.val = (true, vertices_400) then 9 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_75), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_70), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_84), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_324), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_88), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_280), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_296), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_776), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_336), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_400), by decide +kernel⟩
  | 10 => Sum.inl 0
  | 11 => Sum.inr ⟨(false, vertices_391), by decide +kernel⟩
  | 12 => Sum.inr ⟨(false, vertices_835), by decide +kernel⟩
  | 13 => Sum.inl 1
  | 14 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 15 => Sum.inr ⟨(false, vertices_181), by decide +kernel⟩
  | 16 => Sum.inl 2
  | 17 => Sum.inr ⟨(false, vertices_617), by decide +kernel⟩
  | 18 => Sum.inl 3
  | 19 => Sum.inl 4
  | 20 => Sum.inr ⟨(false, vertices_929), by decide +kernel⟩
  | 21 => Sum.inl 5
  | 22 => Sum.inl 6
  | 23 => Sum.inl 7
  | 24 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 1 2 3 30
cert_row_4 1 1 3 5 6 7 468 84 3
cert_row_4 2 2 3 4 6 7 440 56 3
cert_row_4 3 2 3 5 7 8 856 88 3
cert_rows
cert_pivot_2 0 1 4 2
cert_heightProof 4
cert_coverFacet 0 94
cert_cover_5 0 0 0 1 2 5 30 94 3
cert_coverFacet 1 326
cert_cover_2 1 1 0 5 7 70 326 3
cert_coverFacet 2 468
cert_cover_5 2 1 1 3 5 6 84 468 3
cert_coverFacet 3 440
cert_cover_5 3 2 2 3 4 6 56 440 3
cert_coverFacet 4 856
cert_cover_5 4 3 2 3 5 7 88 856 3
cert_coverFacet 5 808
cert_cover_2 5 4 2 7 8 296 808 3
cert_coveringFacets
cert_coveringProof_6
cert_certificate 4 6
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1318

end
end BundlePart13

section BundlePart14
/- Source: ProjectionCertificates/R_one_six_1319.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1319

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 647, 91, 835, 805, 369, 142, 330, 906, 188, 676, 472, 944, 7, 27, 67, 515, 37, 517, 49, 81, 289, 321, 769, 14, 134, 74, 138, 266, 322, 642, 770, 60, 140, 164, 548, 644, 88, 152, 328, 392, 176, 304, 336, 400, 672, 800, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_647, vertices_91, vertices_835, vertices_805, vertices_369, vertices_142, vertices_330, vertices_906, vertices_188, vertices_676, vertices_472, vertices_944] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_27, vertices_67, vertices_515, vertices_37, vertices_517, vertices_49, vertices_81, vertices_289, vertices_321, vertices_769, vertices_14, vertices_134, vertices_74, vertices_138, vertices_266, vertices_322, vertices_642, vertices_770, vertices_60, vertices_140, vertices_164, vertices_548, vertices_644, vertices_88, vertices_152, vertices_328, vertices_392, vertices_176, vertices_304, vertices_336, vertices_400, vertices_672, vertices_800, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_647), (false, vertices_91), (false, vertices_835), (false, vertices_805), (false, vertices_369), (true, vertices_138), (true, vertices_266), (true, vertices_140), (true, vertices_164), (true, vertices_152), (true, vertices_328), (true, vertices_392), (true, vertices_176), (true, vertices_400), (true, vertices_672), (true, vertices_896)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 14 11 18 19 21 22 23 24 25
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 15 else
  if p.val = (false, vertices_647) then 12 else
  if p.val = (false, vertices_91) then 16 else
  if p.val = (false, vertices_835) then 17 else
  if p.val = (false, vertices_805) then 13 else
  if p.val = (false, vertices_369) then 20 else
  if p.val = (true, vertices_138) then 0 else
  if p.val = (true, vertices_266) then 1 else
  if p.val = (true, vertices_140) then 2 else
  if p.val = (true, vertices_164) then 3 else
  if p.val = (true, vertices_152) then 4 else
  if p.val = (true, vertices_328) then 5 else
  if p.val = (true, vertices_392) then 6 else
  if p.val = (true, vertices_176) then 7 else
  if p.val = (true, vertices_400) then 8 else
  if p.val = (true, vertices_672) then 9 else
  if p.val = (true, vertices_896) then 10 else
  0
cert_priority
cert_nodeAtPriority_58 0 138 1 266 140 164 152 328 392 176 400 672 896 647 805 91 835 369
cert_priority_injective
cert_incidenceProof
cert_row_2 0 1 2 3 4 60
cert_row_4 1 0 2 6 7 8 906 138 3
cert_row_4 2 2 3 5 6 7 472 88 3
cert_row_4 3 3 4 6 7 8 944 176 3
cert_rows
cert_pivot_2 1 0 2 3
cert_heightProof 4
cert_coverFacet 0 142
cert_cover_2 0 1 0 2 6 14 142 3
cert_coverFacet 1 330
cert_cover_2 1 2 0 5 7 74 330 3
cert_coverFacet 2 906
cert_cover_5 2 1 0 2 6 7 138 906 3
cert_coverFacet 3 188
cert_cover_5 3 0 1 2 3 6 60 188 3
cert_coverFacet 4 676
cert_cover_2 4 4 1 6 8 164 676 3
cert_coverFacet 5 472
cert_cover_5 5 2 2 3 5 6 88 472 3
cert_coverFacet 6 944
cert_cover_5 6 3 3 4 6 7 176 944 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1319

end
end BundlePart14

section BundlePart15
/- Source: ProjectionCertificates/R_one_six_1324.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1324

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 391, 91, 835, 677, 625, 897, 334, 188, 396, 472, 944, 848, 7, 27, 67, 259, 37, 133, 49, 81, 545, 577, 385, 641, 769, 14, 262, 74, 322, 60, 140, 268, 164, 388, 88, 152, 328, 392, 176, 560, 336, 592, 400, 784, 672, 832, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_391, vertices_91, vertices_835, vertices_677, vertices_625, vertices_897, vertices_334, vertices_188, vertices_396, vertices_472, vertices_944, vertices_848] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_27, vertices_67, vertices_259, vertices_37, vertices_133, vertices_49, vertices_81, vertices_545, vertices_577, vertices_385, vertices_641, vertices_769, vertices_14, vertices_262, vertices_74, vertices_322, vertices_60, vertices_140, vertices_268, vertices_164, vertices_388, vertices_88, vertices_152, vertices_328, vertices_392, vertices_176, vertices_560, vertices_336, vertices_592, vertices_400, vertices_784, vertices_672, vertices_832, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_391), (false, vertices_91), (false, vertices_835), (false, vertices_677), (false, vertices_625), (false, vertices_897), (true, vertices_140), (true, vertices_268), (true, vertices_152), (true, vertices_328), (true, vertices_392), (true, vertices_176), (true, vertices_336), (true, vertices_400), (true, vertices_784)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 13 10 17 18 20 21 22 23 24
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 14 else
  if p.val = (false, vertices_391) then 11 else
  if p.val = (false, vertices_91) then 15 else
  if p.val = (false, vertices_835) then 16 else
  if p.val = (false, vertices_677) then 12 else
  if p.val = (false, vertices_625) then 19 else
  if p.val = (false, vertices_897) then 0 else
  if p.val = (true, vertices_140) then 1 else
  if p.val = (true, vertices_268) then 2 else
  if p.val = (true, vertices_152) then 3 else
  if p.val = (true, vertices_328) then 4 else
  if p.val = (true, vertices_392) then 5 else
  if p.val = (true, vertices_176) then 6 else
  if p.val = (true, vertices_336) then 7 else
  if p.val = (true, vertices_400) then 8 else
  if p.val = (true, vertices_784) then 9 else
  0
cert_priority
cert_nodeAtPriority_41 0 897 1 140 268 152 328 392 176 336 400 784 391 677 91 835 625
cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 2 5 7 334 14 3
cert_row_2 1 1 2 3 4 60
cert_row_4 2 2 3 5 6 7 472 88 3
cert_row_4 3 3 4 6 7 8 944 176 3
cert_rows
cert_pivot_2 0 1 2 3
cert_heightProof 4
cert_coverFacet 0 334
cert_cover_5 0 0 0 1 2 5 14 334 3
cert_coverFacet 1 188
cert_cover_5 1 1 1 2 3 6 60 188 3
cert_coverFacet 2 396
cert_cover_2 2 2 1 6 7 140 396 3
cert_coverFacet 3 472
cert_cover_5 3 2 2 3 5 6 88 472 3
cert_coverFacet 4 944
cert_cover_5 4 3 3 4 6 7 176 944 3
cert_coverFacet 5 848
cert_cover_2 5 5 3 7 8 336 848 3
cert_coveringFacets
cert_coveringProof_6
cert_certificate 4 6
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1324

end
end BundlePart15

section BundlePart16
/- Source: ProjectionCertificates/R_one_six_1325.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1325

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 91, 173, 457, 625, 929, 833, 334, 534, 902, 850, 396, 692, 27, 45, 73, 137, 49, 81, 161, 545, 321, 577, 385, 769, 14, 22, 262, 518, 74, 82, 530, 322, 770, 140, 268, 52, 532, 164, 388, 644, 328, 392, 560, 592, 672, 832, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_91, vertices_173, vertices_457, vertices_625, vertices_929, vertices_833, vertices_334, vertices_534, vertices_902, vertices_850, vertices_396, vertices_692] (by decide +kernel)
  polygons := literalFinset [vertices_27, vertices_45, vertices_73, vertices_137, vertices_49, vertices_81, vertices_161, vertices_545, vertices_321, vertices_577, vertices_385, vertices_769, vertices_14, vertices_22, vertices_262, vertices_518, vertices_74, vertices_82, vertices_530, vertices_322, vertices_770, vertices_140, vertices_268, vertices_52, vertices_532, vertices_164, vertices_388, vertices_644, vertices_328, vertices_392, vertices_560, vertices_592, vertices_672, vertices_832, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_91), (false, vertices_173), (false, vertices_457), (false, vertices_625), (false, vertices_929), (false, vertices_833), (true, vertices_262), (true, vertices_518), (true, vertices_530), (true, vertices_322), (true, vertices_770), (true, vertices_268), (true, vertices_532), (true, vertices_388), (true, vertices_644)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 10 12 15 17 19 21 22 23 24
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 13 else
  if p.val = (false, vertices_91) then 11 else
  if p.val = (false, vertices_173) then 14 else
  if p.val = (false, vertices_457) then 16 else
  if p.val = (false, vertices_625) then 18 else
  if p.val = (false, vertices_929) then 20 else
  if p.val = (false, vertices_833) then 0 else
  if p.val = (true, vertices_262) then 1 else
  if p.val = (true, vertices_518) then 2 else
  if p.val = (true, vertices_530) then 3 else
  if p.val = (true, vertices_322) then 4 else
  if p.val = (true, vertices_770) then 5 else
  if p.val = (true, vertices_268) then 6 else
  if p.val = (true, vertices_532) then 7 else
  if p.val = (true, vertices_388) then 8 else
  if p.val = (true, vertices_644) then 9 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_833), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_262), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_518), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_530), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_322), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_770), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_268), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_532), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_388), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_644), by decide +kernel⟩
  | 10 => Sum.inl 0
  | 11 => Sum.inr ⟨(false, vertices_91), by decide +kernel⟩
  | 12 => Sum.inl 1
  | 13 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 14 => Sum.inr ⟨(false, vertices_173), by decide +kernel⟩
  | 15 => Sum.inl 2
  | 16 => Sum.inr ⟨(false, vertices_457), by decide +kernel⟩
  | 17 => Sum.inl 3
  | 18 => Sum.inr ⟨(false, vertices_625), by decide +kernel⟩
  | 19 => Sum.inl 4
  | 20 => Sum.inr ⟨(false, vertices_929), by decide +kernel⟩
  | 21 => Sum.inl 5
  | 22 => Sum.inl 6
  | 23 => Sum.inl 7
  | 24 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 2 5 7 334 14 3
cert_row_4 1 0 3 5 7 8 850 82 3
cert_row_4 2 0 1 6 7 8 902 262 2
cert_row_4 3 1 3 4 6 8 692 52 3
cert_rows
cert_pivot_2 2 5 0 1
cert_heightProof 4
cert_coverFacet 0 334
cert_cover_5 0 0 0 1 2 5 14 334 3
cert_coverFacet 1 534
cert_cover_2 1 1 0 3 8 22 534 3
cert_coverFacet 2 902
cert_cover_5 2 2 0 1 6 7 262 902 2
cert_coverFacet 3 850
cert_cover_5 3 1 0 3 5 7 82 850 3
cert_coverFacet 4 396
cert_cover_2 4 2 1 6 7 140 396 3
cert_coverFacet 5 692
cert_cover_5 5 3 1 3 4 6 52 692 3
cert_coveringFacets
cert_coveringProof_6
cert_certificate 4 6
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1325

end
end BundlePart16

section BundlePart17
/- Source: ProjectionCertificates/R_one_six_1326.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1326

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 91, 173, 457, 369, 929, 334, 534, 902, 850, 396, 692, 816, 27, 45, 73, 137, 49, 81, 161, 289, 321, 385, 14, 22, 262, 518, 74, 82, 530, 322, 770, 140, 268, 52, 532, 164, 388, 644, 328, 392, 304, 560, 336, 784, 672, 800, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_91, vertices_173, vertices_457, vertices_369, vertices_929, vertices_334, vertices_534, vertices_902, vertices_850, vertices_396, vertices_692, vertices_816] (by decide +kernel)
  polygons := literalFinset [vertices_27, vertices_45, vertices_73, vertices_137, vertices_49, vertices_81, vertices_161, vertices_289, vertices_321, vertices_385, vertices_14, vertices_22, vertices_262, vertices_518, vertices_74, vertices_82, vertices_530, vertices_322, vertices_770, vertices_140, vertices_268, vertices_52, vertices_532, vertices_164, vertices_388, vertices_644, vertices_328, vertices_392, vertices_304, vertices_560, vertices_336, vertices_784, vertices_672, vertices_800, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_91), (false, vertices_173), (false, vertices_457), (false, vertices_369), (false, vertices_929), (true, vertices_262), (true, vertices_518), (true, vertices_530), (true, vertices_322), (true, vertices_770), (true, vertices_268), (true, vertices_532), (true, vertices_388), (true, vertices_644), (true, vertices_560), (true, vertices_784)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 11 13 16 18 20 22 23 24 25
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 14 else
  if p.val = (false, vertices_91) then 12 else
  if p.val = (false, vertices_173) then 15 else
  if p.val = (false, vertices_457) then 17 else
  if p.val = (false, vertices_369) then 19 else
  if p.val = (false, vertices_929) then 21 else
  if p.val = (true, vertices_262) then 0 else
  if p.val = (true, vertices_518) then 1 else
  if p.val = (true, vertices_530) then 2 else
  if p.val = (true, vertices_322) then 3 else
  if p.val = (true, vertices_770) then 4 else
  if p.val = (true, vertices_268) then 5 else
  if p.val = (true, vertices_532) then 6 else
  if p.val = (true, vertices_388) then 7 else
  if p.val = (true, vertices_644) then 8 else
  if p.val = (true, vertices_560) then 9 else
  if p.val = (true, vertices_784) then 10 else
  0
cert_priority
cert_nodeAtPriority_16 262 518 530 322 770 268 532 388 644 560 784
cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 2 5 7 334 14 3
cert_row_4 1 0 3 5 7 8 850 82 3
cert_row_4 2 0 1 6 7 8 902 262 2
cert_row_4 3 1 3 4 6 8 692 52 3
cert_rows
cert_pivot_2 2 5 0 1
cert_heightProof 4
cert_coverFacet 0 334
cert_cover_5 0 0 0 1 2 5 14 334 3
cert_coverFacet 1 534
cert_cover_2 1 1 0 3 8 22 534 3
cert_coverFacet 2 902
cert_cover_5 2 2 0 1 6 7 262 902 2
cert_coverFacet 3 850
cert_cover_5 3 1 0 3 5 7 82 850 3
cert_coverFacet 4 396
cert_cover_2 4 2 1 6 7 140 396 3
cert_coverFacet 5 692
cert_cover_5 5 3 1 3 4 6 52 692 3
cert_coverFacet 6 816
cert_cover_2 6 4 3 7 8 304 816 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1326

end
end BundlePart17

section BundlePart18
/- Source: ProjectionCertificates/R_one_six_1327.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1327

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 327, 91, 181, 901, 465, 270, 842, 684, 780, 632, 944, 848, 7, 27, 67, 53, 133, 261, 81, 145, 321, 385, 14, 262, 74, 266, 322, 44, 268, 524, 164, 644, 772, 56, 88, 552, 584, 776, 176, 560, 336, 592, 400, 784, 672, 832, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_327, vertices_91, vertices_181, vertices_901, vertices_465, vertices_270, vertices_842, vertices_684, vertices_780, vertices_632, vertices_944, vertices_848] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_27, vertices_67, vertices_53, vertices_133, vertices_261, vertices_81, vertices_145, vertices_321, vertices_385, vertices_14, vertices_262, vertices_74, vertices_266, vertices_322, vertices_44, vertices_268, vertices_524, vertices_164, vertices_644, vertices_772, vertices_56, vertices_88, vertices_552, vertices_584, vertices_776, vertices_176, vertices_560, vertices_336, vertices_592, vertices_400, vertices_784, vertices_672, vertices_832, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_327), (false, vertices_91), (false, vertices_181), (false, vertices_901), (false, vertices_465), (true, vertices_266), (true, vertices_268), (true, vertices_524), (true, vertices_552), (true, vertices_584), (true, vertices_776), (true, vertices_560), (true, vertices_592), (true, vertices_784), (true, vertices_672), (true, vertices_832)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 11 14 18 19 21 22 23 24 25
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 15 else
  if p.val = (false, vertices_327) then 12 else
  if p.val = (false, vertices_91) then 13 else
  if p.val = (false, vertices_181) then 16 else
  if p.val = (false, vertices_901) then 17 else
  if p.val = (false, vertices_465) then 20 else
  if p.val = (true, vertices_266) then 0 else
  if p.val = (true, vertices_268) then 1 else
  if p.val = (true, vertices_524) then 2 else
  if p.val = (true, vertices_552) then 3 else
  if p.val = (true, vertices_584) then 4 else
  if p.val = (true, vertices_776) then 5 else
  if p.val = (true, vertices_560) then 6 else
  if p.val = (true, vertices_592) then 7 else
  if p.val = (true, vertices_784) then 8 else
  if p.val = (true, vertices_672) then 9 else
  if p.val = (true, vertices_832) then 10 else
  0
cert_priority
cert_nodeAtPriority_58 1 266 0 268 524 552 584 776 560 592 784 672 832 327 91 181 901 465
cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 2 5 7 8 842 74 3
cert_row_4 1 1 2 4 6 8 684 44 3
cert_row_4 2 2 3 4 5 8 632 56 3
cert_row_4 3 3 4 6 7 8 944 176 3
cert_rows
cert_pivot_2 0 1 2 3
cert_heightProof 4
cert_coverFacet 0 270
cert_cover_2 0 1 0 2 7 14 270 3
cert_coverFacet 1 842
cert_cover_5 1 0 0 2 5 7 74 842 3
cert_coverFacet 2 684
cert_cover_5 2 1 1 2 4 6 44 684 3
cert_coverFacet 3 780
cert_cover_2 3 2 1 7 8 268 780 3
cert_coverFacet 4 632
cert_cover_5 4 2 2 3 4 5 56 632 3
cert_coverFacet 5 944
cert_cover_5 5 3 3 4 6 7 176 944 3
cert_coverFacet 6 848
cert_cover_2 6 5 3 7 8 336 848 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1327

end
end BundlePart18

section BundlePart19
/- Source: ProjectionCertificates/R_one_six_1328.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1328

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 327, 91, 181, 901, 465, 526, 774, 842, 684, 632, 944, 848, 7, 27, 67, 53, 133, 261, 81, 145, 321, 385, 14, 262, 518, 74, 522, 322, 770, 44, 524, 164, 644, 772, 56, 88, 552, 584, 176, 560, 336, 592, 400, 784, 672, 832, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_327, vertices_91, vertices_181, vertices_901, vertices_465, vertices_526, vertices_774, vertices_842, vertices_684, vertices_632, vertices_944, vertices_848] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_27, vertices_67, vertices_53, vertices_133, vertices_261, vertices_81, vertices_145, vertices_321, vertices_385, vertices_14, vertices_262, vertices_518, vertices_74, vertices_522, vertices_322, vertices_770, vertices_44, vertices_524, vertices_164, vertices_644, vertices_772, vertices_56, vertices_88, vertices_552, vertices_584, vertices_176, vertices_560, vertices_336, vertices_592, vertices_400, vertices_784, vertices_672, vertices_832, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_327), (false, vertices_91), (false, vertices_181), (false, vertices_901), (false, vertices_465), (true, vertices_518), (true, vertices_522), (true, vertices_770), (true, vertices_524), (true, vertices_552), (true, vertices_584), (true, vertices_560), (true, vertices_592), (true, vertices_784), (true, vertices_672), (true, vertices_832)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 11 14 18 19 21 22 23 24 25
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 15 else
  if p.val = (false, vertices_327) then 12 else
  if p.val = (false, vertices_91) then 13 else
  if p.val = (false, vertices_181) then 16 else
  if p.val = (false, vertices_901) then 17 else
  if p.val = (false, vertices_465) then 20 else
  if p.val = (true, vertices_518) then 0 else
  if p.val = (true, vertices_522) then 1 else
  if p.val = (true, vertices_770) then 2 else
  if p.val = (true, vertices_524) then 3 else
  if p.val = (true, vertices_552) then 4 else
  if p.val = (true, vertices_584) then 5 else
  if p.val = (true, vertices_560) then 6 else
  if p.val = (true, vertices_592) then 7 else
  if p.val = (true, vertices_784) then 8 else
  if p.val = (true, vertices_672) then 9 else
  if p.val = (true, vertices_832) then 10 else
  0
cert_priority
cert_nodeAtPriority_58 1 518 0 522 770 524 552 584 560 592 784 672 832 327 91 181 901 465
cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 2 5 7 8 842 74 3
cert_row_4 1 1 2 4 6 8 684 44 3
cert_row_4 2 2 3 4 5 8 632 56 3
cert_row_4 3 3 4 6 7 8 944 176 3
cert_rows
cert_pivot_2 0 1 2 3
cert_heightProof 4
cert_coverFacet 0 526
cert_cover_2 0 1 0 2 8 14 526 3
cert_coverFacet 1 774
cert_cover_2 1 1 0 7 8 262 774 3
cert_coverFacet 2 842
cert_cover_5 2 0 0 2 5 7 74 842 3
cert_coverFacet 3 684
cert_cover_5 3 1 1 2 4 6 44 684 3
cert_coverFacet 4 632
cert_cover_5 4 2 2 3 4 5 56 632 3
cert_coverFacet 5 944
cert_cover_5 5 3 3 4 6 7 176 944 3
cert_coverFacet 6 848
cert_cover_2 6 5 3 7 8 336 848 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1328

end
end BundlePart19

section BundlePart20
/- Source: ProjectionCertificates/R_one_six_1329.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1329

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 327, 91, 181, 901, 465, 526, 774, 842, 684, 376, 808, 944, 7, 27, 67, 53, 133, 261, 81, 145, 321, 385, 14, 262, 518, 74, 522, 322, 770, 44, 524, 164, 644, 772, 56, 88, 296, 552, 328, 776, 176, 304, 336, 400, 672, 800, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_327, vertices_91, vertices_181, vertices_901, vertices_465, vertices_526, vertices_774, vertices_842, vertices_684, vertices_376, vertices_808, vertices_944] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_27, vertices_67, vertices_53, vertices_133, vertices_261, vertices_81, vertices_145, vertices_321, vertices_385, vertices_14, vertices_262, vertices_518, vertices_74, vertices_522, vertices_322, vertices_770, vertices_44, vertices_524, vertices_164, vertices_644, vertices_772, vertices_56, vertices_88, vertices_296, vertices_552, vertices_328, vertices_776, vertices_176, vertices_304, vertices_336, vertices_400, vertices_672, vertices_800, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_327), (false, vertices_91), (false, vertices_181), (false, vertices_901), (false, vertices_465), (true, vertices_518), (true, vertices_522), (true, vertices_770), (true, vertices_524), (true, vertices_296), (true, vertices_552), (true, vertices_328), (true, vertices_776), (true, vertices_304), (true, vertices_672), (true, vertices_800)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 11 14 18 19 21 22 23 24 25
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 15 else
  if p.val = (false, vertices_327) then 12 else
  if p.val = (false, vertices_91) then 13 else
  if p.val = (false, vertices_181) then 16 else
  if p.val = (false, vertices_901) then 17 else
  if p.val = (false, vertices_465) then 20 else
  if p.val = (true, vertices_518) then 0 else
  if p.val = (true, vertices_522) then 1 else
  if p.val = (true, vertices_770) then 2 else
  if p.val = (true, vertices_524) then 3 else
  if p.val = (true, vertices_296) then 4 else
  if p.val = (true, vertices_552) then 5 else
  if p.val = (true, vertices_328) then 6 else
  if p.val = (true, vertices_776) then 7 else
  if p.val = (true, vertices_304) then 8 else
  if p.val = (true, vertices_672) then 9 else
  if p.val = (true, vertices_800) then 10 else
  0
cert_priority
cert_nodeAtPriority_58 1 518 0 522 770 524 296 552 328 776 304 672 800 327 91 181 901 465
cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 2 5 7 8 842 74 3
cert_row_4 1 1 2 4 6 8 684 44 3
cert_row_4 2 2 3 4 5 7 376 56 3
cert_row_4 3 3 4 6 7 8 944 176 3
cert_rows
cert_pivot_2 0 1 2 3
cert_heightProof 4
cert_coverFacet 0 526
cert_cover_2 0 1 0 2 8 14 526 3
cert_coverFacet 1 774
cert_cover_2 1 1 0 7 8 262 774 3
cert_coverFacet 2 842
cert_cover_5 2 0 0 2 5 7 74 842 3
cert_coverFacet 3 684
cert_cover_5 3 1 1 2 4 6 44 684 3
cert_coverFacet 4 376
cert_cover_5 4 2 2 3 4 5 56 376 3
cert_coverFacet 5 808
cert_cover_2 5 4 2 7 8 296 808 3
cert_coverFacet 6 944
cert_cover_5 6 3 3 4 6 7 176 944 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1329

end
end BundlePart20

section BundlePart21
/- Source: ProjectionCertificates/R_one_six_1330.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1330

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 327, 779, 181, 901, 681, 94, 330, 468, 120, 872, 368, 944, 7, 11, 259, 53, 133, 261, 41, 521, 161, 641, 769, 30, 70, 74, 266, 322, 84, 148, 324, 388, 56, 88, 104, 552, 328, 776, 112, 176, 304, 336, 400, 352, 672, 800, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_327, vertices_779, vertices_181, vertices_901, vertices_681, vertices_94, vertices_330, vertices_468, vertices_120, vertices_872, vertices_368, vertices_944] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_259, vertices_53, vertices_133, vertices_261, vertices_41, vertices_521, vertices_161, vertices_641, vertices_769, vertices_30, vertices_70, vertices_74, vertices_266, vertices_322, vertices_84, vertices_148, vertices_324, vertices_388, vertices_56, vertices_88, vertices_104, vertices_552, vertices_328, vertices_776, vertices_112, vertices_176, vertices_304, vertices_336, vertices_400, vertices_352, vertices_672, vertices_800, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_327), (false, vertices_779), (false, vertices_181), (false, vertices_901), (false, vertices_681), (true, vertices_74), (true, vertices_84), (true, vertices_88), (true, vertices_104), (true, vertices_328), (true, vertices_112), (true, vertices_304), (true, vertices_336), (true, vertices_400), (true, vertices_352), (true, vertices_800)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 11 14 18 20 21 22 23 24 25
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 15 else
  if p.val = (false, vertices_327) then 12 else
  if p.val = (false, vertices_779) then 13 else
  if p.val = (false, vertices_181) then 16 else
  if p.val = (false, vertices_901) then 17 else
  if p.val = (false, vertices_681) then 19 else
  if p.val = (true, vertices_74) then 0 else
  if p.val = (true, vertices_84) then 1 else
  if p.val = (true, vertices_88) then 2 else
  if p.val = (true, vertices_104) then 3 else
  if p.val = (true, vertices_328) then 4 else
  if p.val = (true, vertices_112) then 5 else
  if p.val = (true, vertices_304) then 6 else
  if p.val = (true, vertices_336) then 7 else
  if p.val = (true, vertices_400) then 8 else
  if p.val = (true, vertices_352) then 9 else
  if p.val = (true, vertices_800) then 10 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_74), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_84), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_88), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_104), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_328), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_112), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_304), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_336), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_400), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_352), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_800), by decide +kernel⟩
  | 11 => Sum.inl 0
  | 12 => Sum.inr ⟨(false, vertices_327), by decide +kernel⟩
  | 13 => Sum.inr ⟨(false, vertices_779), by decide +kernel⟩
  | 14 => Sum.inl 1
  | 15 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 16 => Sum.inr ⟨(false, vertices_181), by decide +kernel⟩
  | 17 => Sum.inr ⟨(false, vertices_901), by decide +kernel⟩
  | 18 => Sum.inl 2
  | 19 => Sum.inr ⟨(false, vertices_681), by decide +kernel⟩
  | 20 => Sum.inl 3
  | 21 => Sum.inl 4
  | 22 => Sum.inl 5
  | 23 => Sum.inl 6
  | 24 => Sum.inl 7
  | 25 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 1 2 3 30
cert_row_4 1 1 3 5 6 7 468 84 3
cert_row_4 2 2 4 5 7 8 872 104 3
cert_row_4 3 3 4 6 7 8 944 176 3
cert_rows
cert_pivot_2 0 1 2 3
cert_heightProof 4
cert_coverFacet 0 94
cert_cover_5 0 0 0 1 2 5 30 94 3
cert_coverFacet 1 330
cert_cover_2 1 2 0 5 7 74 330 3
cert_coverFacet 2 468
cert_cover_5 2 1 1 3 5 6 84 468 3
cert_coverFacet 3 120
cert_cover_2 3 3 2 4 5 56 120 3
cert_coverFacet 4 872
cert_cover_5 4 2 2 4 5 7 104 872 3
cert_coverFacet 5 368
cert_cover_2 5 4 3 5 7 112 368 3
cert_coverFacet 6 944
cert_cover_5 6 3 3 4 6 7 176 944 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1330

end
end BundlePart21

section BundlePart22
/- Source: ProjectionCertificates/R_one_six_1331.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1331

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 327, 779, 181, 901, 681, 94, 330, 468, 632, 840, 944, 848, 7, 11, 259, 53, 133, 261, 41, 521, 161, 641, 769, 30, 70, 74, 266, 322, 84, 148, 324, 388, 56, 88, 552, 328, 584, 776, 176, 560, 336, 592, 400, 784, 672, 832, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_327, vertices_779, vertices_181, vertices_901, vertices_681, vertices_94, vertices_330, vertices_468, vertices_632, vertices_840, vertices_944, vertices_848] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_259, vertices_53, vertices_133, vertices_261, vertices_41, vertices_521, vertices_161, vertices_641, vertices_769, vertices_30, vertices_70, vertices_74, vertices_266, vertices_322, vertices_84, vertices_148, vertices_324, vertices_388, vertices_56, vertices_88, vertices_552, vertices_328, vertices_584, vertices_776, vertices_176, vertices_560, vertices_336, vertices_592, vertices_400, vertices_784, vertices_672, vertices_832, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_327), (false, vertices_779), (false, vertices_181), (false, vertices_901), (false, vertices_681), (true, vertices_74), (true, vertices_84), (true, vertices_88), (true, vertices_328), (true, vertices_584), (true, vertices_560), (true, vertices_336), (true, vertices_592), (true, vertices_400), (true, vertices_784), (true, vertices_832)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 11 14 18 20 21 22 23 24 25
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 15 else
  if p.val = (false, vertices_327) then 12 else
  if p.val = (false, vertices_779) then 13 else
  if p.val = (false, vertices_181) then 16 else
  if p.val = (false, vertices_901) then 17 else
  if p.val = (false, vertices_681) then 19 else
  if p.val = (true, vertices_74) then 0 else
  if p.val = (true, vertices_84) then 1 else
  if p.val = (true, vertices_88) then 2 else
  if p.val = (true, vertices_328) then 3 else
  if p.val = (true, vertices_584) then 4 else
  if p.val = (true, vertices_560) then 5 else
  if p.val = (true, vertices_336) then 6 else
  if p.val = (true, vertices_592) then 7 else
  if p.val = (true, vertices_400) then 8 else
  if p.val = (true, vertices_784) then 9 else
  if p.val = (true, vertices_832) then 10 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_74), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_84), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_88), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_328), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_584), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_560), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_336), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_592), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_400), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_784), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_832), by decide +kernel⟩
  | 11 => Sum.inl 0
  | 12 => Sum.inr ⟨(false, vertices_327), by decide +kernel⟩
  | 13 => Sum.inr ⟨(false, vertices_779), by decide +kernel⟩
  | 14 => Sum.inl 1
  | 15 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 16 => Sum.inr ⟨(false, vertices_181), by decide +kernel⟩
  | 17 => Sum.inr ⟨(false, vertices_901), by decide +kernel⟩
  | 18 => Sum.inl 2
  | 19 => Sum.inr ⟨(false, vertices_681), by decide +kernel⟩
  | 20 => Sum.inl 3
  | 21 => Sum.inl 4
  | 22 => Sum.inl 5
  | 23 => Sum.inl 6
  | 24 => Sum.inl 7
  | 25 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 1 2 3 30
cert_row_4 1 1 3 5 6 7 468 84 3
cert_row_4 2 2 3 4 5 8 632 56 3
cert_row_4 3 3 4 6 7 8 944 176 3
cert_rows
cert_pivot_2 0 1 2 3
cert_heightProof 4
cert_coverFacet 0 94
cert_cover_5 0 0 0 1 2 5 30 94 3
cert_coverFacet 1 330
cert_cover_2 1 2 0 5 7 74 330 3
cert_coverFacet 2 468
cert_cover_5 2 1 1 3 5 6 84 468 3
cert_coverFacet 3 632
cert_cover_5 3 2 2 3 4 5 56 632 3
cert_coverFacet 4 840
cert_cover_2 4 5 2 7 8 328 840 3
cert_coverFacet 5 944
cert_cover_5 5 3 3 4 6 7 176 944 3
cert_coverFacet 6 848
cert_cover_2 6 5 3 7 8 336 848 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1331

end
end BundlePart22

section BundlePart23
/- Source: ProjectionCertificates/R_one_six_1332.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1332

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 327, 779, 181, 901, 681, 94, 586, 834, 468, 632, 944, 848, 7, 11, 259, 53, 133, 261, 41, 521, 161, 641, 769, 30, 70, 74, 522, 322, 578, 770, 84, 148, 324, 388, 56, 88, 552, 584, 176, 560, 336, 592, 400, 784, 672, 832, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_327, vertices_779, vertices_181, vertices_901, vertices_681, vertices_94, vertices_586, vertices_834, vertices_468, vertices_632, vertices_944, vertices_848] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_259, vertices_53, vertices_133, vertices_261, vertices_41, vertices_521, vertices_161, vertices_641, vertices_769, vertices_30, vertices_70, vertices_74, vertices_522, vertices_322, vertices_578, vertices_770, vertices_84, vertices_148, vertices_324, vertices_388, vertices_56, vertices_88, vertices_552, vertices_584, vertices_176, vertices_560, vertices_336, vertices_592, vertices_400, vertices_784, vertices_672, vertices_832, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_327), (false, vertices_779), (false, vertices_181), (false, vertices_901), (false, vertices_681), (true, vertices_74), (true, vertices_578), (true, vertices_84), (true, vertices_88), (true, vertices_584), (true, vertices_560), (true, vertices_336), (true, vertices_592), (true, vertices_400), (true, vertices_784), (true, vertices_832)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 11 14 18 20 21 22 23 24 25
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 15 else
  if p.val = (false, vertices_327) then 12 else
  if p.val = (false, vertices_779) then 13 else
  if p.val = (false, vertices_181) then 16 else
  if p.val = (false, vertices_901) then 17 else
  if p.val = (false, vertices_681) then 19 else
  if p.val = (true, vertices_74) then 0 else
  if p.val = (true, vertices_578) then 1 else
  if p.val = (true, vertices_84) then 2 else
  if p.val = (true, vertices_88) then 3 else
  if p.val = (true, vertices_584) then 4 else
  if p.val = (true, vertices_560) then 5 else
  if p.val = (true, vertices_336) then 6 else
  if p.val = (true, vertices_592) then 7 else
  if p.val = (true, vertices_400) then 8 else
  if p.val = (true, vertices_784) then 9 else
  if p.val = (true, vertices_832) then 10 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_74), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_578), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_84), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_88), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_584), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_560), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_336), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_592), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_400), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_784), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_832), by decide +kernel⟩
  | 11 => Sum.inl 0
  | 12 => Sum.inr ⟨(false, vertices_327), by decide +kernel⟩
  | 13 => Sum.inr ⟨(false, vertices_779), by decide +kernel⟩
  | 14 => Sum.inl 1
  | 15 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 16 => Sum.inr ⟨(false, vertices_181), by decide +kernel⟩
  | 17 => Sum.inr ⟨(false, vertices_901), by decide +kernel⟩
  | 18 => Sum.inl 2
  | 19 => Sum.inr ⟨(false, vertices_681), by decide +kernel⟩
  | 20 => Sum.inl 3
  | 21 => Sum.inl 4
  | 22 => Sum.inl 5
  | 23 => Sum.inl 6
  | 24 => Sum.inl 7
  | 25 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 1 2 3 30
cert_row_4 1 1 3 5 6 7 468 84 3
cert_row_4 2 2 3 4 5 8 632 56 3
cert_row_4 3 3 4 6 7 8 944 176 3
cert_rows
cert_pivot_2 0 1 2 3
cert_heightProof 4
cert_coverFacet 0 94
cert_cover_5 0 0 0 1 2 5 30 94 3
cert_coverFacet 1 586
cert_cover_2 1 2 0 5 8 74 586 3
cert_coverFacet 2 834
cert_cover_2 2 5 0 7 8 322 834 3
cert_coverFacet 3 468
cert_cover_5 3 1 1 3 5 6 84 468 3
cert_coverFacet 4 632
cert_cover_5 4 2 2 3 4 5 56 632 3
cert_coverFacet 5 944
cert_cover_5 5 3 3 4 6 7 176 944 3
cert_coverFacet 6 848
cert_cover_2 6 5 3 7 8 336 848 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1332

end
end BundlePart23

section BundlePart24
/- Source: ProjectionCertificates/R_one_six_1333.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1333

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 583, 91, 181, 901, 465, 833, 526, 842, 684, 376, 808, 944, 7, 27, 67, 53, 133, 517, 81, 145, 321, 577, 385, 769, 14, 518, 74, 522, 578, 44, 524, 164, 644, 56, 88, 296, 552, 328, 776, 176, 304, 336, 400, 672, 800, 832, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_583, vertices_91, vertices_181, vertices_901, vertices_465, vertices_833, vertices_526, vertices_842, vertices_684, vertices_376, vertices_808, vertices_944] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_27, vertices_67, vertices_53, vertices_133, vertices_517, vertices_81, vertices_145, vertices_321, vertices_577, vertices_385, vertices_769, vertices_14, vertices_518, vertices_74, vertices_522, vertices_578, vertices_44, vertices_524, vertices_164, vertices_644, vertices_56, vertices_88, vertices_296, vertices_552, vertices_328, vertices_776, vertices_176, vertices_304, vertices_336, vertices_400, vertices_672, vertices_800, vertices_832, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_583), (false, vertices_91), (false, vertices_181), (false, vertices_901), (false, vertices_465), (false, vertices_833), (true, vertices_522), (true, vertices_524), (true, vertices_296), (true, vertices_552), (true, vertices_328), (true, vertices_776), (true, vertices_304), (true, vertices_672), (true, vertices_800)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 10 13 17 18 20 21 22 23 24
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 14 else
  if p.val = (false, vertices_583) then 11 else
  if p.val = (false, vertices_91) then 12 else
  if p.val = (false, vertices_181) then 15 else
  if p.val = (false, vertices_901) then 16 else
  if p.val = (false, vertices_465) then 19 else
  if p.val = (false, vertices_833) then 0 else
  if p.val = (true, vertices_522) then 1 else
  if p.val = (true, vertices_524) then 2 else
  if p.val = (true, vertices_296) then 3 else
  if p.val = (true, vertices_552) then 4 else
  if p.val = (true, vertices_328) then 5 else
  if p.val = (true, vertices_776) then 6 else
  if p.val = (true, vertices_304) then 7 else
  if p.val = (true, vertices_672) then 8 else
  if p.val = (true, vertices_800) then 9 else
  0
cert_priority
cert_nodeAtPriority_41 1 833 0 522 524 296 552 328 776 304 672 800 583 91 181 901 465
cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 2 5 7 8 842 74 3
cert_row_4 1 1 2 4 6 8 684 44 3
cert_row_4 2 2 3 4 5 7 376 56 3
cert_row_4 3 3 4 6 7 8 944 176 3
cert_rows
cert_pivot_2 0 1 2 3
cert_heightProof 4
cert_coverFacet 0 526
cert_cover_2 0 1 0 2 8 14 526 3
cert_coverFacet 1 842
cert_cover_5 1 0 0 2 5 7 74 842 3
cert_coverFacet 2 684
cert_cover_5 2 1 1 2 4 6 44 684 3
cert_coverFacet 3 376
cert_cover_5 3 2 2 3 4 5 56 376 3
cert_coverFacet 4 808
cert_cover_2 4 4 2 7 8 296 808 3
cert_coverFacet 5 944
cert_cover_5 5 3 3 4 6 7 176 944 3
cert_coveringFacets
cert_coveringProof_6
cert_certificate 4 6
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1333

end
end BundlePart24

section BundlePart25
/- Source: ProjectionCertificates/R_one_six_1334.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1334

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 519, 91, 835, 181, 901, 465, 590, 684, 376, 808, 840, 944, 7, 27, 67, 515, 53, 133, 517, 81, 145, 321, 385, 769, 14, 518, 74, 578, 44, 524, 164, 644, 56, 88, 296, 552, 328, 584, 776, 176, 304, 336, 400, 672, 800, 832, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_519, vertices_91, vertices_835, vertices_181, vertices_901, vertices_465, vertices_590, vertices_684, vertices_376, vertices_808, vertices_840, vertices_944] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_27, vertices_67, vertices_515, vertices_53, vertices_133, vertices_517, vertices_81, vertices_145, vertices_321, vertices_385, vertices_769, vertices_14, vertices_518, vertices_74, vertices_578, vertices_44, vertices_524, vertices_164, vertices_644, vertices_56, vertices_88, vertices_296, vertices_552, vertices_328, vertices_584, vertices_776, vertices_176, vertices_304, vertices_336, vertices_400, vertices_672, vertices_800, vertices_832, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_519), (false, vertices_91), (false, vertices_835), (false, vertices_181), (false, vertices_901), (false, vertices_465), (true, vertices_524), (true, vertices_296), (true, vertices_552), (true, vertices_328), (true, vertices_584), (true, vertices_776), (true, vertices_304), (true, vertices_672), (true, vertices_800)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 10 13 17 18 20 21 22 23 24
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 14 else
  if p.val = (false, vertices_519) then 0 else
  if p.val = (false, vertices_91) then 11 else
  if p.val = (false, vertices_835) then 12 else
  if p.val = (false, vertices_181) then 15 else
  if p.val = (false, vertices_901) then 16 else
  if p.val = (false, vertices_465) then 19 else
  if p.val = (true, vertices_524) then 1 else
  if p.val = (true, vertices_296) then 2 else
  if p.val = (true, vertices_552) then 3 else
  if p.val = (true, vertices_328) then 4 else
  if p.val = (true, vertices_584) then 5 else
  if p.val = (true, vertices_776) then 6 else
  if p.val = (true, vertices_304) then 7 else
  if p.val = (true, vertices_672) then 8 else
  if p.val = (true, vertices_800) then 9 else
  0
cert_priority
cert_nodeAtPriority_41 1 519 0 524 296 552 328 584 776 304 672 800 91 835 181 901 465
cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 2 5 8 590 14 3
cert_row_4 1 1 2 4 6 8 684 44 3
cert_row_4 2 2 3 4 5 7 376 56 3
cert_row_4 3 3 4 6 7 8 944 176 3
cert_rows
cert_pivot_2 0 1 2 3
cert_heightProof 4
cert_coverFacet 0 590
cert_cover_5 0 0 0 1 2 5 14 590 3
cert_coverFacet 1 684
cert_cover_5 1 1 1 2 4 6 44 684 3
cert_coverFacet 2 376
cert_cover_5 2 2 2 3 4 5 56 376 3
cert_coverFacet 3 808
cert_cover_2 3 4 2 7 8 296 808 3
cert_coverFacet 4 840
cert_cover_2 4 5 2 7 8 328 840 3
cert_coverFacet 5 944
cert_cover_5 5 3 3 4 6 7 176 944 3
cert_coveringFacets
cert_coveringProof_6
cert_certificate 4 6
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1334

end
end BundlePart25

section BundlePart26
/- Source: ProjectionCertificates/R_one_six_1335.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1335

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 519, 91, 835, 181, 901, 465, 590, 684, 376, 616, 944, 864, 7, 27, 67, 515, 53, 133, 517, 81, 145, 321, 385, 769, 14, 518, 74, 578, 44, 524, 164, 644, 56, 88, 104, 552, 584, 176, 304, 336, 400, 352, 608, 672, 800, 832, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_519, vertices_91, vertices_835, vertices_181, vertices_901, vertices_465, vertices_590, vertices_684, vertices_376, vertices_616, vertices_944, vertices_864] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_27, vertices_67, vertices_515, vertices_53, vertices_133, vertices_517, vertices_81, vertices_145, vertices_321, vertices_385, vertices_769, vertices_14, vertices_518, vertices_74, vertices_578, vertices_44, vertices_524, vertices_164, vertices_644, vertices_56, vertices_88, vertices_104, vertices_552, vertices_584, vertices_176, vertices_304, vertices_336, vertices_400, vertices_352, vertices_608, vertices_672, vertices_800, vertices_832, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_519), (false, vertices_91), (false, vertices_835), (false, vertices_181), (false, vertices_901), (false, vertices_465), (true, vertices_524), (true, vertices_104), (true, vertices_552), (true, vertices_584), (true, vertices_304), (true, vertices_352), (true, vertices_608), (true, vertices_672), (true, vertices_800)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 10 13 17 18 20 21 22 23 24
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 14 else
  if p.val = (false, vertices_519) then 0 else
  if p.val = (false, vertices_91) then 11 else
  if p.val = (false, vertices_835) then 12 else
  if p.val = (false, vertices_181) then 15 else
  if p.val = (false, vertices_901) then 16 else
  if p.val = (false, vertices_465) then 19 else
  if p.val = (true, vertices_524) then 1 else
  if p.val = (true, vertices_104) then 2 else
  if p.val = (true, vertices_552) then 3 else
  if p.val = (true, vertices_584) then 4 else
  if p.val = (true, vertices_304) then 5 else
  if p.val = (true, vertices_352) then 6 else
  if p.val = (true, vertices_608) then 7 else
  if p.val = (true, vertices_672) then 8 else
  if p.val = (true, vertices_800) then 9 else
  0
cert_priority
cert_nodeAtPriority_41 1 519 0 524 104 552 584 304 352 608 672 800 91 835 181 901 465
cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 2 5 8 590 14 3
cert_row_4 1 1 2 4 6 8 684 44 3
cert_row_4 2 2 3 4 5 7 376 56 3
cert_row_4 3 3 4 6 7 8 944 176 3
cert_rows
cert_pivot_2 0 1 2 3
cert_heightProof 4
cert_coverFacet 0 590
cert_cover_5 0 0 0 1 2 5 14 590 3
cert_coverFacet 1 684
cert_cover_5 1 1 1 2 4 6 44 684 3
cert_coverFacet 2 376
cert_cover_5 2 2 2 3 4 5 56 376 3
cert_coverFacet 3 616
cert_cover_2 3 4 2 5 8 104 616 3
cert_coverFacet 4 944
cert_cover_5 4 3 3 4 6 7 176 944 3
cert_coverFacet 5 864
cert_cover_2 5 5 4 7 8 352 864 3
cert_coveringFacets
cert_coveringProof_6
cert_certificate 4 6
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1335

end
end BundlePart26

section BundlePart27
/- Source: ProjectionCertificates/R_one_six_1336.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1336

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 519, 91, 835, 181, 901, 465, 590, 684, 120, 872, 368, 944, 7, 27, 67, 515, 53, 133, 517, 81, 145, 321, 385, 769, 14, 518, 74, 578, 44, 524, 164, 644, 56, 88, 104, 552, 584, 112, 176, 304, 336, 400, 352, 672, 800, 832, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_519, vertices_91, vertices_835, vertices_181, vertices_901, vertices_465, vertices_590, vertices_684, vertices_120, vertices_872, vertices_368, vertices_944] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_27, vertices_67, vertices_515, vertices_53, vertices_133, vertices_517, vertices_81, vertices_145, vertices_321, vertices_385, vertices_769, vertices_14, vertices_518, vertices_74, vertices_578, vertices_44, vertices_524, vertices_164, vertices_644, vertices_56, vertices_88, vertices_104, vertices_552, vertices_584, vertices_112, vertices_176, vertices_304, vertices_336, vertices_400, vertices_352, vertices_672, vertices_800, vertices_832, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_519), (false, vertices_91), (false, vertices_835), (false, vertices_181), (false, vertices_901), (false, vertices_465), (true, vertices_524), (true, vertices_104), (true, vertices_552), (true, vertices_584), (true, vertices_112), (true, vertices_304), (true, vertices_352), (true, vertices_672), (true, vertices_800)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 10 13 17 18 20 21 22 23 24
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 14 else
  if p.val = (false, vertices_519) then 0 else
  if p.val = (false, vertices_91) then 11 else
  if p.val = (false, vertices_835) then 12 else
  if p.val = (false, vertices_181) then 15 else
  if p.val = (false, vertices_901) then 16 else
  if p.val = (false, vertices_465) then 19 else
  if p.val = (true, vertices_524) then 1 else
  if p.val = (true, vertices_104) then 2 else
  if p.val = (true, vertices_552) then 3 else
  if p.val = (true, vertices_584) then 4 else
  if p.val = (true, vertices_112) then 5 else
  if p.val = (true, vertices_304) then 6 else
  if p.val = (true, vertices_352) then 7 else
  if p.val = (true, vertices_672) then 8 else
  if p.val = (true, vertices_800) then 9 else
  0
cert_priority
cert_nodeAtPriority_41 1 519 0 524 104 552 584 112 304 352 672 800 91 835 181 901 465
cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 2 5 8 590 14 3
cert_row_4 1 1 2 4 6 8 684 44 3
cert_row_4 2 2 4 5 7 8 872 104 3
cert_row_4 3 3 4 6 7 8 944 176 3
cert_rows
cert_pivot_2 0 1 2 3
cert_heightProof 4
cert_coverFacet 0 590
cert_cover_5 0 0 0 1 2 5 14 590 3
cert_coverFacet 1 684
cert_cover_5 1 1 1 2 4 6 44 684 3
cert_coverFacet 2 120
cert_cover_2 2 3 2 4 5 56 120 3
cert_coverFacet 3 872
cert_cover_5 3 2 2 4 5 7 104 872 3
cert_coverFacet 4 368
cert_cover_2 4 4 3 5 7 112 368 3
cert_coverFacet 5 944
cert_cover_5 5 3 3 4 6 7 176 944 3
cert_coveringFacets
cert_coveringProof_6
cert_certificate 4 6
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1336

end
end BundlePart27

section BundlePart28
/- Source: ProjectionCertificates/R_one_six_1337.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1337

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 519, 91, 835, 181, 901, 465, 590, 684, 312, 344, 872, 944, 7, 27, 67, 515, 53, 133, 517, 81, 145, 321, 385, 769, 14, 518, 74, 578, 44, 524, 164, 644, 56, 88, 280, 296, 552, 328, 584, 176, 304, 336, 400, 672, 800, 832, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_519, vertices_91, vertices_835, vertices_181, vertices_901, vertices_465, vertices_590, vertices_684, vertices_312, vertices_344, vertices_872, vertices_944] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_27, vertices_67, vertices_515, vertices_53, vertices_133, vertices_517, vertices_81, vertices_145, vertices_321, vertices_385, vertices_769, vertices_14, vertices_518, vertices_74, vertices_578, vertices_44, vertices_524, vertices_164, vertices_644, vertices_56, vertices_88, vertices_280, vertices_296, vertices_552, vertices_328, vertices_584, vertices_176, vertices_304, vertices_336, vertices_400, vertices_672, vertices_800, vertices_832, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_519), (false, vertices_91), (false, vertices_835), (false, vertices_181), (false, vertices_901), (false, vertices_465), (true, vertices_524), (true, vertices_280), (true, vertices_296), (true, vertices_552), (true, vertices_328), (true, vertices_584), (true, vertices_304), (true, vertices_672), (true, vertices_800)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 10 13 17 18 20 21 22 23 24
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 14 else
  if p.val = (false, vertices_519) then 0 else
  if p.val = (false, vertices_91) then 11 else
  if p.val = (false, vertices_835) then 12 else
  if p.val = (false, vertices_181) then 15 else
  if p.val = (false, vertices_901) then 16 else
  if p.val = (false, vertices_465) then 19 else
  if p.val = (true, vertices_524) then 1 else
  if p.val = (true, vertices_280) then 2 else
  if p.val = (true, vertices_296) then 3 else
  if p.val = (true, vertices_552) then 4 else
  if p.val = (true, vertices_328) then 5 else
  if p.val = (true, vertices_584) then 6 else
  if p.val = (true, vertices_304) then 7 else
  if p.val = (true, vertices_672) then 8 else
  if p.val = (true, vertices_800) then 9 else
  0
cert_priority
cert_nodeAtPriority_41 1 519 0 524 280 296 552 328 584 304 672 800 91 835 181 901 465
cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 2 5 8 590 14 3
cert_row_4 1 1 2 4 6 8 684 44 3
cert_row_4 2 2 4 5 7 8 872 296 2
cert_row_4 3 3 4 6 7 8 944 176 3
cert_rows
cert_pivot_2 0 1 2 3
cert_heightProof 4
cert_coverFacet 0 590
cert_cover_5 0 0 0 1 2 5 14 590 3
cert_coverFacet 1 684
cert_cover_5 1 1 1 2 4 6 44 684 3
cert_coverFacet 2 312
cert_cover_2 2 3 2 4 7 56 312 3
cert_coverFacet 3 344
cert_cover_2 3 3 2 5 7 88 344 3
cert_coverFacet 4 872
cert_cover_5 4 2 2 4 5 7 296 872 2
cert_coverFacet 5 944
cert_cover_5 5 3 3 4 6 7 176 944 3
cert_coveringFacets
cert_coveringProof_6
cert_certificate 4 6
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1337

end
end BundlePart28

section BundlePart29
/- Source: ProjectionCertificates/R_one_six_1338.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1338

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 647, 91, 835, 181, 465, 897, 590, 812, 676, 376, 840, 944, 7, 27, 67, 515, 53, 133, 81, 145, 321, 385, 641, 769, 14, 518, 74, 578, 44, 524, 164, 548, 644, 56, 88, 296, 328, 584, 776, 176, 304, 336, 400, 672, 800, 832, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_647, vertices_91, vertices_835, vertices_181, vertices_465, vertices_897, vertices_590, vertices_812, vertices_676, vertices_376, vertices_840, vertices_944] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_27, vertices_67, vertices_515, vertices_53, vertices_133, vertices_81, vertices_145, vertices_321, vertices_385, vertices_641, vertices_769, vertices_14, vertices_518, vertices_74, vertices_578, vertices_44, vertices_524, vertices_164, vertices_548, vertices_644, vertices_56, vertices_88, vertices_296, vertices_328, vertices_584, vertices_776, vertices_176, vertices_304, vertices_336, vertices_400, vertices_672, vertices_800, vertices_832, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_647), (false, vertices_91), (false, vertices_835), (false, vertices_181), (false, vertices_465), (false, vertices_897), (true, vertices_524), (true, vertices_548), (true, vertices_296), (true, vertices_328), (true, vertices_584), (true, vertices_776), (true, vertices_304), (true, vertices_672), (true, vertices_800)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 13 10 17 18 20 21 22 23 24
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 14 else
  if p.val = (false, vertices_647) then 11 else
  if p.val = (false, vertices_91) then 15 else
  if p.val = (false, vertices_835) then 16 else
  if p.val = (false, vertices_181) then 12 else
  if p.val = (false, vertices_465) then 19 else
  if p.val = (false, vertices_897) then 0 else
  if p.val = (true, vertices_524) then 1 else
  if p.val = (true, vertices_548) then 2 else
  if p.val = (true, vertices_296) then 3 else
  if p.val = (true, vertices_328) then 4 else
  if p.val = (true, vertices_584) then 5 else
  if p.val = (true, vertices_776) then 6 else
  if p.val = (true, vertices_304) then 7 else
  if p.val = (true, vertices_672) then 8 else
  if p.val = (true, vertices_800) then 9 else
  0
cert_priority
cert_nodeAtPriority_41 0 897 1 524 548 296 328 584 776 304 672 800 647 181 91 835 465
cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 2 5 8 590 14 3
cert_row_4 1 1 2 4 7 8 812 44 3
cert_row_4 2 2 3 4 5 7 376 56 3
cert_row_4 3 3 4 6 7 8 944 176 3
cert_rows
cert_pivot_2 0 1 2 3
cert_heightProof 4
cert_coverFacet 0 590
cert_cover_5 0 0 0 1 2 5 14 590 3
cert_coverFacet 1 812
cert_cover_5 1 1 1 2 4 7 44 812 3
cert_coverFacet 2 676
cert_cover_2 2 4 1 6 8 164 676 3
cert_coverFacet 3 376
cert_cover_5 3 2 2 3 4 5 56 376 3
cert_coverFacet 4 840
cert_cover_2 4 5 2 7 8 328 840 3
cert_coverFacet 5 944
cert_cover_5 5 3 3 4 6 7 176 944 3
cert_coveringFacets
cert_coveringProof_6
cert_certificate 4 6
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1338

end
end BundlePart29

-- Public target certificates; internal witness data stays private.
namespace Nonrational.TerminalVerification
open Papers.RationalityTen.ChirotopeDensity.FiniteProjection
open Nonrational.TerminalData
set_option maxRecDepth 100000
set_option maxHeartbeats 0

public theorem projection_1500 : Certifies 1500 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1305.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1501 : Certifies 1501 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1306.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1502 : Certifies 1502 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1307.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1503 : Certifies 1503 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1308.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1504 : Certifies 1504 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1309.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1505 : Certifies 1505 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1310.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1506 : Certifies 1506 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1311.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1507 : Certifies 1507 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1312.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1508 : Certifies 1508 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1313.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1509 : Certifies 1509 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1314.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1510 : Certifies 1510 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1315.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1511 : Certifies 1511 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1316.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1512 : Certifies 1512 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1317.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1513 : Certifies 1513 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1318.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1514 : Certifies 1514 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1319.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1515 : Certifies 1515 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1324.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1516 : Certifies 1516 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1325.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1517 : Certifies 1517 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1326.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1518 : Certifies 1518 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1327.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1519 : Certifies 1519 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1328.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1520 : Certifies 1520 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1329.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1521 : Certifies 1521 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1330.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1522 : Certifies 1522 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1331.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1523 : Certifies 1523 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1332.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1524 : Certifies 1524 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1333.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1525 : Certifies 1525 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1334.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1526 : Certifies 1526 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1335.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1527 : Certifies 1527 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1336.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1528 : Certifies 1528 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1337.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1529 : Certifies 1529 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1338.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem certified_B050 (j : Fin 30) :
    Certifies (1500 + j.val) := by
  fin_cases j
  · exact projection_1500
  · exact projection_1501
  · exact projection_1502
  · exact projection_1503
  · exact projection_1504
  · exact projection_1505
  · exact projection_1506
  · exact projection_1507
  · exact projection_1508
  · exact projection_1509
  · exact projection_1510
  · exact projection_1511
  · exact projection_1512
  · exact projection_1513
  · exact projection_1514
  · exact projection_1515
  · exact projection_1516
  · exact projection_1517
  · exact projection_1518
  · exact projection_1519
  · exact projection_1520
  · exact projection_1521
  · exact projection_1522
  · exact projection_1523
  · exact projection_1524
  · exact projection_1525
  · exact projection_1526
  · exact projection_1527
  · exact projection_1528
  · exact projection_1529

end Nonrational.TerminalVerification
-- Explicit facial frame witnesses, with lexical vector tracking.
