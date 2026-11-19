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
/- Source: ProjectionCertificates/R_m16e10q1_0711.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0711

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [271, 551, 523, 421, 409, 649, 737, 790, 714, 330, 850, 628, 308, 248, 344, 432, 7, 11, 515, 37, 261, 137, 265, 521, 161, 545, 385, 641, 262, 518, 74, 266, 522, 786, 322, 578, 52, 276, 532, 292, 548, 88, 152, 280, 200, 328, 648, 112, 176, 304, 336, 592, 400, 224, 608, 416, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_271, vertices_551, vertices_523, vertices_421, vertices_409, vertices_649, vertices_737, vertices_790, vertices_714, vertices_330, vertices_850, vertices_628, vertices_308, vertices_248, vertices_344, vertices_432] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_515, vertices_37, vertices_261, vertices_137, vertices_265, vertices_521, vertices_161, vertices_545, vertices_385, vertices_641, vertices_262, vertices_518, vertices_74, vertices_266, vertices_522, vertices_786, vertices_322, vertices_578, vertices_52, vertices_276, vertices_532, vertices_292, vertices_548, vertices_88, vertices_152, vertices_280, vertices_200, vertices_328, vertices_648, vertices_112, vertices_176, vertices_304, vertices_336, vertices_592, vertices_400, vertices_224, vertices_608, vertices_416, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_271), (false, vertices_551), (false, vertices_523), (false, vertices_421), (false, vertices_409), (false, vertices_649), (false, vertices_737), (true, vertices_74), (true, vertices_786), (true, vertices_322), (true, vertices_578), (true, vertices_52), (true, vertices_276), (true, vertices_532), (true, vertices_88), (true, vertices_200), (true, vertices_328), (true, vertices_112), (true, vertices_176), (true, vertices_304), (true, vertices_336), (true, vertices_592)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 16 20 22 24 25 27 28 29 30
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_271) then 17 else
  if p.val = (false, vertices_551) then 18 else
  if p.val = (false, vertices_523) then 0 else
  if p.val = (false, vertices_421) then 21 else
  if p.val = (false, vertices_409) then 23 else
  if p.val = (false, vertices_649) then 1 else
  if p.val = (false, vertices_737) then 26 else
  if p.val = (true, vertices_74) then 2 else
  if p.val = (true, vertices_786) then 19 else
  if p.val = (true, vertices_322) then 3 else
  if p.val = (true, vertices_578) then 4 else
  if p.val = (true, vertices_52) then 5 else
  if p.val = (true, vertices_276) then 6 else
  if p.val = (true, vertices_532) then 7 else
  if p.val = (true, vertices_88) then 8 else
  if p.val = (true, vertices_200) then 9 else
  if p.val = (true, vertices_328) then 10 else
  if p.val = (true, vertices_112) then 11 else
  if p.val = (true, vertices_176) then 12 else
  if p.val = (true, vertices_304) then 13 else
  if p.val = (true, vertices_336) then 14 else
  if p.val = (true, vertices_592) then 15 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_523), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_649), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_74), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_322), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_578), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_52), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_276), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_532), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_88), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_200), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_328), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_112), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_176), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_304), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_336), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_592), by decide +kernel⟩
  | 16 => Sum.inl 0
  | 17 => Sum.inr ⟨(false, vertices_271), by decide +kernel⟩
  | 18 => Sum.inr ⟨(false, vertices_551), by decide +kernel⟩
  | 19 => Sum.inr ⟨(true, vertices_786), by decide +kernel⟩
  | 20 => Sum.inl 1
  | 21 => Sum.inr ⟨(false, vertices_421), by decide +kernel⟩
  | 22 => Sum.inl 2
  | 23 => Sum.inr ⟨(false, vertices_409), by decide +kernel⟩
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
cert_row_2 0 0 3 7 8 786
cert_row_4 1 0 2 5 6 8 714 74 3
cert_row_4 2 1 3 4 5 8 628 52 3
cert_row_4 3 2 3 4 5 6 248 88 2
cert_rows
cert_pivot_2 7 0 1 2
cert_heightProof 4
cert_coverFacet 0 790
cert_cover_5 0 0 0 1 3 7 262 790 2
cert_coverFacet 1 714
cert_cover_5 1 1 0 2 5 6 74 714 3
cert_coverFacet 2 330
cert_cover_2 2 2 0 5 7 74 330 3
cert_coverFacet 3 850
cert_cover_5 3 0 0 3 5 7 786 850 2
cert_coverFacet 4 628
cert_cover_5 4 2 1 3 4 5 52 628 3
cert_coverFacet 5 308
cert_cover_2 5 3 1 4 7 52 308 3
cert_coverFacet 6 248
cert_cover_5 6 3 2 3 4 5 88 248 2
cert_coverFacet 7 344
cert_cover_2 7 3 2 5 7 88 344 3
cert_coverFacet 8 432
cert_cover_2 8 4 3 6 7 176 432 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0711

end
end BundlePart0

section BundlePart1
/- Source: ProjectionCertificates/R_m16e10q1_0712.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0712

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [299, 339, 99, 613, 601, 409, 553, 230, 418, 962, 188, 572, 916, 708, 424, 848, 35, 67, 259, 25, 41, 265, 521, 81, 273, 97, 545, 577, 98, 162, 290, 194, 322, 386, 60, 148, 532, 100, 164, 548, 196, 580, 644, 152, 536, 168, 296, 552, 392, 336, 592, 400, 784, 416, 704, 832, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_299, vertices_339, vertices_99, vertices_613, vertices_601, vertices_409, vertices_553, vertices_230, vertices_418, vertices_962, vertices_188, vertices_572, vertices_916, vertices_708, vertices_424, vertices_848] (by decide +kernel)
  polygons := literalFinset [vertices_35, vertices_67, vertices_259, vertices_25, vertices_41, vertices_265, vertices_521, vertices_81, vertices_273, vertices_97, vertices_545, vertices_577, vertices_98, vertices_162, vertices_290, vertices_194, vertices_322, vertices_386, vertices_60, vertices_148, vertices_532, vertices_100, vertices_164, vertices_548, vertices_196, vertices_580, vertices_644, vertices_152, vertices_536, vertices_168, vertices_296, vertices_552, vertices_392, vertices_336, vertices_592, vertices_400, vertices_784, vertices_416, vertices_704, vertices_832, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_299), (false, vertices_339), (false, vertices_99), (false, vertices_613), (false, vertices_601), (false, vertices_409), (false, vertices_553), (true, vertices_162), (true, vertices_194), (true, vertices_386), (true, vertices_60), (true, vertices_148), (true, vertices_532), (true, vertices_164), (true, vertices_196), (true, vertices_644), (true, vertices_168), (true, vertices_784), (true, vertices_416), (true, vertices_704), (true, vertices_832), (true, vertices_896)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 16 19 22 25 26 27 28 29 30
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_299) then 17 else
  if p.val = (false, vertices_339) then 18 else
  if p.val = (false, vertices_99) then 0 else
  if p.val = (false, vertices_613) then 20 else
  if p.val = (false, vertices_601) then 23 else
  if p.val = (false, vertices_409) then 24 else
  if p.val = (false, vertices_553) then 1 else
  if p.val = (true, vertices_162) then 2 else
  if p.val = (true, vertices_194) then 3 else
  if p.val = (true, vertices_386) then 4 else
  if p.val = (true, vertices_60) then 21 else
  if p.val = (true, vertices_148) then 5 else
  if p.val = (true, vertices_532) then 6 else
  if p.val = (true, vertices_164) then 7 else
  if p.val = (true, vertices_196) then 8 else
  if p.val = (true, vertices_644) then 9 else
  if p.val = (true, vertices_168) then 10 else
  if p.val = (true, vertices_784) then 11 else
  if p.val = (true, vertices_416) then 12 else
  if p.val = (true, vertices_704) then 13 else
  if p.val = (true, vertices_832) then 14 else
  if p.val = (true, vertices_896) then 15 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_99), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_553), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_162), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_194), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_386), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_148), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_532), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_164), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_196), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_644), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_168), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_784), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_416), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_704), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_832), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_896), by decide +kernel⟩
  | 16 => Sum.inl 0
  | 17 => Sum.inr ⟨(false, vertices_299), by decide +kernel⟩
  | 18 => Sum.inr ⟨(false, vertices_339), by decide +kernel⟩
  | 19 => Sum.inl 1
  | 20 => Sum.inr ⟨(false, vertices_613), by decide +kernel⟩
  | 21 => Sum.inr ⟨(true, vertices_60), by decide +kernel⟩
  | 22 => Sum.inl 2
  | 23 => Sum.inr ⟨(false, vertices_601), by decide +kernel⟩
  | 24 => Sum.inr ⟨(false, vertices_409), by decide +kernel⟩
  | 25 => Sum.inl 3
  | 26 => Sum.inl 4
  | 27 => Sum.inl 5
  | 28 => Sum.inl 6
  | 29 => Sum.inl 7
  | 30 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 1 2 3 4 60
cert_row_4 1 0 1 4 5 6 230 98 1
cert_row_4 2 0 5 6 7 8 962 194 3
cert_row_4 3 1 3 6 7 8 916 148 3
cert_rows
cert_pivot_2 2 4 0 1
cert_heightProof 4
cert_coverFacet 0 230
cert_cover_5 0 1 0 1 4 5 98 230 1
cert_coverFacet 1 418
cert_cover_2 1 4 0 6 7 162 418 3
cert_coverFacet 2 962
cert_cover_5 2 2 0 5 6 7 194 962 3
cert_coverFacet 3 188
cert_cover_5 3 0 1 2 3 6 60 188 3
cert_coverFacet 4 572
cert_cover_5 4 0 1 2 3 8 60 572 3
cert_coverFacet 5 916
cert_cover_5 5 3 1 3 6 7 148 916 3
cert_coverFacet 6 708
cert_cover_2 6 5 1 6 8 196 708 3
cert_coverFacet 7 424
cert_cover_2 7 4 2 6 7 168 424 3
cert_coverFacet 8 848
cert_cover_2 8 5 3 7 8 336 848 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0712

end
end BundlePart1

section BundlePart2
/- Source: ProjectionCertificates/R_m16e10q1_0713.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0713

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [307, 563, 835, 205, 617, 425, 449, 662, 410, 898, 60, 156, 108, 628, 964, 312, 51, 259, 515, 41, 73, 137, 289, 545, 193, 321, 577, 385, 146, 274, 530, 386, 642, 770, 28, 44, 76, 140, 52, 148, 532, 100, 196, 580, 644, 56, 152, 280, 104, 296, 392, 304, 560, 608, 448, 832, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_307, vertices_563, vertices_835, vertices_205, vertices_617, vertices_425, vertices_449, vertices_662, vertices_410, vertices_898, vertices_60, vertices_156, vertices_108, vertices_628, vertices_964, vertices_312] (by decide +kernel)
  polygons := literalFinset [vertices_51, vertices_259, vertices_515, vertices_41, vertices_73, vertices_137, vertices_289, vertices_545, vertices_193, vertices_321, vertices_577, vertices_385, vertices_146, vertices_274, vertices_530, vertices_386, vertices_642, vertices_770, vertices_28, vertices_44, vertices_76, vertices_140, vertices_52, vertices_148, vertices_532, vertices_100, vertices_196, vertices_580, vertices_644, vertices_56, vertices_152, vertices_280, vertices_104, vertices_296, vertices_392, vertices_304, vertices_560, vertices_608, vertices_448, vertices_832, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_307), (false, vertices_563), (false, vertices_835), (false, vertices_205), (false, vertices_617), (false, vertices_425), (false, vertices_449), (true, vertices_146), (true, vertices_386), (true, vertices_642), (true, vertices_28), (true, vertices_44), (true, vertices_52), (true, vertices_148), (true, vertices_532), (true, vertices_100), (true, vertices_580), (true, vertices_644), (true, vertices_56), (true, vertices_152), (true, vertices_280), (true, vertices_896)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 16 20 22 25 26 27 28 29 30
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_307) then 17 else
  if p.val = (false, vertices_563) then 18 else
  if p.val = (false, vertices_835) then 19 else
  if p.val = (false, vertices_205) then 21 else
  if p.val = (false, vertices_617) then 23 else
  if p.val = (false, vertices_425) then 24 else
  if p.val = (false, vertices_449) then 0 else
  if p.val = (true, vertices_146) then 1 else
  if p.val = (true, vertices_386) then 2 else
  if p.val = (true, vertices_642) then 3 else
  if p.val = (true, vertices_28) then 4 else
  if p.val = (true, vertices_44) then 5 else
  if p.val = (true, vertices_52) then 6 else
  if p.val = (true, vertices_148) then 7 else
  if p.val = (true, vertices_532) then 8 else
  if p.val = (true, vertices_100) then 9 else
  if p.val = (true, vertices_580) then 10 else
  if p.val = (true, vertices_644) then 11 else
  if p.val = (true, vertices_56) then 12 else
  if p.val = (true, vertices_152) then 13 else
  if p.val = (true, vertices_280) then 14 else
  if p.val = (true, vertices_896) then 15 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_449), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_146), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_386), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_642), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_28), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_44), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_52), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_148), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_532), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_100), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_580), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_644), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_56), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_152), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_280), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_896), by decide +kernel⟩
  | 16 => Sum.inl 0
  | 17 => Sum.inr ⟨(false, vertices_307), by decide +kernel⟩
  | 18 => Sum.inr ⟨(false, vertices_563), by decide +kernel⟩
  | 19 => Sum.inr ⟨(false, vertices_835), by decide +kernel⟩
  | 20 => Sum.inl 1
  | 21 => Sum.inr ⟨(false, vertices_205), by decide +kernel⟩
  | 22 => Sum.inl 2
  | 23 => Sum.inr ⟨(false, vertices_617), by decide +kernel⟩
  | 24 => Sum.inr ⟨(false, vertices_425), by decide +kernel⟩
  | 25 => Sum.inl 3
  | 26 => Sum.inl 4
  | 27 => Sum.inl 5
  | 28 => Sum.inl 6
  | 29 => Sum.inl 7
  | 30 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 2 3 6 7 410 146 1
cert_row_4 1 0 1 3 6 8 662 146 1
cert_row_4 2 1 3 4 5 8 628 52 3
cert_row_4 3 1 5 6 7 8 964 196 3
cert_rows
cert_pivot_2 2 0 3 1
cert_heightProof 4
cert_coverFacet 0 662
cert_cover_5 0 1 0 1 3 6 146 662 1
cert_coverFacet 1 410
cert_cover_5 1 0 0 2 3 6 146 410 1
cert_coverFacet 2 898
cert_cover_2 2 6 0 7 8 386 898 3
cert_coverFacet 3 60
cert_cover_2 3 2 1 3 4 28 60 3
cert_coverFacet 4 156
cert_cover_2 4 2 1 3 6 28 156 3
cert_coverFacet 5 108
cert_cover_2 5 2 1 4 5 44 108 3
cert_coverFacet 6 628
cert_cover_5 6 2 1 3 4 5 52 628 3
cert_coverFacet 7 964
cert_cover_5 7 3 1 5 6 7 196 964 3
cert_coverFacet 8 312
cert_cover_2 8 3 2 4 7 56 312 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0713

end
end BundlePart2

section BundlePart3
/- Source: ProjectionCertificates/R_m16e10q1_0714.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0714

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [775, 557, 229, 389, 601, 105, 961, 182, 566, 390, 410, 850, 184, 568, 344, 488, 37, 133, 261, 517, 41, 73, 521, 97, 193, 577, 385, 769, 54, 134, 262, 518, 146, 274, 530, 386, 770, 164, 548, 388, 56, 88, 152, 280, 536, 104, 168, 552, 328, 392, 176, 560, 336, 592, 224, 448, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_775, vertices_557, vertices_229, vertices_389, vertices_601, vertices_105, vertices_961, vertices_182, vertices_566, vertices_390, vertices_410, vertices_850, vertices_184, vertices_568, vertices_344, vertices_488] (by decide +kernel)
  polygons := literalFinset [vertices_37, vertices_133, vertices_261, vertices_517, vertices_41, vertices_73, vertices_521, vertices_97, vertices_193, vertices_577, vertices_385, vertices_769, vertices_54, vertices_134, vertices_262, vertices_518, vertices_146, vertices_274, vertices_530, vertices_386, vertices_770, vertices_164, vertices_548, vertices_388, vertices_56, vertices_88, vertices_152, vertices_280, vertices_536, vertices_104, vertices_168, vertices_552, vertices_328, vertices_392, vertices_176, vertices_560, vertices_336, vertices_592, vertices_224, vertices_448, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_775), (false, vertices_557), (false, vertices_229), (false, vertices_389), (false, vertices_601), (false, vertices_105), (false, vertices_961), (true, vertices_54), (true, vertices_134), (true, vertices_146), (true, vertices_274), (true, vertices_530), (true, vertices_386), (true, vertices_56), (true, vertices_152), (true, vertices_280), (true, vertices_168), (true, vertices_328), (true, vertices_392), (true, vertices_176), (true, vertices_560), (true, vertices_336)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 16 19 22 24 25 26 28 29 30
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_775) then 17 else
  if p.val = (false, vertices_557) then 20 else
  if p.val = (false, vertices_229) then 21 else
  if p.val = (false, vertices_389) then 0 else
  if p.val = (false, vertices_601) then 23 else
  if p.val = (false, vertices_105) then 1 else
  if p.val = (false, vertices_961) then 27 else
  if p.val = (true, vertices_54) then 18 else
  if p.val = (true, vertices_134) then 2 else
  if p.val = (true, vertices_146) then 3 else
  if p.val = (true, vertices_274) then 4 else
  if p.val = (true, vertices_530) then 5 else
  if p.val = (true, vertices_386) then 6 else
  if p.val = (true, vertices_56) then 7 else
  if p.val = (true, vertices_152) then 8 else
  if p.val = (true, vertices_280) then 9 else
  if p.val = (true, vertices_168) then 10 else
  if p.val = (true, vertices_328) then 11 else
  if p.val = (true, vertices_392) then 12 else
  if p.val = (true, vertices_176) then 13 else
  if p.val = (true, vertices_560) then 14 else
  if p.val = (true, vertices_336) then 15 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_389), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_105), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_134), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_146), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_274), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_530), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_386), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_56), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_152), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_280), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_168), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_328), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_392), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_176), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_560), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_336), by decide +kernel⟩
  | 16 => Sum.inl 0
  | 17 => Sum.inr ⟨(false, vertices_775), by decide +kernel⟩
  | 18 => Sum.inr ⟨(true, vertices_54), by decide +kernel⟩
  | 19 => Sum.inl 1
  | 20 => Sum.inr ⟨(false, vertices_557), by decide +kernel⟩
  | 21 => Sum.inr ⟨(false, vertices_229), by decide +kernel⟩
  | 22 => Sum.inl 2
  | 23 => Sum.inr ⟨(false, vertices_601), by decide +kernel⟩
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
cert_row_2 0 0 1 3 4 54
cert_row_4 1 0 3 5 7 8 850 274 2
cert_row_4 2 0 2 3 6 7 410 146 1
cert_row_4 3 2 4 5 6 7 488 104 3
cert_rows
cert_pivot_2 1 8 0 2
cert_heightProof 4
cert_coverFacet 0 182
cert_cover_5 0 0 0 1 3 6 54 182 3
cert_coverFacet 1 566
cert_cover_5 1 0 0 1 3 8 54 566 3
cert_coverFacet 2 390
cert_cover_2 2 1 0 6 7 134 390 3
cert_coverFacet 3 410
cert_cover_5 3 2 0 2 3 6 146 410 1
cert_coverFacet 4 850
cert_cover_5 4 1 0 3 5 7 274 850 2
cert_coverFacet 5 184
cert_cover_2 5 3 2 4 6 56 184 3
cert_coverFacet 6 568
cert_cover_2 6 3 2 4 8 56 568 3
cert_coverFacet 7 344
cert_cover_2 7 3 2 5 7 88 344 3
cert_coverFacet 8 488
cert_cover_5 8 3 2 4 5 6 104 488 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0714

end
end BundlePart3

section BundlePart4
/- Source: ProjectionCertificates/R_m16e10q1_0715.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0715

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [775, 285, 149, 709, 217, 617, 777, 406, 678, 362, 554, 778, 434, 344, 752, 368, 21, 133, 261, 517, 25, 73, 265, 521, 145, 193, 577, 769, 134, 262, 518, 42, 266, 522, 402, 162, 290, 546, 770, 148, 276, 644, 88, 280, 104, 552, 328, 776, 112, 176, 304, 208, 336, 352, 608, 672, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_775, vertices_285, vertices_149, vertices_709, vertices_217, vertices_617, vertices_777, vertices_406, vertices_678, vertices_362, vertices_554, vertices_778, vertices_434, vertices_344, vertices_752, vertices_368] (by decide +kernel)
  polygons := literalFinset [vertices_21, vertices_133, vertices_261, vertices_517, vertices_25, vertices_73, vertices_265, vertices_521, vertices_145, vertices_193, vertices_577, vertices_769, vertices_134, vertices_262, vertices_518, vertices_42, vertices_266, vertices_522, vertices_402, vertices_162, vertices_290, vertices_546, vertices_770, vertices_148, vertices_276, vertices_644, vertices_88, vertices_280, vertices_104, vertices_552, vertices_328, vertices_776, vertices_112, vertices_176, vertices_304, vertices_208, vertices_336, vertices_352, vertices_608, vertices_672, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_775), (false, vertices_285), (false, vertices_149), (false, vertices_709), (false, vertices_217), (false, vertices_617), (false, vertices_777), (true, vertices_134), (true, vertices_42), (true, vertices_266), (true, vertices_522), (true, vertices_402), (true, vertices_162), (true, vertices_290), (true, vertices_546), (true, vertices_328), (true, vertices_112), (true, vertices_176), (true, vertices_304), (true, vertices_336), (true, vertices_352), (true, vertices_672)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 16 19 22 25 26 27 28 29 30
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_775) then 17 else
  if p.val = (false, vertices_285) then 20 else
  if p.val = (false, vertices_149) then 0 else
  if p.val = (false, vertices_709) then 21 else
  if p.val = (false, vertices_217) then 23 else
  if p.val = (false, vertices_617) then 24 else
  if p.val = (false, vertices_777) then 1 else
  if p.val = (true, vertices_134) then 2 else
  if p.val = (true, vertices_42) then 3 else
  if p.val = (true, vertices_266) then 4 else
  if p.val = (true, vertices_522) then 5 else
  if p.val = (true, vertices_402) then 18 else
  if p.val = (true, vertices_162) then 6 else
  if p.val = (true, vertices_290) then 7 else
  if p.val = (true, vertices_546) then 8 else
  if p.val = (true, vertices_328) then 9 else
  if p.val = (true, vertices_112) then 10 else
  if p.val = (true, vertices_176) then 11 else
  if p.val = (true, vertices_304) then 12 else
  if p.val = (true, vertices_336) then 13 else
  if p.val = (true, vertices_352) then 14 else
  if p.val = (true, vertices_672) then 15 else
  0
cert_priority
cert_nodeAtPriority_39 0 149 1 777 134 42 266 522 162 290 546 328 112 176 304 336 352 672 775 402 285 709 217 617
cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 4 6 8 678 134 2
cert_row_4 1 0 2 4 5 7 362 42 3
cert_row_2 2 0 3 6 7 402
cert_row_4 3 3 4 5 6 8 752 112 3
cert_rows
cert_pivot_2 1 2 0 3
cert_heightProof 4
cert_coverFacet 0 406
cert_cover_5 0 2 0 1 3 6 134 406 2
cert_coverFacet 1 678
cert_cover_5 1 0 0 1 4 6 134 678 2
cert_coverFacet 2 362
cert_cover_5 2 1 0 2 4 5 42 362 3
cert_coverFacet 3 554
cert_cover_2 3 2 0 4 8 42 554 3
cert_coverFacet 4 778
cert_cover_2 4 2 0 7 8 266 778 3
cert_coverFacet 5 434
cert_cover_5 5 2 0 3 4 6 402 434 2
cert_coverFacet 6 344
cert_cover_2 6 3 2 5 7 88 344 3
cert_coverFacet 7 752
cert_cover_5 7 3 3 4 5 6 112 752 3
cert_coverFacet 8 368
cert_cover_2 8 4 3 5 7 112 368 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0715

end
end BundlePart4

section BundlePart5
/- Source: ProjectionCertificates/R_m16e10q1_0716.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0716

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [527, 141, 565, 213, 905, 113, 737, 286, 534, 778, 370, 562, 930, 348, 204, 488, 13, 21, 133, 517, 137, 521, 49, 81, 97, 545, 193, 641, 14, 22, 518, 266, 522, 50, 274, 530, 290, 546, 770, 284, 76, 140, 84, 532, 196, 200, 328, 392, 776, 112, 560, 336, 224, 352, 416, 672, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_527, vertices_141, vertices_565, vertices_213, vertices_905, vertices_113, vertices_737, vertices_286, vertices_534, vertices_778, vertices_370, vertices_562, vertices_930, vertices_348, vertices_204, vertices_488] (by decide +kernel)
  polygons := literalFinset [vertices_13, vertices_21, vertices_133, vertices_517, vertices_137, vertices_521, vertices_49, vertices_81, vertices_97, vertices_545, vertices_193, vertices_641, vertices_14, vertices_22, vertices_518, vertices_266, vertices_522, vertices_50, vertices_274, vertices_530, vertices_290, vertices_546, vertices_770, vertices_284, vertices_76, vertices_140, vertices_84, vertices_532, vertices_196, vertices_200, vertices_328, vertices_392, vertices_776, vertices_112, vertices_560, vertices_336, vertices_224, vertices_352, vertices_416, vertices_672, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_527), (false, vertices_141), (false, vertices_565), (false, vertices_213), (false, vertices_905), (false, vertices_113), (false, vertices_737), (true, vertices_22), (true, vertices_266), (true, vertices_50), (true, vertices_274), (true, vertices_530), (true, vertices_290), (true, vertices_546), (true, vertices_770), (true, vertices_284), (true, vertices_76), (true, vertices_200), (true, vertices_328), (true, vertices_336), (true, vertices_352), (true, vertices_416)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 16 21 18 24 25 27 28 29 30
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_527) then 17 else
  if p.val = (false, vertices_141) then 0 else
  if p.val = (false, vertices_565) then 22 else
  if p.val = (false, vertices_213) then 23 else
  if p.val = (false, vertices_905) then 19 else
  if p.val = (false, vertices_113) then 1 else
  if p.val = (false, vertices_737) then 26 else
  if p.val = (true, vertices_22) then 2 else
  if p.val = (true, vertices_266) then 3 else
  if p.val = (true, vertices_50) then 4 else
  if p.val = (true, vertices_274) then 5 else
  if p.val = (true, vertices_530) then 6 else
  if p.val = (true, vertices_290) then 7 else
  if p.val = (true, vertices_546) then 8 else
  if p.val = (true, vertices_770) then 9 else
  if p.val = (true, vertices_284) then 20 else
  if p.val = (true, vertices_76) then 10 else
  if p.val = (true, vertices_200) then 11 else
  if p.val = (true, vertices_328) then 12 else
  if p.val = (true, vertices_336) then 13 else
  if p.val = (true, vertices_352) then 14 else
  if p.val = (true, vertices_416) then 15 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_141), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_113), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_22), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_266), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_50), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_274), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_530), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_290), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_546), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_770), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_76), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_200), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_328), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_336), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_352), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_416), by decide +kernel⟩
  | 16 => Sum.inl 0
  | 17 => Sum.inr ⟨(false, vertices_527), by decide +kernel⟩
  | 18 => Sum.inl 2
  | 19 => Sum.inr ⟨(false, vertices_905), by decide +kernel⟩
  | 20 => Sum.inr ⟨(true, vertices_284), by decide +kernel⟩
  | 21 => Sum.inl 1
  | 22 => Sum.inr ⟨(false, vertices_565), by decide +kernel⟩
  | 23 => Sum.inr ⟨(false, vertices_213), by decide +kernel⟩
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
cert_row_2 0 1 2 3 7 284
cert_row_4 1 0 3 4 5 7 370 50 3
cert_row_4 2 0 4 6 7 8 930 290 2
cert_row_4 3 2 4 5 6 7 488 200 1
cert_rows
cert_pivot_2 1 3 0 2
cert_heightProof 4
cert_coverFacet 0 286
cert_cover_5 0 0 0 1 2 3 14 286 3
cert_coverFacet 1 534
cert_cover_2 1 1 0 3 8 22 534 3
cert_coverFacet 2 778
cert_cover_2 2 2 0 7 8 266 778 3
cert_coverFacet 3 370
cert_cover_5 3 1 0 3 4 5 50 370 3
cert_coverFacet 4 562
cert_cover_2 4 3 0 4 8 50 562 3
cert_coverFacet 5 930
cert_cover_5 5 2 0 4 6 7 290 930 2
cert_coverFacet 6 348
cert_cover_5 6 0 1 2 3 5 284 348 3
cert_coverFacet 7 204
cert_cover_2 7 2 1 5 6 76 204 3
cert_coverFacet 8 488
cert_cover_5 8 3 2 4 5 6 200 488 1
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0716

end
end BundlePart5

section BundlePart6
/- Source: ProjectionCertificates/R_m16e10q1_0717.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0717

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [143, 539, 451, 771, 525, 229, 837, 410, 818, 124, 540, 172, 596, 440, 624, 992, 11, 131, 259, 515, 13, 69, 133, 517, 521, 193, 321, 769, 26, 138, 274, 530, 386, 770, 28, 44, 140, 524, 84, 532, 100, 164, 580, 56, 408, 536, 168, 112, 304, 560, 592, 224, 608, 416, 800, 448, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_143, vertices_539, vertices_451, vertices_771, vertices_525, vertices_229, vertices_837, vertices_410, vertices_818, vertices_124, vertices_540, vertices_172, vertices_596, vertices_440, vertices_624, vertices_992] (by decide +kernel)
  polygons := literalFinset [vertices_11, vertices_131, vertices_259, vertices_515, vertices_13, vertices_69, vertices_133, vertices_517, vertices_521, vertices_193, vertices_321, vertices_769, vertices_26, vertices_138, vertices_274, vertices_530, vertices_386, vertices_770, vertices_28, vertices_44, vertices_140, vertices_524, vertices_84, vertices_532, vertices_100, vertices_164, vertices_580, vertices_56, vertices_408, vertices_536, vertices_168, vertices_112, vertices_304, vertices_560, vertices_592, vertices_224, vertices_608, vertices_416, vertices_800, vertices_448, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_143), (false, vertices_539), (false, vertices_451), (false, vertices_771), (false, vertices_525), (false, vertices_229), (false, vertices_837), (true, vertices_274), (true, vertices_28), (true, vertices_44), (true, vertices_84), (true, vertices_532), (true, vertices_56), (true, vertices_408), (true, vertices_168), (true, vertices_112), (true, vertices_304), (true, vertices_560), (true, vertices_592), (true, vertices_608), (true, vertices_416), (true, vertices_800)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 16 20 23 25 26 27 28 29 30
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_143) then 17 else
  if p.val = (false, vertices_539) then 18 else
  if p.val = (false, vertices_451) then 19 else
  if p.val = (false, vertices_771) then 0 else
  if p.val = (false, vertices_525) then 1 else
  if p.val = (false, vertices_229) then 21 else
  if p.val = (false, vertices_837) then 22 else
  if p.val = (true, vertices_274) then 2 else
  if p.val = (true, vertices_28) then 3 else
  if p.val = (true, vertices_44) then 4 else
  if p.val = (true, vertices_84) then 5 else
  if p.val = (true, vertices_532) then 6 else
  if p.val = (true, vertices_56) then 7 else
  if p.val = (true, vertices_408) then 24 else
  if p.val = (true, vertices_168) then 8 else
  if p.val = (true, vertices_112) then 9 else
  if p.val = (true, vertices_304) then 10 else
  if p.val = (true, vertices_560) then 11 else
  if p.val = (true, vertices_592) then 12 else
  if p.val = (true, vertices_608) then 13 else
  if p.val = (true, vertices_416) then 14 else
  if p.val = (true, vertices_800) then 15 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_771), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_525), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_274), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_28), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_44), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_84), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_532), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_56), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_168), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_112), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_304), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_560), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_592), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_608), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_416), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_800), by decide +kernel⟩
  | 16 => Sum.inl 0
  | 17 => Sum.inr ⟨(false, vertices_143), by decide +kernel⟩
  | 18 => Sum.inr ⟨(false, vertices_539), by decide +kernel⟩
  | 19 => Sum.inr ⟨(false, vertices_451), by decide +kernel⟩
  | 20 => Sum.inl 1
  | 21 => Sum.inr ⟨(false, vertices_229), by decide +kernel⟩
  | 22 => Sum.inr ⟨(false, vertices_837), by decide +kernel⟩
  | 23 => Sum.inl 2
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
cert_row_4 0 0 3 4 7 8 818 274 2
cert_row_4 1 1 2 3 4 5 124 28 3
cert_row_2 2 2 3 6 7 408
cert_row_4 3 4 5 6 7 8 992 224 3
cert_rows
cert_pivot_2 0 1 2 4
cert_heightProof 4
cert_coverFacet 0 410
cert_cover_5 0 2 0 2 3 6 26 410 3
cert_coverFacet 1 818
cert_cover_5 1 0 0 3 4 7 274 818 2
cert_coverFacet 2 124
cert_cover_5 2 1 1 2 3 4 28 124 3
cert_coverFacet 3 540
cert_cover_2 3 2 1 3 8 28 540 3
cert_coverFacet 4 172
cert_cover_2 4 2 1 4 6 44 172 3
cert_coverFacet 5 596
cert_cover_2 5 3 1 5 8 84 596 3
cert_coverFacet 6 440
cert_cover_5 6 2 2 3 4 6 56 440 3
cert_coverFacet 7 624
cert_cover_2 7 4 3 5 8 112 624 3
cert_coverFacet 8 992
cert_cover_5 8 3 4 5 6 7 224 992 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0717

end
end BundlePart6

section BundlePart7
/- Source: ProjectionCertificates/R_m16e10q1_0718.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0718

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [171, 307, 835, 643, 653, 361, 585, 902, 178, 402, 604, 236, 244, 404, 788, 880, 35, 131, 259, 515, 41, 73, 137, 521, 289, 321, 577, 641, 50, 146, 274, 162, 386, 642, 770, 76, 140, 524, 84, 148, 276, 532, 228, 388, 644, 772, 104, 168, 584, 112, 176, 304, 592, 400, 784, 352, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_171, vertices_307, vertices_835, vertices_643, vertices_653, vertices_361, vertices_585, vertices_902, vertices_178, vertices_402, vertices_604, vertices_236, vertices_244, vertices_404, vertices_788, vertices_880] (by decide +kernel)
  polygons := literalFinset [vertices_35, vertices_131, vertices_259, vertices_515, vertices_41, vertices_73, vertices_137, vertices_521, vertices_289, vertices_321, vertices_577, vertices_641, vertices_50, vertices_146, vertices_274, vertices_162, vertices_386, vertices_642, vertices_770, vertices_76, vertices_140, vertices_524, vertices_84, vertices_148, vertices_276, vertices_532, vertices_228, vertices_388, vertices_644, vertices_772, vertices_104, vertices_168, vertices_584, vertices_112, vertices_176, vertices_304, vertices_592, vertices_400, vertices_784, vertices_352, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_171), (false, vertices_307), (false, vertices_835), (false, vertices_643), (false, vertices_653), (false, vertices_361), (false, vertices_585), (true, vertices_146), (true, vertices_386), (true, vertices_76), (true, vertices_84), (true, vertices_148), (true, vertices_276), (true, vertices_532), (true, vertices_228), (true, vertices_388), (true, vertices_772), (true, vertices_112), (true, vertices_176), (true, vertices_592), (true, vertices_400), (true, vertices_784)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 16 20 23 25 26 27 28 29 30
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_171) then 17 else
  if p.val = (false, vertices_307) then 18 else
  if p.val = (false, vertices_835) then 19 else
  if p.val = (false, vertices_643) then 0 else
  if p.val = (false, vertices_653) then 21 else
  if p.val = (false, vertices_361) then 24 else
  if p.val = (false, vertices_585) then 1 else
  if p.val = (true, vertices_146) then 2 else
  if p.val = (true, vertices_386) then 3 else
  if p.val = (true, vertices_76) then 4 else
  if p.val = (true, vertices_84) then 5 else
  if p.val = (true, vertices_148) then 6 else
  if p.val = (true, vertices_276) then 7 else
  if p.val = (true, vertices_532) then 8 else
  if p.val = (true, vertices_228) then 22 else
  if p.val = (true, vertices_388) then 9 else
  if p.val = (true, vertices_772) then 10 else
  if p.val = (true, vertices_112) then 11 else
  if p.val = (true, vertices_176) then 12 else
  if p.val = (true, vertices_592) then 13 else
  if p.val = (true, vertices_400) then 14 else
  if p.val = (true, vertices_784) then 15 else
  0
cert_priority
cert_nodeAtPriority_60 643 585 146 386 76 84 148 276 532 388 772 112 176 592 400 784 171 307 835 653 228 361
cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 6 7 8 902 386 1
cert_row_2 1 1 4 5 6 228
cert_row_4 2 1 2 3 5 8 604 76 2
cert_row_4 3 3 4 5 7 8 880 112 3
cert_rows
cert_pivot_2 0 6 1 3
cert_heightProof 4
cert_coverFacet 0 902
cert_cover_5 0 0 0 1 6 7 386 902 1
cert_coverFacet 1 178
cert_cover_2 1 3 0 4 6 50 178 3
cert_coverFacet 2 402
cert_cover_2 2 3 0 6 7 146 402 3
cert_coverFacet 3 604
cert_cover_5 3 2 1 2 3 5 76 604 2
cert_coverFacet 4 236
cert_cover_5 4 1 1 2 4 5 76 236 2
cert_coverFacet 5 244
cert_cover_5 5 1 1 3 4 5 84 244 2
cert_coverFacet 6 404
cert_cover_2 6 3 1 6 7 148 404 3
cert_coverFacet 7 788
cert_cover_2 7 3 1 7 8 276 788 3
cert_coverFacet 8 880
cert_cover_5 8 3 3 4 5 7 112 880 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0718

end
end BundlePart7

section BundlePart8
/- Source: ProjectionCertificates/R_m16e10q1_0719.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0719

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [583, 781, 309, 85, 681, 297, 625, 454, 774, 410, 650, 778, 738, 468, 248, 312, 21, 69, 261, 517, 41, 265, 521, 49, 81, 289, 545, 577, 70, 262, 518, 138, 266, 522, 194, 578, 386, 642, 770, 84, 276, 452, 772, 56, 152, 280, 168, 296, 648, 776, 112, 304, 208, 400, 224, 608, 672]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_583, vertices_781, vertices_309, vertices_85, vertices_681, vertices_297, vertices_625, vertices_454, vertices_774, vertices_410, vertices_650, vertices_778, vertices_738, vertices_468, vertices_248, vertices_312] (by decide +kernel)
  polygons := literalFinset [vertices_21, vertices_69, vertices_261, vertices_517, vertices_41, vertices_265, vertices_521, vertices_49, vertices_81, vertices_289, vertices_545, vertices_577, vertices_70, vertices_262, vertices_518, vertices_138, vertices_266, vertices_522, vertices_194, vertices_578, vertices_386, vertices_642, vertices_770, vertices_84, vertices_276, vertices_452, vertices_772, vertices_56, vertices_152, vertices_280, vertices_168, vertices_296, vertices_648, vertices_776, vertices_112, vertices_304, vertices_208, vertices_400, vertices_224, vertices_608, vertices_672] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_583), (false, vertices_781), (false, vertices_309), (false, vertices_85), (false, vertices_681), (false, vertices_297), (false, vertices_625), (true, vertices_262), (true, vertices_138), (true, vertices_266), (true, vertices_522), (true, vertices_194), (true, vertices_386), (true, vertices_642), (true, vertices_770), (true, vertices_452), (true, vertices_56), (true, vertices_152), (true, vertices_280), (true, vertices_208), (true, vertices_400), (true, vertices_224)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 16 21 18 24 26 27 28 29 30
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_583) then 17 else
  if p.val = (false, vertices_781) then 19 else
  if p.val = (false, vertices_309) then 22 else
  if p.val = (false, vertices_85) then 0 else
  if p.val = (false, vertices_681) then 20 else
  if p.val = (false, vertices_297) then 1 else
  if p.val = (false, vertices_625) then 25 else
  if p.val = (true, vertices_262) then 2 else
  if p.val = (true, vertices_138) then 3 else
  if p.val = (true, vertices_266) then 4 else
  if p.val = (true, vertices_522) then 5 else
  if p.val = (true, vertices_194) then 6 else
  if p.val = (true, vertices_386) then 7 else
  if p.val = (true, vertices_642) then 8 else
  if p.val = (true, vertices_770) then 9 else
  if p.val = (true, vertices_452) then 23 else
  if p.val = (true, vertices_56) then 10 else
  if p.val = (true, vertices_152) then 11 else
  if p.val = (true, vertices_280) then 12 else
  if p.val = (true, vertices_208) then 13 else
  if p.val = (true, vertices_400) then 14 else
  if p.val = (true, vertices_224) then 15 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_85), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_297), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_262), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_138), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_266), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_522), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_194), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_386), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_642), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_770), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_56), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_152), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_280), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_208), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_400), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_224), by decide +kernel⟩
  | 16 => Sum.inl 0
  | 17 => Sum.inr ⟨(false, vertices_583), by decide +kernel⟩
  | 18 => Sum.inl 2
  | 19 => Sum.inr ⟨(false, vertices_781), by decide +kernel⟩
  | 20 => Sum.inr ⟨(false, vertices_681), by decide +kernel⟩
  | 21 => Sum.inl 1
  | 22 => Sum.inr ⟨(false, vertices_309), by decide +kernel⟩
  | 23 => Sum.inr ⟨(true, vertices_452), by decide +kernel⟩
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
cert_row_2 0 1 5 6 7 452
cert_row_4 1 0 2 3 6 7 410 138 2
cert_row_4 2 0 4 5 6 8 738 194 1
cert_row_4 3 2 3 4 5 6 248 56 3
cert_rows
cert_pivot_2 1 7 0 2
cert_heightProof 4
cert_coverFacet 0 454
cert_cover_5 0 0 0 1 5 6 70 454 3
cert_coverFacet 1 774
cert_cover_2 1 1 0 7 8 262 774 3
cert_coverFacet 2 410
cert_cover_5 2 1 0 2 3 6 138 410 2
cert_coverFacet 3 650
cert_cover_2 3 2 0 6 8 138 650 3
cert_coverFacet 4 778
cert_cover_2 4 2 0 7 8 266 778 3
cert_coverFacet 5 738
cert_cover_5 5 2 0 4 5 6 194 738 1
cert_coverFacet 6 468
cert_cover_5 6 0 1 3 5 6 84 468 3
cert_coverFacet 7 248
cert_cover_5 7 3 2 3 4 5 56 248 3
cert_coverFacet 8 312
cert_cover_2 8 3 2 4 7 56 312 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0719

end
end BundlePart8

section BundlePart9
/- Source: ProjectionCertificates/R_m16e10q1_0720.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0720

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [299, 563, 707, 387, 397, 617, 201, 790, 306, 898, 220, 364, 372, 660, 900, 752, 35, 131, 259, 515, 41, 73, 137, 265, 545, 193, 577, 385, 50, 274, 530, 290, 386, 642, 770, 76, 140, 268, 84, 148, 276, 532, 356, 388, 644, 772, 104, 296, 200, 112, 304, 560, 208, 656, 608, 704, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_299, vertices_563, vertices_707, vertices_387, vertices_397, vertices_617, vertices_201, vertices_790, vertices_306, vertices_898, vertices_220, vertices_364, vertices_372, vertices_660, vertices_900, vertices_752] (by decide +kernel)
  polygons := literalFinset [vertices_35, vertices_131, vertices_259, vertices_515, vertices_41, vertices_73, vertices_137, vertices_265, vertices_545, vertices_193, vertices_577, vertices_385, vertices_50, vertices_274, vertices_530, vertices_290, vertices_386, vertices_642, vertices_770, vertices_76, vertices_140, vertices_268, vertices_84, vertices_148, vertices_276, vertices_532, vertices_356, vertices_388, vertices_644, vertices_772, vertices_104, vertices_296, vertices_200, vertices_112, vertices_304, vertices_560, vertices_208, vertices_656, vertices_608, vertices_704, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_299), (false, vertices_563), (false, vertices_707), (false, vertices_387), (false, vertices_397), (false, vertices_617), (false, vertices_201), (true, vertices_274), (true, vertices_770), (true, vertices_76), (true, vertices_84), (true, vertices_148), (true, vertices_276), (true, vertices_532), (true, vertices_356), (true, vertices_644), (true, vertices_772), (true, vertices_112), (true, vertices_304), (true, vertices_208), (true, vertices_656), (true, vertices_896)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 16 20 23 25 26 27 28 29 30
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_299) then 17 else
  if p.val = (false, vertices_563) then 18 else
  if p.val = (false, vertices_707) then 19 else
  if p.val = (false, vertices_387) then 0 else
  if p.val = (false, vertices_397) then 21 else
  if p.val = (false, vertices_617) then 24 else
  if p.val = (false, vertices_201) then 1 else
  if p.val = (true, vertices_274) then 2 else
  if p.val = (true, vertices_770) then 3 else
  if p.val = (true, vertices_76) then 4 else
  if p.val = (true, vertices_84) then 5 else
  if p.val = (true, vertices_148) then 6 else
  if p.val = (true, vertices_276) then 7 else
  if p.val = (true, vertices_532) then 8 else
  if p.val = (true, vertices_356) then 22 else
  if p.val = (true, vertices_644) then 9 else
  if p.val = (true, vertices_772) then 10 else
  if p.val = (true, vertices_112) then 11 else
  if p.val = (true, vertices_304) then 12 else
  if p.val = (true, vertices_208) then 13 else
  if p.val = (true, vertices_656) then 14 else
  if p.val = (true, vertices_896) then 15 else
  0
cert_priority
cert_nodeAtPriority_60 387 201 274 770 76 84 148 276 532 644 772 112 304 208 656 896 299 563 707 397 356 617
cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 3 7 8 790 274 1
cert_row_2 1 1 4 5 7 356
cert_row_4 2 1 2 3 5 6 220 76 2
cert_row_4 3 3 4 5 6 8 752 112 3
cert_rows
cert_pivot_2 0 7 1 3
cert_heightProof 4
cert_coverFacet 0 790
cert_cover_5 0 0 0 1 3 7 274 790 1
cert_coverFacet 1 306
cert_cover_2 1 3 0 4 7 50 306 3
cert_coverFacet 2 898
cert_cover_2 2 6 0 7 8 386 898 3
cert_coverFacet 3 220
cert_cover_5 3 2 1 2 3 5 76 220 2
cert_coverFacet 4 364
cert_cover_5 4 1 1 2 4 5 76 364 2
cert_coverFacet 5 372
cert_cover_5 5 1 1 3 4 5 84 372 2
cert_coverFacet 6 660
cert_cover_2 6 3 1 6 8 148 660 3
cert_coverFacet 7 900
cert_cover_2 7 6 1 7 8 388 900 3
cert_coverFacet 8 752
cert_cover_5 8 3 3 4 5 6 112 752 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0720

end
end BundlePart9

section BundlePart10
/- Source: ProjectionCertificates/R_m16e10q1_0721.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0721

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [151, 563, 451, 771, 205, 533, 837, 810, 434, 60, 156, 108, 628, 440, 616, 968, 19, 131, 259, 515, 21, 69, 133, 517, 529, 193, 321, 769, 50, 146, 290, 546, 386, 770, 28, 44, 76, 140, 52, 148, 532, 100, 580, 56, 152, 104, 296, 552, 200, 584, 392, 776, 432, 560, 608, 448, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_151, vertices_563, vertices_451, vertices_771, vertices_205, vertices_533, vertices_837, vertices_810, vertices_434, vertices_60, vertices_156, vertices_108, vertices_628, vertices_440, vertices_616, vertices_968] (by decide +kernel)
  polygons := literalFinset [vertices_19, vertices_131, vertices_259, vertices_515, vertices_21, vertices_69, vertices_133, vertices_517, vertices_529, vertices_193, vertices_321, vertices_769, vertices_50, vertices_146, vertices_290, vertices_546, vertices_386, vertices_770, vertices_28, vertices_44, vertices_76, vertices_140, vertices_52, vertices_148, vertices_532, vertices_100, vertices_580, vertices_56, vertices_152, vertices_104, vertices_296, vertices_552, vertices_200, vertices_584, vertices_392, vertices_776, vertices_432, vertices_560, vertices_608, vertices_448, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_151), (false, vertices_563), (false, vertices_451), (false, vertices_771), (false, vertices_205), (false, vertices_533), (false, vertices_837), (true, vertices_290), (true, vertices_28), (true, vertices_44), (true, vertices_52), (true, vertices_100), (true, vertices_56), (true, vertices_152), (true, vertices_104), (true, vertices_296), (true, vertices_552), (true, vertices_584), (true, vertices_392), (true, vertices_776), (true, vertices_432), (true, vertices_608)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 16 20 23 24 26 27 28 29 30
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_151) then 17 else
  if p.val = (false, vertices_563) then 18 else
  if p.val = (false, vertices_451) then 19 else
  if p.val = (false, vertices_771) then 0 else
  if p.val = (false, vertices_205) then 21 else
  if p.val = (false, vertices_533) then 1 else
  if p.val = (false, vertices_837) then 22 else
  if p.val = (true, vertices_290) then 2 else
  if p.val = (true, vertices_28) then 3 else
  if p.val = (true, vertices_44) then 4 else
  if p.val = (true, vertices_52) then 5 else
  if p.val = (true, vertices_100) then 6 else
  if p.val = (true, vertices_56) then 7 else
  if p.val = (true, vertices_152) then 8 else
  if p.val = (true, vertices_104) then 9 else
  if p.val = (true, vertices_296) then 10 else
  if p.val = (true, vertices_552) then 11 else
  if p.val = (true, vertices_584) then 12 else
  if p.val = (true, vertices_392) then 13 else
  if p.val = (true, vertices_776) then 14 else
  if p.val = (true, vertices_432) then 25 else
  if p.val = (true, vertices_608) then 15 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_771), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_533), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_290), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_28), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_44), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_52), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_100), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_56), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_152), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_104), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_296), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_552), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_584), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_392), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_776), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_608), by decide +kernel⟩
  | 16 => Sum.inl 0
  | 17 => Sum.inr ⟨(false, vertices_151), by decide +kernel⟩
  | 18 => Sum.inr ⟨(false, vertices_563), by decide +kernel⟩
  | 19 => Sum.inr ⟨(false, vertices_451), by decide +kernel⟩
  | 20 => Sum.inl 1
  | 21 => Sum.inr ⟨(false, vertices_205), by decide +kernel⟩
  | 22 => Sum.inr ⟨(false, vertices_837), by decide +kernel⟩
  | 23 => Sum.inl 2
  | 24 => Sum.inl 3
  | 25 => Sum.inr ⟨(true, vertices_432), by decide +kernel⟩
  | 26 => Sum.inl 4
  | 27 => Sum.inl 5
  | 28 => Sum.inl 6
  | 29 => Sum.inl 7
  | 30 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 2 4 7 8 810 290 1
cert_row_4 1 1 3 4 5 8 628 52 3
cert_row_2 2 3 4 6 7 432
cert_row_4 3 2 5 6 7 8 968 200 3
cert_rows
cert_pivot_2 0 1 3 2
cert_heightProof 4
cert_coverFacet 0 810
cert_cover_5 0 0 0 2 4 7 290 810 1
cert_coverFacet 1 434
cert_cover_5 1 2 0 3 4 6 50 434 3
cert_coverFacet 2 60
cert_cover_2 2 2 1 3 4 28 60 3
cert_coverFacet 3 156
cert_cover_2 3 2 1 3 6 28 156 3
cert_coverFacet 4 108
cert_cover_2 4 2 1 4 5 44 108 3
cert_coverFacet 5 628
cert_cover_5 5 1 1 3 4 5 52 628 3
cert_coverFacet 6 440
cert_cover_5 6 2 2 3 4 6 56 440 3
cert_coverFacet 7 616
cert_cover_2 7 4 2 5 8 104 616 3
cert_coverFacet 8 968
cert_cover_5 8 3 2 5 6 7 200 968 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0721

end
end BundlePart10

section BundlePart11
/- Source: ProjectionCertificates/R_m16e10q1_0722.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0722

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [283, 179, 707, 771, 229, 305, 865, 782, 538, 658, 188, 668, 108, 332, 964, 376, 19, 131, 259, 515, 49, 273, 97, 161, 289, 193, 577, 769, 26, 266, 522, 146, 530, 642, 770, 156, 44, 76, 268, 524, 100, 164, 196, 324, 644, 772, 56, 280, 536, 104, 328, 176, 304, 656, 352, 704, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_283, vertices_179, vertices_707, vertices_771, vertices_229, vertices_305, vertices_865, vertices_782, vertices_538, vertices_658, vertices_188, vertices_668, vertices_108, vertices_332, vertices_964, vertices_376] (by decide +kernel)
  polygons := literalFinset [vertices_19, vertices_131, vertices_259, vertices_515, vertices_49, vertices_273, vertices_97, vertices_161, vertices_289, vertices_193, vertices_577, vertices_769, vertices_26, vertices_266, vertices_522, vertices_146, vertices_530, vertices_642, vertices_770, vertices_156, vertices_44, vertices_76, vertices_268, vertices_524, vertices_100, vertices_164, vertices_196, vertices_324, vertices_644, vertices_772, vertices_56, vertices_280, vertices_536, vertices_104, vertices_328, vertices_176, vertices_304, vertices_656, vertices_352, vertices_704, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_283), (false, vertices_179), (false, vertices_707), (false, vertices_771), (false, vertices_229), (false, vertices_305), (false, vertices_865), (true, vertices_522), (true, vertices_530), (true, vertices_156), (true, vertices_44), (true, vertices_76), (true, vertices_268), (true, vertices_524), (true, vertices_324), (true, vertices_644), (true, vertices_772), (true, vertices_56), (true, vertices_536), (true, vertices_104), (true, vertices_328), (true, vertices_656)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 16 20 23 24 25 27 28 29 30
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_283) then 17 else
  if p.val = (false, vertices_179) then 18 else
  if p.val = (false, vertices_707) then 19 else
  if p.val = (false, vertices_771) then 0 else
  if p.val = (false, vertices_229) then 21 else
  if p.val = (false, vertices_305) then 1 else
  if p.val = (false, vertices_865) then 26 else
  if p.val = (true, vertices_522) then 2 else
  if p.val = (true, vertices_530) then 3 else
  if p.val = (true, vertices_156) then 22 else
  if p.val = (true, vertices_44) then 4 else
  if p.val = (true, vertices_76) then 5 else
  if p.val = (true, vertices_268) then 6 else
  if p.val = (true, vertices_524) then 7 else
  if p.val = (true, vertices_324) then 8 else
  if p.val = (true, vertices_644) then 9 else
  if p.val = (true, vertices_772) then 10 else
  if p.val = (true, vertices_56) then 11 else
  if p.val = (true, vertices_536) then 12 else
  if p.val = (true, vertices_104) then 13 else
  if p.val = (true, vertices_328) then 14 else
  if p.val = (true, vertices_656) then 15 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_771), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_305), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_522), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_530), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_44), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_76), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_268), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_524), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_324), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_644), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_772), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_56), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_536), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_104), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_328), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_656), by decide +kernel⟩
  | 16 => Sum.inl 0
  | 17 => Sum.inr ⟨(false, vertices_283), by decide +kernel⟩
  | 18 => Sum.inr ⟨(false, vertices_179), by decide +kernel⟩
  | 19 => Sum.inr ⟨(false, vertices_707), by decide +kernel⟩
  | 20 => Sum.inl 1
  | 21 => Sum.inr ⟨(false, vertices_229), by decide +kernel⟩
  | 22 => Sum.inr ⟨(true, vertices_156), by decide +kernel⟩
  | 23 => Sum.inl 2
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
cert_row_4 0 0 1 2 7 8 782 266 1
cert_row_4 1 1 5 6 7 8 964 196 3
cert_row_2 2 1 2 3 6 156
cert_row_4 3 2 3 4 5 7 376 56 3
cert_rows
cert_pivot_2 0 8 1 2
cert_heightProof 4
cert_coverFacet 0 782
cert_cover_5 0 0 0 1 2 7 266 782 1
cert_coverFacet 1 538
cert_cover_2 1 2 0 3 8 26 538 3
cert_coverFacet 2 658
cert_cover_2 2 3 0 6 8 146 658 3
cert_coverFacet 3 188
cert_cover_5 3 2 1 2 3 4 156 188 3
cert_coverFacet 4 668
cert_cover_5 4 2 1 2 3 8 156 668 3
cert_coverFacet 5 108
cert_cover_2 5 2 1 4 5 44 108 3
cert_coverFacet 6 332
cert_cover_2 6 2 1 5 7 76 332 3
cert_coverFacet 7 964
cert_cover_5 7 1 1 5 6 7 196 964 3
cert_coverFacet 8 376
cert_cover_5 8 3 2 3 4 5 56 376 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0722

end
end BundlePart11

section BundlePart12
/- Source: ProjectionCertificates/R_m16e10q1_0723.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0723

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [707, 205, 269, 789, 677, 601, 281, 806, 186, 218, 370, 674, 834, 428, 312, 848, 13, 133, 261, 517, 25, 73, 265, 273, 529, 193, 577, 641, 154, 50, 82, 162, 290, 546, 194, 322, 578, 642, 770, 140, 268, 164, 292, 548, 772, 56, 88, 280, 168, 296, 200, 304, 336, 592, 784, 672, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_707, vertices_205, vertices_269, vertices_789, vertices_677, vertices_601, vertices_281, vertices_806, vertices_186, vertices_218, vertices_370, vertices_674, vertices_834, vertices_428, vertices_312, vertices_848] (by decide +kernel)
  polygons := literalFinset [vertices_13, vertices_133, vertices_261, vertices_517, vertices_25, vertices_73, vertices_265, vertices_273, vertices_529, vertices_193, vertices_577, vertices_641, vertices_154, vertices_50, vertices_82, vertices_162, vertices_290, vertices_546, vertices_194, vertices_322, vertices_578, vertices_642, vertices_770, vertices_140, vertices_268, vertices_164, vertices_292, vertices_548, vertices_772, vertices_56, vertices_88, vertices_280, vertices_168, vertices_296, vertices_200, vertices_304, vertices_336, vertices_592, vertices_784, vertices_672, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_707), (false, vertices_205), (false, vertices_269), (false, vertices_789), (false, vertices_677), (false, vertices_601), (false, vertices_281), (true, vertices_154), (true, vertices_50), (true, vertices_82), (true, vertices_162), (true, vertices_290), (true, vertices_546), (true, vertices_322), (true, vertices_770), (true, vertices_292), (true, vertices_56), (true, vertices_168), (true, vertices_296), (true, vertices_304), (true, vertices_336), (true, vertices_832)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 16 19 23 25 26 27 28 29 30
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_707) then 17 else
  if p.val = (false, vertices_205) then 20 else
  if p.val = (false, vertices_269) then 0 else
  if p.val = (false, vertices_789) then 21 else
  if p.val = (false, vertices_677) then 22 else
  if p.val = (false, vertices_601) then 24 else
  if p.val = (false, vertices_281) then 1 else
  if p.val = (true, vertices_154) then 18 else
  if p.val = (true, vertices_50) then 2 else
  if p.val = (true, vertices_82) then 3 else
  if p.val = (true, vertices_162) then 4 else
  if p.val = (true, vertices_290) then 5 else
  if p.val = (true, vertices_546) then 6 else
  if p.val = (true, vertices_322) then 7 else
  if p.val = (true, vertices_770) then 8 else
  if p.val = (true, vertices_292) then 9 else
  if p.val = (true, vertices_56) then 10 else
  if p.val = (true, vertices_168) then 11 else
  if p.val = (true, vertices_296) then 12 else
  if p.val = (true, vertices_304) then 13 else
  if p.val = (true, vertices_336) then 14 else
  if p.val = (true, vertices_832) then 15 else
  0
cert_priority
cert_nodeAtPriority_5 0 269 1 281 50 82 162 290 546 322 770 292 56 168 296 304 336 832 707 154 205 789 677 601
cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 4 7 8 806 290 1
cert_row_4 1 0 3 4 5 7 370 50 3
cert_row_2 2 0 2 3 6 154
cert_row_4 3 1 2 4 6 7 428 140 2
cert_rows
cert_pivot_2 8 5 0 1
cert_heightProof 4
cert_coverFacet 0 806
cert_cover_5 0 0 0 1 4 7 290 806 1
cert_coverFacet 1 186
cert_cover_5 1 2 0 2 3 4 154 186 3
cert_coverFacet 2 218
cert_cover_5 2 2 0 2 3 5 154 218 3
cert_coverFacet 3 370
cert_cover_5 3 1 0 3 4 5 50 370 3
cert_coverFacet 4 674
cert_cover_2 4 4 0 6 8 162 674 3
cert_coverFacet 5 834
cert_cover_2 5 5 0 7 8 322 834 3
cert_coverFacet 6 428
cert_cover_5 6 3 1 2 4 6 140 428 2
cert_coverFacet 7 312
cert_cover_2 7 3 2 4 7 56 312 3
cert_coverFacet 8 848
cert_cover_2 8 5 3 7 8 336 848 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0723

end
end BundlePart12

section BundlePart13
/- Source: ProjectionCertificates/R_m16e10q1_0724.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0724

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [331, 677, 233, 905, 369, 801, 542, 270, 310, 714, 722, 338, 780, 244, 660, 804, 73, 137, 265, 97, 161, 289, 545, 321, 641, 769, 14, 22, 262, 74, 266, 522, 82, 274, 530, 706, 322, 268, 524, 52, 148, 532, 164, 292, 548, 644, 772, 200, 648, 776, 112, 304, 208, 336, 656, 224, 800]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_331, vertices_677, vertices_233, vertices_905, vertices_369, vertices_801, vertices_542, vertices_270, vertices_310, vertices_714, vertices_722, vertices_338, vertices_780, vertices_244, vertices_660, vertices_804] (by decide +kernel)
  polygons := literalFinset [vertices_73, vertices_137, vertices_265, vertices_97, vertices_161, vertices_289, vertices_545, vertices_321, vertices_641, vertices_769, vertices_14, vertices_22, vertices_262, vertices_74, vertices_266, vertices_522, vertices_82, vertices_274, vertices_530, vertices_706, vertices_322, vertices_268, vertices_524, vertices_52, vertices_148, vertices_532, vertices_164, vertices_292, vertices_548, vertices_644, vertices_772, vertices_200, vertices_648, vertices_776, vertices_112, vertices_304, vertices_208, vertices_336, vertices_656, vertices_224, vertices_800] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_331), (false, vertices_677), (false, vertices_233), (false, vertices_905), (false, vertices_369), (false, vertices_801), (true, vertices_14), (true, vertices_22), (true, vertices_262), (true, vertices_522), (true, vertices_82), (true, vertices_274), (true, vertices_530), (true, vertices_706), (true, vertices_268), (true, vertices_524), (true, vertices_52), (true, vertices_148), (true, vertices_532), (true, vertices_292), (true, vertices_772), (true, vertices_208), (true, vertices_656)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 17 20 22 25 27 28 29 30 31
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_331) then 18 else
  if p.val = (false, vertices_677) then 21 else
  if p.val = (false, vertices_233) then 23 else
  if p.val = (false, vertices_905) then 24 else
  if p.val = (false, vertices_369) then 26 else
  if p.val = (false, vertices_801) then 0 else
  if p.val = (true, vertices_14) then 1 else
  if p.val = (true, vertices_22) then 2 else
  if p.val = (true, vertices_262) then 3 else
  if p.val = (true, vertices_522) then 4 else
  if p.val = (true, vertices_82) then 5 else
  if p.val = (true, vertices_274) then 6 else
  if p.val = (true, vertices_530) then 7 else
  if p.val = (true, vertices_706) then 19 else
  if p.val = (true, vertices_268) then 8 else
  if p.val = (true, vertices_524) then 9 else
  if p.val = (true, vertices_52) then 10 else
  if p.val = (true, vertices_148) then 11 else
  if p.val = (true, vertices_532) then 12 else
  if p.val = (true, vertices_292) then 13 else
  if p.val = (true, vertices_772) then 14 else
  if p.val = (true, vertices_208) then 15 else
  if p.val = (true, vertices_656) then 16 else
  0
cert_priority
cert_nodeAtPriority_33 801 14 22 262 522 82 274 530 268 524 52 148 532 292 772 208 656 331 706 677 233 905 369
cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 2 3 8 542 14 3
cert_row_2 1 0 5 6 8 706
cert_row_4 2 0 1 3 4 7 310 22 3
cert_row_4 3 1 3 4 5 6 244 52 3
cert_rows
cert_pivot_2 2 8 0 1
cert_heightProof 4
cert_coverFacet 0 542
cert_cover_5 0 0 0 1 2 3 14 542 3
cert_coverFacet 1 270
cert_cover_2 1 1 0 2 7 14 270 3
cert_coverFacet 2 310
cert_cover_5 2 2 0 1 3 4 22 310 3
cert_coverFacet 3 714
cert_cover_5 3 1 0 2 5 6 74 714 3
cert_coverFacet 4 722
cert_cover_5 4 1 0 3 5 6 82 722 3
cert_coverFacet 5 338
cert_cover_2 5 3 0 5 7 82 338 3
cert_coverFacet 6 780
cert_cover_2 6 2 1 7 8 268 780 3
cert_coverFacet 7 244
cert_cover_5 7 3 1 3 4 5 52 244 3
cert_coverFacet 8 660
cert_cover_2 8 3 1 6 8 148 660 3
cert_coverFacet 9 804
cert_cover_2 9 4 1 7 8 292 804 3
cert_coveringFacets_5
cert_coveringProof
cert_certificate 4 10
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0724

end
end BundlePart13

section BundlePart14
/- Source: ProjectionCertificates/R_m16e10q1_0725.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0725

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [107, 267, 579, 899, 301, 721, 481, 790, 602, 282, 220, 284, 236, 692, 804, 928, 11, 67, 259, 515, 41, 265, 97, 289, 193, 577, 385, 641, 26, 74, 266, 274, 530, 578, 770, 28, 44, 204, 268, 148, 276, 532, 164, 292, 548, 772, 88, 280, 104, 208, 592, 656, 224, 416, 672, 800, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_107, vertices_267, vertices_579, vertices_899, vertices_301, vertices_721, vertices_481, vertices_790, vertices_602, vertices_282, vertices_220, vertices_284, vertices_236, vertices_692, vertices_804, vertices_928] (by decide +kernel)
  polygons := literalFinset [vertices_11, vertices_67, vertices_259, vertices_515, vertices_41, vertices_265, vertices_97, vertices_289, vertices_193, vertices_577, vertices_385, vertices_641, vertices_26, vertices_74, vertices_266, vertices_274, vertices_530, vertices_578, vertices_770, vertices_28, vertices_44, vertices_204, vertices_268, vertices_148, vertices_276, vertices_532, vertices_164, vertices_292, vertices_548, vertices_772, vertices_88, vertices_280, vertices_104, vertices_208, vertices_592, vertices_656, vertices_224, vertices_416, vertices_672, vertices_800, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_107), (false, vertices_267), (false, vertices_579), (false, vertices_899), (false, vertices_301), (false, vertices_721), (false, vertices_481), (true, vertices_26), (true, vertices_274), (true, vertices_530), (true, vertices_28), (true, vertices_204), (true, vertices_148), (true, vertices_276), (true, vertices_532), (true, vertices_164), (true, vertices_548), (true, vertices_772), (true, vertices_88), (true, vertices_280), (true, vertices_672), (true, vertices_800)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 16 19 22 23 25 27 28 29 30
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_107) then 17 else
  if p.val = (false, vertices_267) then 0 else
  if p.val = (false, vertices_579) then 1 else
  if p.val = (false, vertices_899) then 18 else
  if p.val = (false, vertices_301) then 20 else
  if p.val = (false, vertices_721) then 24 else
  if p.val = (false, vertices_481) then 26 else
  if p.val = (true, vertices_26) then 2 else
  if p.val = (true, vertices_274) then 3 else
  if p.val = (true, vertices_530) then 4 else
  if p.val = (true, vertices_28) then 5 else
  if p.val = (true, vertices_204) then 21 else
  if p.val = (true, vertices_148) then 6 else
  if p.val = (true, vertices_276) then 7 else
  if p.val = (true, vertices_532) then 8 else
  if p.val = (true, vertices_164) then 9 else
  if p.val = (true, vertices_548) then 10 else
  if p.val = (true, vertices_772) then 11 else
  if p.val = (true, vertices_88) then 12 else
  if p.val = (true, vertices_280) then 13 else
  if p.val = (true, vertices_672) then 14 else
  if p.val = (true, vertices_800) then 15 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_267), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_579), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_26), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_274), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_530), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_28), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_148), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_276), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_532), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_164), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_548), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_772), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_88), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_280), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_672), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_800), by decide +kernel⟩
  | 16 => Sum.inl 0
  | 17 => Sum.inr ⟨(false, vertices_107), by decide +kernel⟩
  | 18 => Sum.inr ⟨(false, vertices_899), by decide +kernel⟩
  | 19 => Sum.inl 1
  | 20 => Sum.inr ⟨(false, vertices_301), by decide +kernel⟩
  | 21 => Sum.inr ⟨(true, vertices_204), by decide +kernel⟩
  | 22 => Sum.inl 2
  | 23 => Sum.inl 3
  | 24 => Sum.inr ⟨(false, vertices_721), by decide +kernel⟩
  | 25 => Sum.inl 4
  | 26 => Sum.inr ⟨(false, vertices_481), by decide +kernel⟩
  | 27 => Sum.inl 5
  | 28 => Sum.inl 6
  | 29 => Sum.inl 7
  | 30 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 3 7 8 790 274 1
cert_row_4 1 0 2 3 5 8 602 26 3
cert_row_2 2 1 2 5 6 204
cert_row_4 3 1 3 4 6 8 692 148 2
cert_rows
cert_pivot_2 7 0 2 1
cert_heightProof 4
cert_coverFacet 0 790
cert_cover_5 0 0 0 1 3 7 274 790 1
cert_coverFacet 1 602
cert_cover_5 1 1 0 2 3 5 26 602 3
cert_coverFacet 2 282
cert_cover_2 2 2 0 3 7 26 282 3
cert_coverFacet 3 220
cert_cover_5 3 2 1 2 3 5 28 220 3
cert_coverFacet 4 284
cert_cover_2 4 2 1 3 7 28 284 3
cert_coverFacet 5 236
cert_cover_5 5 2 1 2 4 5 44 236 3
cert_coverFacet 6 692
cert_cover_5 6 3 1 3 4 6 148 692 2
cert_coverFacet 7 804
cert_cover_2 7 4 1 7 8 292 804 3
cert_coverFacet 8 928
cert_cover_2 8 6 4 7 8 416 928 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0725

end
end BundlePart14

section BundlePart15
/- Source: ProjectionCertificates/R_m16e10q1_0726.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0726

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [899, 77, 781, 117, 421, 233, 649, 94, 538, 714, 818, 466, 540, 564, 804, 496, 13, 37, 69, 261, 73, 137, 521, 97, 161, 385, 641, 769, 26, 74, 522, 82, 274, 530, 194, 386, 642, 770, 28, 76, 524, 52, 84, 532, 292, 548, 772, 536, 200, 648, 112, 304, 560, 464, 224, 416, 800]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_899, vertices_77, vertices_781, vertices_117, vertices_421, vertices_233, vertices_649, vertices_94, vertices_538, vertices_714, vertices_818, vertices_466, vertices_540, vertices_564, vertices_804, vertices_496] (by decide +kernel)
  polygons := literalFinset [vertices_13, vertices_37, vertices_69, vertices_261, vertices_73, vertices_137, vertices_521, vertices_97, vertices_161, vertices_385, vertices_641, vertices_769, vertices_26, vertices_74, vertices_522, vertices_82, vertices_274, vertices_530, vertices_194, vertices_386, vertices_642, vertices_770, vertices_28, vertices_76, vertices_524, vertices_52, vertices_84, vertices_532, vertices_292, vertices_548, vertices_772, vertices_536, vertices_200, vertices_648, vertices_112, vertices_304, vertices_560, vertices_464, vertices_224, vertices_416, vertices_800] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_899), (false, vertices_77), (false, vertices_781), (false, vertices_117), (false, vertices_421), (false, vertices_233), (false, vertices_649), (true, vertices_26), (true, vertices_74), (true, vertices_522), (true, vertices_82), (true, vertices_274), (true, vertices_530), (true, vertices_194), (true, vertices_28), (true, vertices_532), (true, vertices_548), (true, vertices_536), (true, vertices_304), (true, vertices_560), (true, vertices_464), (true, vertices_800)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 16 18 22 24 26 27 28 29 30
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_899) then 17 else
  if p.val = (false, vertices_77) then 0 else
  if p.val = (false, vertices_781) then 19 else
  if p.val = (false, vertices_117) then 20 else
  if p.val = (false, vertices_421) then 21 else
  if p.val = (false, vertices_233) then 23 else
  if p.val = (false, vertices_649) then 1 else
  if p.val = (true, vertices_26) then 2 else
  if p.val = (true, vertices_74) then 3 else
  if p.val = (true, vertices_522) then 4 else
  if p.val = (true, vertices_82) then 5 else
  if p.val = (true, vertices_274) then 6 else
  if p.val = (true, vertices_530) then 7 else
  if p.val = (true, vertices_194) then 8 else
  if p.val = (true, vertices_28) then 9 else
  if p.val = (true, vertices_532) then 10 else
  if p.val = (true, vertices_548) then 11 else
  if p.val = (true, vertices_536) then 12 else
  if p.val = (true, vertices_304) then 13 else
  if p.val = (true, vertices_560) then 14 else
  if p.val = (true, vertices_464) then 25 else
  if p.val = (true, vertices_800) then 15 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_77), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_649), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_26), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_74), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_522), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_82), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_274), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_530), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_194), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_28), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_532), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_548), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_536), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_304), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_560), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_800), by decide +kernel⟩
  | 16 => Sum.inl 0
  | 17 => Sum.inr ⟨(false, vertices_899), by decide +kernel⟩
  | 18 => Sum.inl 1
  | 19 => Sum.inr ⟨(false, vertices_781), by decide +kernel⟩
  | 20 => Sum.inr ⟨(false, vertices_117), by decide +kernel⟩
  | 21 => Sum.inr ⟨(false, vertices_421), by decide +kernel⟩
  | 22 => Sum.inl 2
  | 23 => Sum.inr ⟨(false, vertices_233), by decide +kernel⟩
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
cert_row_4 0 0 1 2 3 5 94 26 1
cert_row_4 1 0 2 5 6 8 714 74 3
cert_row_2 2 3 5 6 7 464
cert_row_4 3 0 3 4 7 8 818 274 2
cert_rows
cert_pivot_2 1 2 5 0
cert_heightProof 4
cert_coverFacet 0 94
cert_cover_5 0 0 0 1 2 3 26 94 1
cert_coverFacet 1 538
cert_cover_2 1 2 0 3 8 26 538 3
cert_coverFacet 2 714
cert_cover_5 2 1 0 2 5 6 74 714 3
cert_coverFacet 3 818
cert_cover_5 3 3 0 3 4 7 274 818 2
cert_coverFacet 4 466
cert_cover_5 4 2 0 3 5 6 82 466 3
cert_coverFacet 5 540
cert_cover_2 5 2 1 3 8 28 540 3
cert_coverFacet 6 564
cert_cover_2 6 3 1 4 8 52 564 3
cert_coverFacet 7 804
cert_cover_2 7 4 1 7 8 292 804 3
cert_coverFacet 8 496
cert_cover_5 8 2 3 4 5 6 112 496 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0726

end
end BundlePart15

section BundlePart16
/- Source: ProjectionCertificates/R_m16e10q1_0727.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0727

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [787, 229, 665, 369, 177, 961, 206, 270, 582, 774, 314, 538, 714, 188, 300, 868, 49, 145, 273, 529, 97, 161, 193, 321, 641, 769, 14, 70, 262, 518, 26, 202, 266, 522, 274, 530, 578, 770, 44, 140, 268, 100, 164, 292, 196, 580, 772, 56, 152, 536, 296, 648, 176, 304, 352, 704, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_787, vertices_229, vertices_665, vertices_369, vertices_177, vertices_961, vertices_206, vertices_270, vertices_582, vertices_774, vertices_314, vertices_538, vertices_714, vertices_188, vertices_300, vertices_868] (by decide +kernel)
  polygons := literalFinset [vertices_49, vertices_145, vertices_273, vertices_529, vertices_97, vertices_161, vertices_193, vertices_321, vertices_641, vertices_769, vertices_14, vertices_70, vertices_262, vertices_518, vertices_26, vertices_202, vertices_266, vertices_522, vertices_274, vertices_530, vertices_578, vertices_770, vertices_44, vertices_140, vertices_268, vertices_100, vertices_164, vertices_292, vertices_196, vertices_580, vertices_772, vertices_56, vertices_152, vertices_536, vertices_296, vertices_648, vertices_176, vertices_304, vertices_352, vertices_704, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_787), (false, vertices_229), (false, vertices_665), (false, vertices_369), (false, vertices_177), (false, vertices_961), (true, vertices_14), (true, vertices_70), (true, vertices_262), (true, vertices_518), (true, vertices_26), (true, vertices_202), (true, vertices_266), (true, vertices_522), (true, vertices_578), (true, vertices_44), (true, vertices_140), (true, vertices_268), (true, vertices_292), (true, vertices_580), (true, vertices_772), (true, vertices_56), (true, vertices_296)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 17 20 22 24 26 27 29 30 31
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_787) then 18 else
  if p.val = (false, vertices_229) then 21 else
  if p.val = (false, vertices_665) then 23 else
  if p.val = (false, vertices_369) then 25 else
  if p.val = (false, vertices_177) then 0 else
  if p.val = (false, vertices_961) then 28 else
  if p.val = (true, vertices_14) then 1 else
  if p.val = (true, vertices_70) then 2 else
  if p.val = (true, vertices_262) then 3 else
  if p.val = (true, vertices_518) then 4 else
  if p.val = (true, vertices_26) then 5 else
  if p.val = (true, vertices_202) then 19 else
  if p.val = (true, vertices_266) then 6 else
  if p.val = (true, vertices_522) then 7 else
  if p.val = (true, vertices_578) then 8 else
  if p.val = (true, vertices_44) then 9 else
  if p.val = (true, vertices_140) then 10 else
  if p.val = (true, vertices_268) then 11 else
  if p.val = (true, vertices_292) then 12 else
  if p.val = (true, vertices_580) then 13 else
  if p.val = (true, vertices_772) then 14 else
  if p.val = (true, vertices_56) then 15 else
  if p.val = (true, vertices_296) then 16 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_177), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_14), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_70), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_262), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_518), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_26), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_266), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_522), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_578), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_44), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_140), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_268), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_292), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_580), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_772), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_56), by decide +kernel⟩
  | 16 => Sum.inr ⟨(true, vertices_296), by decide +kernel⟩
  | 17 => Sum.inl 0
  | 18 => Sum.inr ⟨(false, vertices_787), by decide +kernel⟩
  | 19 => Sum.inr ⟨(true, vertices_202), by decide +kernel⟩
  | 20 => Sum.inl 1
  | 21 => Sum.inr ⟨(false, vertices_229), by decide +kernel⟩
  | 22 => Sum.inl 2
  | 23 => Sum.inr ⟨(false, vertices_665), by decide +kernel⟩
  | 24 => Sum.inl 3
  | 25 => Sum.inr ⟨(false, vertices_369), by decide +kernel⟩
  | 26 => Sum.inl 4
  | 27 => Sum.inl 5
  | 28 => Sum.inr ⟨(false, vertices_961), by decide +kernel⟩
  | 29 => Sum.inl 6
  | 30 => Sum.inl 7
  | 31 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 1 4 5 7 8 868 100 3
cert_row_2 1 0 2 5 6 202
cert_row_4 2 0 2 3 4 7 314 26 3
cert_row_4 3 1 2 3 4 6 188 44 2
cert_rows
cert_pivot_2 8 5 0 1
cert_heightProof 4
cert_coverFacet 0 206
cert_cover_5 0 1 0 1 2 5 14 206 3
cert_coverFacet 1 270
cert_cover_2 1 1 0 2 7 14 270 3
cert_coverFacet 2 582
cert_cover_2 2 1 0 5 8 70 582 3
cert_coverFacet 3 774
cert_cover_2 3 1 0 7 8 262 774 3
cert_coverFacet 4 314
cert_cover_5 4 2 0 2 3 4 26 314 3
cert_coverFacet 5 538
cert_cover_2 5 2 0 3 8 26 538 3
cert_coverFacet 6 714
cert_cover_5 6 1 0 2 5 8 202 714 3
cert_coverFacet 7 188
cert_cover_5 7 3 1 2 3 4 44 188 2
cert_coverFacet 8 300
cert_cover_2 8 2 1 4 7 44 300 3
cert_coverFacet 9 868
cert_cover_5 9 0 1 4 5 7 100 868 3
cert_coveringFacets_5
cert_coveringProof
cert_certificate 4 10
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0727

end
end BundlePart16

section BundlePart17
/- Source: ProjectionCertificates/R_m16e10q1_0728.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0728

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [331, 301, 681, 585, 721, 481, 270, 526, 566, 214, 454, 602, 556, 308, 404, 944, 41, 73, 265, 521, 161, 289, 193, 321, 577, 641, 14, 22, 198, 262, 518, 74, 266, 522, 82, 530, 322, 44, 268, 524, 52, 148, 276, 292, 548, 388, 552, 584, 304, 560, 208, 592, 400, 656, 416, 672, 448]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_331, vertices_301, vertices_681, vertices_585, vertices_721, vertices_481, vertices_270, vertices_526, vertices_566, vertices_214, vertices_454, vertices_602, vertices_556, vertices_308, vertices_404, vertices_944] (by decide +kernel)
  polygons := literalFinset [vertices_41, vertices_73, vertices_265, vertices_521, vertices_161, vertices_289, vertices_193, vertices_321, vertices_577, vertices_641, vertices_14, vertices_22, vertices_198, vertices_262, vertices_518, vertices_74, vertices_266, vertices_522, vertices_82, vertices_530, vertices_322, vertices_44, vertices_268, vertices_524, vertices_52, vertices_148, vertices_276, vertices_292, vertices_548, vertices_388, vertices_552, vertices_584, vertices_304, vertices_560, vertices_208, vertices_592, vertices_400, vertices_656, vertices_416, vertices_672, vertices_448] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_331), (false, vertices_301), (false, vertices_681), (false, vertices_585), (false, vertices_721), (false, vertices_481), (true, vertices_14), (true, vertices_22), (true, vertices_198), (true, vertices_262), (true, vertices_518), (true, vertices_522), (true, vertices_82), (true, vertices_530), (true, vertices_524), (true, vertices_52), (true, vertices_148), (true, vertices_276), (true, vertices_548), (true, vertices_388), (true, vertices_304), (true, vertices_560), (true, vertices_400)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 17 20 22 24 26 28 29 30 31
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_331) then 18 else
  if p.val = (false, vertices_301) then 21 else
  if p.val = (false, vertices_681) then 23 else
  if p.val = (false, vertices_585) then 0 else
  if p.val = (false, vertices_721) then 25 else
  if p.val = (false, vertices_481) then 27 else
  if p.val = (true, vertices_14) then 1 else
  if p.val = (true, vertices_22) then 2 else
  if p.val = (true, vertices_198) then 19 else
  if p.val = (true, vertices_262) then 3 else
  if p.val = (true, vertices_518) then 4 else
  if p.val = (true, vertices_522) then 5 else
  if p.val = (true, vertices_82) then 6 else
  if p.val = (true, vertices_530) then 7 else
  if p.val = (true, vertices_524) then 8 else
  if p.val = (true, vertices_52) then 9 else
  if p.val = (true, vertices_148) then 10 else
  if p.val = (true, vertices_276) then 11 else
  if p.val = (true, vertices_548) then 12 else
  if p.val = (true, vertices_388) then 13 else
  if p.val = (true, vertices_304) then 14 else
  if p.val = (true, vertices_560) then 15 else
  if p.val = (true, vertices_400) then 16 else
  0
cert_priority
cert_nodeAtPriority_66 585 14 22 262 518 522 82 530 524 52 148 276 548 388 304 560 400 331 198 301 681 721 481
cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 2 3 5 8 602 74 2
cert_row_2 1 0 1 5 6 198
cert_row_4 2 0 1 3 4 8 566 22 3
cert_row_4 3 3 4 6 7 8 944 304 2
cert_rows
cert_pivot_2 2 5 0 3
cert_heightProof 4
cert_coverFacet 0 270
cert_cover_2 0 1 0 2 7 14 270 3
cert_coverFacet 1 526
cert_cover_2 1 1 0 2 8 14 526 3
cert_coverFacet 2 566
cert_cover_5 2 2 0 1 3 4 22 566 3
cert_coverFacet 3 214
cert_cover_5 3 1 0 1 3 5 22 214 3
cert_coverFacet 4 454
cert_cover_5 4 1 0 1 5 7 198 454 3
cert_coverFacet 5 602
cert_cover_5 5 0 0 2 3 5 74 602 2
cert_coverFacet 6 556
cert_cover_2 6 2 1 4 8 44 556 3
cert_coverFacet 7 308
cert_cover_2 7 3 1 4 7 52 308 3
cert_coverFacet 8 404
cert_cover_2 8 3 1 6 7 148 404 3
cert_coverFacet 9 944
cert_cover_5 9 3 3 4 6 7 304 944 2
cert_coveringFacets_5
cert_coveringProof
cert_certificate 4 10
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0728

end
end BundlePart17

section BundlePart18
/- Source: ProjectionCertificates/R_m16e10q1_0729.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0729

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [527, 295, 899, 613, 369, 961, 270, 666, 458, 284, 540, 692, 308, 248, 344, 736, 7, 259, 515, 37, 517, 97, 289, 321, 577, 897, 14, 262, 138, 266, 522, 386, 642, 28, 268, 524, 52, 276, 532, 292, 548, 88, 152, 280, 536, 200, 328, 112, 176, 304, 336, 656, 224, 608, 672, 448, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_527, vertices_295, vertices_899, vertices_613, vertices_369, vertices_961, vertices_270, vertices_666, vertices_458, vertices_284, vertices_540, vertices_692, vertices_308, vertices_248, vertices_344, vertices_736] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_259, vertices_515, vertices_37, vertices_517, vertices_97, vertices_289, vertices_321, vertices_577, vertices_897, vertices_14, vertices_262, vertices_138, vertices_266, vertices_522, vertices_386, vertices_642, vertices_28, vertices_268, vertices_524, vertices_52, vertices_276, vertices_532, vertices_292, vertices_548, vertices_88, vertices_152, vertices_280, vertices_536, vertices_200, vertices_328, vertices_112, vertices_176, vertices_304, vertices_336, vertices_656, vertices_224, vertices_608, vertices_672, vertices_448, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_527), (false, vertices_295), (false, vertices_899), (false, vertices_613), (false, vertices_369), (false, vertices_961), (true, vertices_138), (true, vertices_266), (true, vertices_28), (true, vertices_268), (true, vertices_52), (true, vertices_276), (true, vertices_532), (true, vertices_88), (true, vertices_152), (true, vertices_280), (true, vertices_536), (true, vertices_200), (true, vertices_328), (true, vertices_176), (true, vertices_656), (true, vertices_224), (true, vertices_672)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 17 20 22 23 25 26 27 30 31
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_527) then 18 else
  if p.val = (false, vertices_295) then 19 else
  if p.val = (false, vertices_899) then 28 else
  if p.val = (false, vertices_613) then 21 else
  if p.val = (false, vertices_369) then 24 else
  if p.val = (false, vertices_961) then 29 else
  if p.val = (true, vertices_138) then 0 else
  if p.val = (true, vertices_266) then 1 else
  if p.val = (true, vertices_28) then 2 else
  if p.val = (true, vertices_268) then 3 else
  if p.val = (true, vertices_52) then 4 else
  if p.val = (true, vertices_276) then 5 else
  if p.val = (true, vertices_532) then 6 else
  if p.val = (true, vertices_88) then 7 else
  if p.val = (true, vertices_152) then 8 else
  if p.val = (true, vertices_280) then 9 else
  if p.val = (true, vertices_536) then 10 else
  if p.val = (true, vertices_200) then 11 else
  if p.val = (true, vertices_328) then 12 else
  if p.val = (true, vertices_176) then 13 else
  if p.val = (true, vertices_656) then 14 else
  if p.val = (true, vertices_224) then 15 else
  if p.val = (true, vertices_672) then 16 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_138), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_266), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_28), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_268), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_52), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_276), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_532), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_88), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_152), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_280), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_536), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_200), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_328), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_176), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_656), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_224), by decide +kernel⟩
  | 16 => Sum.inr ⟨(true, vertices_672), by decide +kernel⟩
  | 17 => Sum.inl 0
  | 18 => Sum.inr ⟨(false, vertices_527), by decide +kernel⟩
  | 19 => Sum.inr ⟨(false, vertices_295), by decide +kernel⟩
  | 20 => Sum.inl 1
  | 21 => Sum.inr ⟨(false, vertices_613), by decide +kernel⟩
  | 22 => Sum.inl 2
  | 23 => Sum.inl 3
  | 24 => Sum.inr ⟨(false, vertices_369), by decide +kernel⟩
  | 25 => Sum.inl 4
  | 26 => Sum.inl 5
  | 27 => Sum.inl 6
  | 28 => Sum.inr ⟨(false, vertices_899), by decide +kernel⟩
  | 29 => Sum.inr ⟨(false, vertices_961), by decide +kernel⟩
  | 30 => Sum.inl 7
  | 31 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 2 5 6 7 458 138 2
cert_row_4 1 0 2 3 6 8 666 138 2
cert_row_4 2 1 3 4 6 8 692 52 3
cert_row_4 3 2 3 4 5 6 248 88 2
cert_rows
cert_pivot_2 7 0 1 2
cert_heightProof 4
cert_coverFacet 0 270
cert_cover_2 0 1 0 2 7 14 270 3
cert_coverFacet 1 666
cert_cover_5 1 1 0 2 3 6 138 666 2
cert_coverFacet 2 458
cert_cover_5 2 0 0 2 5 6 138 458 2
cert_coverFacet 3 284
cert_cover_2 3 2 1 3 7 28 284 3
cert_coverFacet 4 540
cert_cover_2 4 2 1 3 8 28 540 3
cert_coverFacet 5 692
cert_cover_5 5 2 1 3 4 6 52 692 3
cert_coverFacet 6 308
cert_cover_2 6 3 1 4 7 52 308 3
cert_coverFacet 7 248
cert_cover_5 7 3 2 3 4 5 88 248 2
cert_coverFacet 8 344
cert_cover_2 8 3 2 5 7 88 344 3
cert_coverFacet 9 736
cert_cover_2 9 5 4 6 8 224 736 3
cert_coveringFacets_5
cert_coveringProof
cert_certificate 4 10
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0729

end
end BundlePart18

section BundlePart19
/- Source: ProjectionCertificates/R_m16e10q1_0730.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0730

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [43, 203, 611, 709, 809, 393, 913, 62, 94, 818, 594, 300, 460, 436, 596, 660, 11, 35, 67, 41, 137, 265, 545, 193, 577, 385, 641, 769, 30, 42, 74, 50, 82, 530, 546, 578, 44, 76, 268, 52, 84, 148, 532, 292, 196, 580, 388, 644, 296, 200, 392, 304, 592, 400, 656, 784, 800]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_43, vertices_203, vertices_611, vertices_709, vertices_809, vertices_393, vertices_913, vertices_62, vertices_94, vertices_818, vertices_594, vertices_300, vertices_460, vertices_436, vertices_596, vertices_660] (by decide +kernel)
  polygons := literalFinset [vertices_11, vertices_35, vertices_67, vertices_41, vertices_137, vertices_265, vertices_545, vertices_193, vertices_577, vertices_385, vertices_641, vertices_769, vertices_30, vertices_42, vertices_74, vertices_50, vertices_82, vertices_530, vertices_546, vertices_578, vertices_44, vertices_76, vertices_268, vertices_52, vertices_84, vertices_148, vertices_532, vertices_292, vertices_196, vertices_580, vertices_388, vertices_644, vertices_296, vertices_200, vertices_392, vertices_304, vertices_592, vertices_400, vertices_656, vertices_784, vertices_800] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_43), (false, vertices_203), (false, vertices_611), (false, vertices_709), (false, vertices_809), (false, vertices_393), (false, vertices_913), (true, vertices_30), (true, vertices_50), (true, vertices_82), (true, vertices_530), (true, vertices_44), (true, vertices_76), (true, vertices_268), (true, vertices_52), (true, vertices_84), (true, vertices_148), (true, vertices_532), (true, vertices_292), (true, vertices_388), (true, vertices_304), (true, vertices_592)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 16 20 22 24 26 27 28 29 30
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_43) then 0 else
  if p.val = (false, vertices_203) then 17 else
  if p.val = (false, vertices_611) then 18 else
  if p.val = (false, vertices_709) then 21 else
  if p.val = (false, vertices_809) then 23 else
  if p.val = (false, vertices_393) then 1 else
  if p.val = (false, vertices_913) then 25 else
  if p.val = (true, vertices_30) then 19 else
  if p.val = (true, vertices_50) then 2 else
  if p.val = (true, vertices_82) then 3 else
  if p.val = (true, vertices_530) then 4 else
  if p.val = (true, vertices_44) then 5 else
  if p.val = (true, vertices_76) then 6 else
  if p.val = (true, vertices_268) then 7 else
  if p.val = (true, vertices_52) then 8 else
  if p.val = (true, vertices_84) then 9 else
  if p.val = (true, vertices_148) then 10 else
  if p.val = (true, vertices_532) then 11 else
  if p.val = (true, vertices_292) then 12 else
  if p.val = (true, vertices_388) then 13 else
  if p.val = (true, vertices_304) then 14 else
  if p.val = (true, vertices_592) then 15 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_43), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_393), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_50), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_82), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_530), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_44), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_76), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_268), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_52), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_84), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_148), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_532), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_292), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_388), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_304), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_592), by decide +kernel⟩
  | 16 => Sum.inl 0
  | 17 => Sum.inr ⟨(false, vertices_203), by decide +kernel⟩
  | 18 => Sum.inr ⟨(false, vertices_611), by decide +kernel⟩
  | 19 => Sum.inr ⟨(true, vertices_30), by decide +kernel⟩
  | 20 => Sum.inl 1
  | 21 => Sum.inr ⟨(false, vertices_709), by decide +kernel⟩
  | 22 => Sum.inl 2
  | 23 => Sum.inr ⟨(false, vertices_809), by decide +kernel⟩
  | 24 => Sum.inl 3
  | 25 => Sum.inr ⟨(false, vertices_913), by decide +kernel⟩
  | 26 => Sum.inl 4
  | 27 => Sum.inl 5
  | 28 => Sum.inl 6
  | 29 => Sum.inl 7
  | 30 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 3 4 7 8 818 50 3
cert_row_2 1 0 1 2 3 30
cert_row_4 2 1 2 5 6 7 460 76 3
cert_row_4 3 1 3 4 6 7 436 52 3
cert_rows
cert_pivot_2 8 0 2 1
cert_heightProof 4
cert_coverFacet 0 62
cert_cover_5 0 1 0 1 2 4 30 62 3
cert_coverFacet 1 94
cert_cover_5 1 1 0 1 2 5 30 94 3
cert_coverFacet 2 818
cert_cover_5 2 0 0 3 4 7 50 818 3
cert_coverFacet 3 594
cert_cover_2 3 3 0 5 8 82 594 3
cert_coverFacet 4 300
cert_cover_2 4 2 1 4 7 44 300 3
cert_coverFacet 5 460
cert_cover_5 5 2 1 2 5 6 76 460 3
cert_coverFacet 6 436
cert_cover_5 6 3 1 3 4 6 52 436 3
cert_coverFacet 7 596
cert_cover_2 7 3 1 5 8 84 596 3
cert_coverFacet 8 660
cert_cover_2 8 3 1 6 8 148 660 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0730

end
end BundlePart19

section BundlePart20
/- Source: ProjectionCertificates/R_m16e10q1_0731.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0731

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [835, 677, 293, 453, 713, 817, 558, 122, 586, 562, 466, 786, 316, 412, 652, 216, 37, 133, 261, 289, 545, 193, 321, 577, 641, 769, 42, 74, 522, 50, 82, 274, 530, 546, 322, 578, 770, 284, 44, 140, 524, 292, 548, 388, 644, 56, 88, 152, 200, 584, 648, 304, 560, 208, 400, 784, 448]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_835, vertices_677, vertices_293, vertices_453, vertices_713, vertices_817, vertices_558, vertices_122, vertices_586, vertices_562, vertices_466, vertices_786, vertices_316, vertices_412, vertices_652, vertices_216] (by decide +kernel)
  polygons := literalFinset [vertices_37, vertices_133, vertices_261, vertices_289, vertices_545, vertices_193, vertices_321, vertices_577, vertices_641, vertices_769, vertices_42, vertices_74, vertices_522, vertices_50, vertices_82, vertices_274, vertices_530, vertices_546, vertices_322, vertices_578, vertices_770, vertices_284, vertices_44, vertices_140, vertices_524, vertices_292, vertices_548, vertices_388, vertices_644, vertices_56, vertices_88, vertices_152, vertices_200, vertices_584, vertices_648, vertices_304, vertices_560, vertices_208, vertices_400, vertices_784, vertices_448] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_835), (false, vertices_677), (false, vertices_293), (false, vertices_453), (false, vertices_713), (false, vertices_817), (true, vertices_42), (true, vertices_74), (true, vertices_522), (true, vertices_50), (true, vertices_82), (true, vertices_274), (true, vertices_530), (true, vertices_546), (true, vertices_284), (true, vertices_44), (true, vertices_140), (true, vertices_524), (true, vertices_56), (true, vertices_88), (true, vertices_152), (true, vertices_208), (true, vertices_400)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 17 19 23 25 27 28 29 30 31
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_835) then 18 else
  if p.val = (false, vertices_677) then 20 else
  if p.val = (false, vertices_293) then 0 else
  if p.val = (false, vertices_453) then 21 else
  if p.val = (false, vertices_713) then 24 else
  if p.val = (false, vertices_817) then 26 else
  if p.val = (true, vertices_42) then 1 else
  if p.val = (true, vertices_74) then 2 else
  if p.val = (true, vertices_522) then 3 else
  if p.val = (true, vertices_50) then 4 else
  if p.val = (true, vertices_82) then 5 else
  if p.val = (true, vertices_274) then 6 else
  if p.val = (true, vertices_530) then 7 else
  if p.val = (true, vertices_546) then 8 else
  if p.val = (true, vertices_284) then 22 else
  if p.val = (true, vertices_44) then 9 else
  if p.val = (true, vertices_140) then 10 else
  if p.val = (true, vertices_524) then 11 else
  if p.val = (true, vertices_56) then 12 else
  if p.val = (true, vertices_88) then 13 else
  if p.val = (true, vertices_152) then 14 else
  if p.val = (true, vertices_208) then 15 else
  if p.val = (true, vertices_400) then 16 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_293), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_42), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_74), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_522), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_50), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_82), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_274), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_530), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_546), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_44), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_140), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_524), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_56), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_88), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_152), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_208), by decide +kernel⟩
  | 16 => Sum.inr ⟨(true, vertices_400), by decide +kernel⟩
  | 17 => Sum.inl 0
  | 18 => Sum.inr ⟨(false, vertices_835), by decide +kernel⟩
  | 19 => Sum.inl 1
  | 20 => Sum.inr ⟨(false, vertices_677), by decide +kernel⟩
  | 21 => Sum.inr ⟨(false, vertices_453), by decide +kernel⟩
  | 22 => Sum.inr ⟨(true, vertices_284), by decide +kernel⟩
  | 23 => Sum.inl 2
  | 24 => Sum.inr ⟨(false, vertices_713), by decide +kernel⟩
  | 25 => Sum.inl 3
  | 26 => Sum.inr ⟨(false, vertices_817), by decide +kernel⟩
  | 27 => Sum.inl 4
  | 28 => Sum.inl 5
  | 29 => Sum.inl 6
  | 30 => Sum.inl 7
  | 31 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 2 4 8 558 42 1
cert_row_2 1 1 2 3 7 284
cert_row_4 2 0 2 3 4 5 122 42 2
cert_row_4 3 0 3 5 6 7 466 82 3
cert_rows
cert_pivot_2 8 1 2 0
cert_heightProof 4
cert_coverFacet 0 558
cert_cover_5 0 0 0 1 2 4 42 558 1
cert_coverFacet 1 122
cert_cover_5 1 2 0 2 3 4 42 122 2
cert_coverFacet 2 586
cert_cover_2 2 2 0 5 8 74 586 3
cert_coverFacet 3 562
cert_cover_2 3 3 0 4 8 50 562 3
cert_coverFacet 4 466
cert_cover_5 4 3 0 3 5 6 82 466 3
cert_coverFacet 5 786
cert_cover_2 5 3 0 7 8 274 786 3
cert_coverFacet 6 316
cert_cover_5 6 1 1 2 3 4 284 316 3
cert_coverFacet 7 412
cert_cover_5 7 1 1 2 3 6 284 412 3
cert_coverFacet 8 652
cert_cover_2 8 2 1 6 8 140 652 3
cert_coverFacet 9 216
cert_cover_2 9 3 2 5 6 88 216 3
cert_coveringFacets_5
cert_coveringProof
cert_certificate 4 10
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0731

end
end BundlePart20

section BundlePart21
/- Source: ProjectionCertificates/R_m16e10q1_0732.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0732

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [675, 333, 613, 901, 241, 465, 398, 314, 538, 650, 626, 418, 604, 652, 344, 432, 69, 261, 517, 209, 97, 161, 545, 321, 385, 641, 26, 138, 266, 522, 50, 530, 162, 290, 546, 386, 642, 76, 140, 268, 524, 580, 388, 644, 88, 280, 536, 328, 648, 112, 176, 304, 336, 592, 400, 608, 416]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_675, vertices_333, vertices_613, vertices_901, vertices_241, vertices_465, vertices_398, vertices_314, vertices_538, vertices_650, vertices_626, vertices_418, vertices_604, vertices_652, vertices_344, vertices_432] (by decide +kernel)
  polygons := literalFinset [vertices_69, vertices_261, vertices_517, vertices_209, vertices_97, vertices_161, vertices_545, vertices_321, vertices_385, vertices_641, vertices_26, vertices_138, vertices_266, vertices_522, vertices_50, vertices_530, vertices_162, vertices_290, vertices_546, vertices_386, vertices_642, vertices_76, vertices_140, vertices_268, vertices_524, vertices_580, vertices_388, vertices_644, vertices_88, vertices_280, vertices_536, vertices_328, vertices_648, vertices_112, vertices_176, vertices_304, vertices_336, vertices_592, vertices_400, vertices_608, vertices_416] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_675), (false, vertices_333), (false, vertices_613), (false, vertices_901), (false, vertices_241), (false, vertices_465), (true, vertices_26), (true, vertices_138), (true, vertices_266), (true, vertices_522), (true, vertices_50), (true, vertices_530), (true, vertices_290), (true, vertices_386), (true, vertices_140), (true, vertices_524), (true, vertices_88), (true, vertices_280), (true, vertices_536), (true, vertices_648), (true, vertices_304), (true, vertices_592), (true, vertices_416)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 17 19 23 24 27 28 29 30 31
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_675) then 18 else
  if p.val = (false, vertices_333) then 20 else
  if p.val = (false, vertices_613) then 21 else
  if p.val = (false, vertices_901) then 22 else
  if p.val = (false, vertices_241) then 25 else
  if p.val = (false, vertices_465) then 26 else
  if p.val = (true, vertices_26) then 0 else
  if p.val = (true, vertices_138) then 1 else
  if p.val = (true, vertices_266) then 2 else
  if p.val = (true, vertices_522) then 3 else
  if p.val = (true, vertices_50) then 4 else
  if p.val = (true, vertices_530) then 5 else
  if p.val = (true, vertices_290) then 6 else
  if p.val = (true, vertices_386) then 7 else
  if p.val = (true, vertices_140) then 8 else
  if p.val = (true, vertices_524) then 9 else
  if p.val = (true, vertices_88) then 10 else
  if p.val = (true, vertices_280) then 11 else
  if p.val = (true, vertices_536) then 12 else
  if p.val = (true, vertices_648) then 13 else
  if p.val = (true, vertices_304) then 14 else
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
  | 6 => Sum.inr ⟨(true, vertices_290), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_386), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_140), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_524), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_88), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_280), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_536), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_648), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_304), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_592), by decide +kernel⟩
  | 16 => Sum.inr ⟨(true, vertices_416), by decide +kernel⟩
  | 17 => Sum.inl 0
  | 18 => Sum.inr ⟨(false, vertices_675), by decide +kernel⟩
  | 19 => Sum.inl 1
  | 20 => Sum.inr ⟨(false, vertices_333), by decide +kernel⟩
  | 21 => Sum.inr ⟨(false, vertices_613), by decide +kernel⟩
  | 22 => Sum.inr ⟨(false, vertices_901), by decide +kernel⟩
  | 23 => Sum.inl 2
  | 24 => Sum.inl 3
  | 25 => Sum.inr ⟨(false, vertices_241), by decide +kernel⟩
  | 26 => Sum.inr ⟨(false, vertices_465), by decide +kernel⟩
  | 27 => Sum.inl 4
  | 28 => Sum.inl 5
  | 29 => Sum.inl 6
  | 30 => Sum.inl 7
  | 31 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 2 6 7 398 138 1
cert_row_4 1 0 2 3 4 7 314 26 3
cert_row_4 2 0 3 4 5 8 626 50 3
cert_row_4 3 1 2 3 5 8 604 76 2
cert_rows
cert_pivot_2 6 7 0 1
cert_heightProof 4
cert_coverFacet 0 398
cert_cover_5 0 0 0 1 2 6 138 398 1
cert_coverFacet 1 314
cert_cover_5 1 1 0 2 3 4 26 314 3
cert_coverFacet 2 538
cert_cover_2 2 2 0 3 8 26 538 3
cert_coverFacet 3 650
cert_cover_2 3 2 0 6 8 138 650 3
cert_coverFacet 4 626
cert_cover_5 4 2 0 3 4 5 50 626 3
cert_coverFacet 5 418
cert_cover_2 5 4 0 6 7 162 418 3
cert_coverFacet 6 604
cert_cover_5 6 3 1 2 3 5 76 604 2
cert_coverFacet 7 652
cert_cover_2 7 2 1 6 8 140 652 3
cert_coverFacet 8 344
cert_cover_2 8 3 2 5 7 88 344 3
cert_coverFacet 9 432
cert_cover_2 9 4 3 6 7 176 432 3
cert_coveringFacets_5
cert_coveringProof
cert_certificate 4 10
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0732

end
end BundlePart21

section BundlePart22
/- Source: ProjectionCertificates/R_m16e10q1_0733.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0733

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [419, 597, 217, 409, 817, 737, 334, 526, 566, 294, 682, 394, 716, 308, 340, 344, 153, 81, 273, 529, 161, 289, 545, 193, 577, 385, 14, 38, 262, 518, 138, 266, 522, 162, 290, 546, 386, 76, 524, 52, 84, 276, 532, 292, 324, 580, 88, 280, 200, 328, 392, 648, 304, 560, 336, 672, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_419, vertices_597, vertices_217, vertices_409, vertices_817, vertices_737, vertices_334, vertices_526, vertices_566, vertices_294, vertices_682, vertices_394, vertices_716, vertices_308, vertices_340, vertices_344] (by decide +kernel)
  polygons := literalFinset [vertices_153, vertices_81, vertices_273, vertices_529, vertices_161, vertices_289, vertices_545, vertices_193, vertices_577, vertices_385, vertices_14, vertices_38, vertices_262, vertices_518, vertices_138, vertices_266, vertices_522, vertices_162, vertices_290, vertices_546, vertices_386, vertices_76, vertices_524, vertices_52, vertices_84, vertices_276, vertices_532, vertices_292, vertices_324, vertices_580, vertices_88, vertices_280, vertices_200, vertices_328, vertices_392, vertices_648, vertices_304, vertices_560, vertices_336, vertices_672, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_419), (false, vertices_597), (false, vertices_217), (false, vertices_409), (false, vertices_817), (false, vertices_737), (true, vertices_14), (true, vertices_38), (true, vertices_262), (true, vertices_518), (true, vertices_138), (true, vertices_266), (true, vertices_522), (true, vertices_546), (true, vertices_76), (true, vertices_524), (true, vertices_52), (true, vertices_276), (true, vertices_292), (true, vertices_324), (true, vertices_328), (true, vertices_648), (true, vertices_336)] (by decide +kernel)
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
  if p.val = (true, vertices_292) then 12 else
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
  | 12 => Sum.inr ⟨(true, vertices_292), by decide +kernel⟩
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
cert_row_4 0 0 1 2 5 7 334 14 3
cert_row_4 1 0 1 3 4 8 566 38 2
cert_row_4 2 0 2 4 6 8 682 138 2
cert_row_4 3 1 2 5 6 8 716 76 3
cert_rows
cert_pivot_2 7 3 0 1
cert_heightProof 4
cert_coverFacet 0 334
cert_cover_5 0 0 0 1 2 5 14 334 3
cert_coverFacet 1 526
cert_cover_2 1 1 0 2 8 14 526 3
cert_coverFacet 2 566
cert_cover_5 2 1 0 1 3 4 38 566 2
cert_coverFacet 3 294
cert_cover_2 3 1 0 4 7 38 294 3
cert_coverFacet 4 682
cert_cover_5 4 2 0 2 4 6 138 682 2
cert_coverFacet 5 394
cert_cover_2 5 2 0 6 7 138 394 3
cert_coverFacet 6 716
cert_cover_5 6 3 1 2 5 6 76 716 3
cert_coverFacet 7 308
cert_cover_2 7 3 1 4 7 52 308 3
cert_coverFacet 8 340
cert_cover_2 8 3 1 5 7 84 340 3
cert_coverFacet 9 344
cert_cover_2 9 3 2 5 7 88 344 3
cert_coveringFacets_5
cert_coveringProof
cert_certificate 4 10
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0733

end
end BundlePart22

section BundlePart23
/- Source: ProjectionCertificates/R_m16e10q1_0734.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0734

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [199, 779, 611, 387, 313, 553, 481, 598, 390, 774, 796, 436, 212, 184, 728, 744, 67, 131, 259, 515, 41, 265, 521, 97, 289, 545, 193, 385, 70, 134, 262, 518, 578, 386, 770, 84, 148, 276, 532, 196, 388, 772, 56, 152, 280, 536, 168, 552, 712, 776, 176, 304, 208, 592, 224, 608, 416]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_199, vertices_779, vertices_611, vertices_387, vertices_313, vertices_553, vertices_481, vertices_598, vertices_390, vertices_774, vertices_796, vertices_436, vertices_212, vertices_184, vertices_728, vertices_744] (by decide +kernel)
  polygons := literalFinset [vertices_67, vertices_131, vertices_259, vertices_515, vertices_41, vertices_265, vertices_521, vertices_97, vertices_289, vertices_545, vertices_193, vertices_385, vertices_70, vertices_134, vertices_262, vertices_518, vertices_578, vertices_386, vertices_770, vertices_84, vertices_148, vertices_276, vertices_532, vertices_196, vertices_388, vertices_772, vertices_56, vertices_152, vertices_280, vertices_536, vertices_168, vertices_552, vertices_712, vertices_776, vertices_176, vertices_304, vertices_208, vertices_592, vertices_224, vertices_608, vertices_416] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_199), (false, vertices_779), (false, vertices_611), (false, vertices_387), (false, vertices_313), (false, vertices_553), (false, vertices_481), (true, vertices_262), (true, vertices_518), (true, vertices_84), (true, vertices_148), (true, vertices_276), (true, vertices_532), (true, vertices_388), (true, vertices_772), (true, vertices_152), (true, vertices_536), (true, vertices_168), (true, vertices_712), (true, vertices_176), (true, vertices_208), (true, vertices_592)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 16 20 21 24 25 27 28 29 30
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_199) then 17 else
  if p.val = (false, vertices_779) then 18 else
  if p.val = (false, vertices_611) then 19 else
  if p.val = (false, vertices_387) then 0 else
  if p.val = (false, vertices_313) then 22 else
  if p.val = (false, vertices_553) then 1 else
  if p.val = (false, vertices_481) then 26 else
  if p.val = (true, vertices_262) then 2 else
  if p.val = (true, vertices_518) then 3 else
  if p.val = (true, vertices_84) then 4 else
  if p.val = (true, vertices_148) then 5 else
  if p.val = (true, vertices_276) then 6 else
  if p.val = (true, vertices_532) then 7 else
  if p.val = (true, vertices_388) then 8 else
  if p.val = (true, vertices_772) then 9 else
  if p.val = (true, vertices_152) then 10 else
  if p.val = (true, vertices_536) then 11 else
  if p.val = (true, vertices_168) then 12 else
  if p.val = (true, vertices_712) then 23 else
  if p.val = (true, vertices_176) then 13 else
  if p.val = (true, vertices_208) then 14 else
  if p.val = (true, vertices_592) then 15 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_387), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_553), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_262), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_518), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_84), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_148), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_276), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_532), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_388), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_772), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_152), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_536), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_168), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_176), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_208), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_592), by decide +kernel⟩
  | 16 => Sum.inl 0
  | 17 => Sum.inr ⟨(false, vertices_199), by decide +kernel⟩
  | 18 => Sum.inr ⟨(false, vertices_779), by decide +kernel⟩
  | 19 => Sum.inr ⟨(false, vertices_611), by decide +kernel⟩
  | 20 => Sum.inl 1
  | 21 => Sum.inl 2
  | 22 => Sum.inr ⟨(false, vertices_313), by decide +kernel⟩
  | 23 => Sum.inr ⟨(true, vertices_712), by decide +kernel⟩
  | 24 => Sum.inl 3
  | 25 => Sum.inl 4
  | 26 => Sum.inr ⟨(false, vertices_481), by decide +kernel⟩
  | 27 => Sum.inl 5
  | 28 => Sum.inl 6
  | 29 => Sum.inl 7
  | 30 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 3 5 8 598 70 2
cert_row_2 1 2 5 6 8 712
cert_row_4 2 1 2 3 7 8 796 276 1
cert_row_4 3 1 3 4 6 7 436 148 2
cert_rows
cert_pivot_2 0 5 2 1
cert_heightProof 4
cert_coverFacet 0 598
cert_cover_5 0 0 0 1 3 5 70 598 2
cert_coverFacet 1 390
cert_cover_2 1 1 0 6 7 134 390 3
cert_coverFacet 2 774
cert_cover_2 2 1 0 7 8 262 774 3
cert_coverFacet 3 796
cert_cover_5 3 2 1 2 3 7 276 796 1
cert_coverFacet 4 436
cert_cover_5 4 3 1 3 4 6 148 436 2
cert_coverFacet 5 212
cert_cover_2 5 3 1 5 6 84 212 3
cert_coverFacet 6 184
cert_cover_2 6 3 2 4 6 56 184 3
cert_coverFacet 7 728
cert_cover_5 7 1 2 3 5 6 152 728 2
cert_coverFacet 8 744
cert_cover_5 8 1 2 4 5 6 168 744 2
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0734

end
end BundlePart23

section BundlePart24
/- Source: ProjectionCertificates/R_m16e10q1_0735.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0735

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [775, 27, 555, 403, 709, 389, 57, 689, 346, 778, 844, 372, 436, 228, 120, 744, 11, 19, 259, 515, 133, 261, 517, 25, 41, 49, 145, 545, 385, 641, 26, 266, 522, 274, 770, 308, 100, 164, 196, 324, 580, 388, 772, 56, 88, 104, 552, 328, 584, 776, 112, 176, 336, 400, 224, 672, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_775, vertices_27, vertices_555, vertices_403, vertices_709, vertices_389, vertices_57, vertices_689, vertices_346, vertices_778, vertices_844, vertices_372, vertices_436, vertices_228, vertices_120, vertices_744] (by decide +kernel)
  polygons := literalFinset [vertices_11, vertices_19, vertices_259, vertices_515, vertices_133, vertices_261, vertices_517, vertices_25, vertices_41, vertices_49, vertices_145, vertices_545, vertices_385, vertices_641, vertices_26, vertices_266, vertices_522, vertices_274, vertices_770, vertices_308, vertices_100, vertices_164, vertices_196, vertices_324, vertices_580, vertices_388, vertices_772, vertices_56, vertices_88, vertices_104, vertices_552, vertices_328, vertices_584, vertices_776, vertices_112, vertices_176, vertices_336, vertices_400, vertices_224, vertices_672, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_775), (false, vertices_27), (false, vertices_555), (false, vertices_403), (false, vertices_709), (false, vertices_389), (false, vertices_57), (false, vertices_689), (true, vertices_266), (true, vertices_308), (true, vertices_100), (true, vertices_164), (true, vertices_324), (true, vertices_88), (true, vertices_104), (true, vertices_328), (true, vertices_584), (true, vertices_776), (true, vertices_112), (true, vertices_336), (true, vertices_224)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 19 22 23 25 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_775) then 16 else
  if p.val = (false, vertices_27) then 0 else
  if p.val = (false, vertices_555) then 17 else
  if p.val = (false, vertices_403) then 18 else
  if p.val = (false, vertices_709) then 20 else
  if p.val = (false, vertices_389) then 1 else
  if p.val = (false, vertices_57) then 2 else
  if p.val = (false, vertices_689) then 24 else
  if p.val = (true, vertices_266) then 3 else
  if p.val = (true, vertices_308) then 21 else
  if p.val = (true, vertices_100) then 4 else
  if p.val = (true, vertices_164) then 5 else
  if p.val = (true, vertices_324) then 6 else
  if p.val = (true, vertices_88) then 7 else
  if p.val = (true, vertices_104) then 8 else
  if p.val = (true, vertices_328) then 9 else
  if p.val = (true, vertices_584) then 10 else
  if p.val = (true, vertices_776) then 11 else
  if p.val = (true, vertices_112) then 12 else
  if p.val = (true, vertices_336) then 13 else
  if p.val = (true, vertices_224) then 14 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_27), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_389), by decide +kernel⟩
  | 2 => Sum.inr ⟨(false, vertices_57), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_266), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_100), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_164), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_324), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_88), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_104), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_328), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_584), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_776), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_112), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_336), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_224), by decide +kernel⟩
  | 15 => Sum.inl 0
  | 16 => Sum.inr ⟨(false, vertices_775), by decide +kernel⟩
  | 17 => Sum.inr ⟨(false, vertices_555), by decide +kernel⟩
  | 18 => Sum.inr ⟨(false, vertices_403), by decide +kernel⟩
  | 19 => Sum.inl 1
  | 20 => Sum.inr ⟨(false, vertices_709), by decide +kernel⟩
  | 21 => Sum.inr ⟨(true, vertices_308), by decide +kernel⟩
  | 22 => Sum.inl 2
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
cert_row_4 0 0 2 3 5 7 346 26 3
cert_row_2 1 1 3 4 7 308
cert_row_4 2 1 2 5 7 8 844 324 1
cert_row_4 3 2 4 5 6 8 744 104 3
cert_rows
cert_pivot_2 0 3 1 2
cert_heightProof 4
cert_coverFacet 0 346
cert_cover_5 0 0 0 2 3 5 26 346 3
cert_coverFacet 1 778
cert_cover_2 1 2 0 7 8 266 778 3
cert_coverFacet 2 844
cert_cover_5 2 2 1 2 5 7 324 844 1
cert_coverFacet 3 372
cert_cover_5 3 1 1 3 4 5 308 372 3
cert_coverFacet 4 436
cert_cover_5 4 1 1 3 4 6 308 436 3
cert_coverFacet 5 228
cert_cover_2 5 4 1 5 6 100 228 3
cert_coverFacet 6 120
cert_cover_2 6 3 2 4 5 56 120 3
cert_coverFacet 7 744
cert_cover_5 7 3 2 4 5 6 104 744 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0735

end
end BundlePart24

section BundlePart25
/- Source: ProjectionCertificates/R_m16e10q1_0736.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0736

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [659, 99, 419, 579, 405, 617, 817, 358, 714, 450, 220, 796, 108, 812, 452, 664, 35, 67, 131, 515, 145, 273, 529, 97, 289, 545, 577, 385, 98, 290, 194, 322, 578, 386, 642, 28, 44, 76, 780, 148, 276, 100, 292, 196, 324, 388, 152, 536, 104, 552, 200, 584, 648, 656, 784, 800, 448]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_659, vertices_99, vertices_419, vertices_579, vertices_405, vertices_617, vertices_817, vertices_358, vertices_714, vertices_450, vertices_220, vertices_796, vertices_108, vertices_812, vertices_452, vertices_664] (by decide +kernel)
  polygons := literalFinset [vertices_35, vertices_67, vertices_131, vertices_515, vertices_145, vertices_273, vertices_529, vertices_97, vertices_289, vertices_545, vertices_577, vertices_385, vertices_98, vertices_290, vertices_194, vertices_322, vertices_578, vertices_386, vertices_642, vertices_28, vertices_44, vertices_76, vertices_780, vertices_148, vertices_276, vertices_100, vertices_292, vertices_196, vertices_324, vertices_388, vertices_152, vertices_536, vertices_104, vertices_552, vertices_200, vertices_584, vertices_648, vertices_656, vertices_784, vertices_800, vertices_448] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_659), (false, vertices_99), (false, vertices_419), (false, vertices_579), (false, vertices_405), (false, vertices_617), (false, vertices_817), (true, vertices_194), (true, vertices_322), (true, vertices_28), (true, vertices_44), (true, vertices_76), (true, vertices_780), (true, vertices_100), (true, vertices_292), (true, vertices_196), (true, vertices_324), (true, vertices_152), (true, vertices_536), (true, vertices_200), (true, vertices_648), (true, vertices_448)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 16 19 22 24 26 27 28 29 30
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_659) then 17 else
  if p.val = (false, vertices_99) then 0 else
  if p.val = (false, vertices_419) then 18 else
  if p.val = (false, vertices_579) then 1 else
  if p.val = (false, vertices_405) then 20 else
  if p.val = (false, vertices_617) then 23 else
  if p.val = (false, vertices_817) then 25 else
  if p.val = (true, vertices_194) then 2 else
  if p.val = (true, vertices_322) then 3 else
  if p.val = (true, vertices_28) then 4 else
  if p.val = (true, vertices_44) then 5 else
  if p.val = (true, vertices_76) then 6 else
  if p.val = (true, vertices_780) then 21 else
  if p.val = (true, vertices_100) then 7 else
  if p.val = (true, vertices_292) then 8 else
  if p.val = (true, vertices_196) then 9 else
  if p.val = (true, vertices_324) then 10 else
  if p.val = (true, vertices_152) then 11 else
  if p.val = (true, vertices_536) then 12 else
  if p.val = (true, vertices_200) then 13 else
  if p.val = (true, vertices_648) then 14 else
  if p.val = (true, vertices_448) then 15 else
  0
cert_priority
cert_nodeAtPriority_61 0 99 1 579 194 322 28 44 76 100 292 196 324 152 536 200 648 448 659 419 405 780 617 817
cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 4 5 7 358 98 1
cert_row_2 1 1 2 7 8 780
cert_row_4 2 0 2 5 6 8 714 194 1
cert_row_4 3 1 2 3 5 6 220 28 3
cert_rows
cert_pivot_2 4 7 0 1
cert_heightProof 4
cert_coverFacet 0 358
cert_cover_5 0 0 0 1 4 5 98 358 1
cert_coverFacet 1 714
cert_cover_5 1 2 0 2 5 6 194 714 1
cert_coverFacet 2 450
cert_cover_2 2 5 0 6 7 194 450 3
cert_coverFacet 3 220
cert_cover_5 3 3 1 2 3 5 28 220 3
cert_coverFacet 4 796
cert_cover_5 4 1 1 2 3 7 28 796 3
cert_coverFacet 5 108
cert_cover_2 5 2 1 4 5 44 108 3
cert_coverFacet 6 812
cert_cover_5 6 1 1 2 4 7 44 812 3
cert_coverFacet 7 452
cert_cover_2 7 5 1 6 7 196 452 3
cert_coverFacet 8 664
cert_cover_2 8 3 2 6 8 152 664 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0736

end
end BundlePart25

section BundlePart26
/- Source: ProjectionCertificates/R_m16e10q1_0737.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0737

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [327, 355, 421, 709, 601, 113, 689, 590, 774, 794, 106, 426, 916, 120, 184, 408, 323, 69, 133, 261, 49, 81, 529, 97, 161, 289, 577, 641, 70, 262, 518, 42, 74, 266, 522, 98, 290, 770, 580, 388, 644, 772, 56, 88, 152, 280, 536, 104, 168, 584, 392, 112, 176, 400, 656, 784, 416]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_327, vertices_355, vertices_421, vertices_709, vertices_601, vertices_113, vertices_689, vertices_590, vertices_774, vertices_794, vertices_106, vertices_426, vertices_916, vertices_120, vertices_184, vertices_408] (by decide +kernel)
  polygons := literalFinset [vertices_323, vertices_69, vertices_133, vertices_261, vertices_49, vertices_81, vertices_529, vertices_97, vertices_161, vertices_289, vertices_577, vertices_641, vertices_70, vertices_262, vertices_518, vertices_42, vertices_74, vertices_266, vertices_522, vertices_98, vertices_290, vertices_770, vertices_580, vertices_388, vertices_644, vertices_772, vertices_56, vertices_88, vertices_152, vertices_280, vertices_536, vertices_104, vertices_168, vertices_584, vertices_392, vertices_112, vertices_176, vertices_400, vertices_656, vertices_784, vertices_416] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_327), (false, vertices_355), (false, vertices_421), (false, vertices_709), (false, vertices_601), (false, vertices_113), (false, vertices_689), (true, vertices_518), (true, vertices_42), (true, vertices_74), (true, vertices_266), (true, vertices_522), (true, vertices_770), (true, vertices_772), (true, vertices_56), (true, vertices_152), (true, vertices_280), (true, vertices_104), (true, vertices_168), (true, vertices_392), (true, vertices_400), (true, vertices_784)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 16 19 22 24 26 27 28 29 30
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_327) then 17 else
  if p.val = (false, vertices_355) then 18 else
  if p.val = (false, vertices_421) then 20 else
  if p.val = (false, vertices_709) then 21 else
  if p.val = (false, vertices_601) then 23 else
  if p.val = (false, vertices_113) then 0 else
  if p.val = (false, vertices_689) then 25 else
  if p.val = (true, vertices_518) then 1 else
  if p.val = (true, vertices_42) then 2 else
  if p.val = (true, vertices_74) then 3 else
  if p.val = (true, vertices_266) then 4 else
  if p.val = (true, vertices_522) then 5 else
  if p.val = (true, vertices_770) then 6 else
  if p.val = (true, vertices_772) then 7 else
  if p.val = (true, vertices_56) then 8 else
  if p.val = (true, vertices_152) then 9 else
  if p.val = (true, vertices_280) then 10 else
  if p.val = (true, vertices_104) then 11 else
  if p.val = (true, vertices_168) then 12 else
  if p.val = (true, vertices_392) then 13 else
  if p.val = (true, vertices_400) then 14 else
  if p.val = (true, vertices_784) then 15 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_113), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_518), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_42), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_74), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_266), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_522), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_770), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_772), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_56), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_152), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_280), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_104), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_168), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_392), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_400), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_784), by decide +kernel⟩
  | 16 => Sum.inl 0
  | 17 => Sum.inr ⟨(false, vertices_327), by decide +kernel⟩
  | 18 => Sum.inr ⟨(false, vertices_355), by decide +kernel⟩
  | 19 => Sum.inl 1
  | 20 => Sum.inr ⟨(false, vertices_421), by decide +kernel⟩
  | 21 => Sum.inr ⟨(false, vertices_709), by decide +kernel⟩
  | 22 => Sum.inl 2
  | 23 => Sum.inr ⟨(false, vertices_601), by decide +kernel⟩
  | 24 => Sum.inl 3
  | 25 => Sum.inr ⟨(false, vertices_689), by decide +kernel⟩
  | 26 => Sum.inl 4
  | 27 => Sum.inl 5
  | 28 => Sum.inl 6
  | 29 => Sum.inl 7
  | 30 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 2 5 8 590 70 2
cert_row_4 1 0 2 4 6 7 426 42 3
cert_row_4 2 0 2 3 7 8 794 266 2
cert_row_4 3 1 3 6 7 8 916 388 1
cert_rows
cert_pivot_2 5 4 0 1
cert_heightProof 4
cert_coverFacet 0 590
cert_cover_5 0 0 0 1 2 5 70 590 2
cert_coverFacet 1 774
cert_cover_2 1 1 0 7 8 262 774 3
cert_coverFacet 2 794
cert_cover_5 2 2 0 2 3 7 266 794 2
cert_coverFacet 3 106
cert_cover_2 3 2 0 4 5 42 106 3
cert_coverFacet 4 426
cert_cover_5 4 1 0 2 4 6 42 426 3
cert_coverFacet 5 916
cert_cover_5 5 3 1 3 6 7 388 916 1
cert_coverFacet 6 120
cert_cover_2 6 3 2 4 5 56 120 3
cert_coverFacet 7 184
cert_cover_2 7 3 2 4 6 56 184 3
cert_coverFacet 8 408
cert_cover_2 8 3 2 6 7 152 408 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0737

end
end BundlePart26

section BundlePart27
/- Source: ProjectionCertificates/R_m16e10q1_0738.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0738

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [199, 331, 675, 771, 301, 77, 165, 817, 914, 450, 572, 604, 740, 312, 472, 720, 67, 131, 259, 515, 13, 37, 69, 133, 73, 265, 161, 289, 545, 769, 194, 322, 386, 642, 770, 540, 44, 76, 164, 548, 196, 580, 56, 88, 280, 296, 328, 304, 560, 208, 592, 400, 656, 784, 672, 448, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_199, vertices_331, vertices_675, vertices_771, vertices_301, vertices_77, vertices_165, vertices_817, vertices_914, vertices_450, vertices_572, vertices_604, vertices_740, vertices_312, vertices_472, vertices_720] (by decide +kernel)
  polygons := literalFinset [vertices_67, vertices_131, vertices_259, vertices_515, vertices_13, vertices_37, vertices_69, vertices_133, vertices_73, vertices_265, vertices_161, vertices_289, vertices_545, vertices_769, vertices_194, vertices_322, vertices_386, vertices_642, vertices_770, vertices_540, vertices_44, vertices_76, vertices_164, vertices_548, vertices_196, vertices_580, vertices_56, vertices_88, vertices_280, vertices_296, vertices_328, vertices_304, vertices_560, vertices_208, vertices_592, vertices_400, vertices_656, vertices_784, vertices_672, vertices_448, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_199), (false, vertices_331), (false, vertices_675), (false, vertices_771), (false, vertices_301), (false, vertices_77), (false, vertices_165), (false, vertices_817), (true, vertices_386), (true, vertices_540), (true, vertices_548), (true, vertices_580), (true, vertices_56), (true, vertices_88), (true, vertices_280), (true, vertices_208), (true, vertices_592), (true, vertices_400), (true, vertices_656), (true, vertices_448), (true, vertices_704)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 19 22 23 25 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_199) then 16 else
  if p.val = (false, vertices_331) then 17 else
  if p.val = (false, vertices_675) then 18 else
  if p.val = (false, vertices_771) then 0 else
  if p.val = (false, vertices_301) then 20 else
  if p.val = (false, vertices_77) then 1 else
  if p.val = (false, vertices_165) then 2 else
  if p.val = (false, vertices_817) then 24 else
  if p.val = (true, vertices_386) then 3 else
  if p.val = (true, vertices_540) then 21 else
  if p.val = (true, vertices_548) then 4 else
  if p.val = (true, vertices_580) then 5 else
  if p.val = (true, vertices_56) then 6 else
  if p.val = (true, vertices_88) then 7 else
  if p.val = (true, vertices_280) then 8 else
  if p.val = (true, vertices_208) then 9 else
  if p.val = (true, vertices_592) then 10 else
  if p.val = (true, vertices_400) then 11 else
  if p.val = (true, vertices_656) then 12 else
  if p.val = (true, vertices_448) then 13 else
  if p.val = (true, vertices_704) then 14 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_771), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_77), by decide +kernel⟩
  | 2 => Sum.inr ⟨(false, vertices_165), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_386), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_548), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_580), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_56), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_88), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_280), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_208), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_592), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_400), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_656), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_448), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_704), by decide +kernel⟩
  | 15 => Sum.inl 0
  | 16 => Sum.inr ⟨(false, vertices_199), by decide +kernel⟩
  | 17 => Sum.inr ⟨(false, vertices_331), by decide +kernel⟩
  | 18 => Sum.inr ⟨(false, vertices_675), by decide +kernel⟩
  | 19 => Sum.inl 1
  | 20 => Sum.inr ⟨(false, vertices_301), by decide +kernel⟩
  | 21 => Sum.inr ⟨(true, vertices_540), by decide +kernel⟩
  | 22 => Sum.inl 2
  | 23 => Sum.inl 3
  | 24 => Sum.inr ⟨(false, vertices_817), by decide +kernel⟩
  | 25 => Sum.inl 4
  | 26 => Sum.inl 5
  | 27 => Sum.inl 6
  | 28 => Sum.inl 7
  | 29 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 3 6 7 8 914 386 1
cert_row_4 1 1 4 5 6 8 740 164 2
cert_row_2 2 1 2 3 8 540
cert_row_4 3 2 3 5 6 7 472 88 3
cert_rows
cert_pivot_2 0 4 1 2
cert_heightProof 4
cert_coverFacet 0 914
cert_cover_5 0 0 0 3 6 7 386 914 1
cert_coverFacet 1 450
cert_cover_2 1 5 0 6 7 194 450 3
cert_coverFacet 2 572
cert_cover_5 2 2 1 2 3 4 540 572 3
cert_coverFacet 3 604
cert_cover_5 3 2 1 2 3 5 540 604 3
cert_coverFacet 4 740
cert_cover_5 4 1 1 4 5 6 164 740 2
cert_coverFacet 5 312
cert_cover_2 5 3 2 4 7 56 312 3
cert_coverFacet 6 472
cert_cover_5 6 3 2 3 5 6 88 472 3
cert_coverFacet 7 720
cert_cover_2 7 5 3 6 8 208 720 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0738

end
end BundlePart27

section BundlePart28
/- Source: ProjectionCertificates/R_m16e10q1_0739.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0739

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [775, 173, 613, 389, 217, 105, 961, 182, 566, 390, 794, 466, 184, 568, 344, 872, 37, 133, 261, 517, 41, 73, 137, 97, 193, 577, 385, 769, 54, 134, 262, 518, 146, 274, 530, 386, 770, 164, 548, 388, 56, 88, 152, 280, 536, 104, 168, 552, 328, 776, 176, 560, 208, 336, 608, 448, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_775, vertices_173, vertices_613, vertices_389, vertices_217, vertices_105, vertices_961, vertices_182, vertices_566, vertices_390, vertices_794, vertices_466, vertices_184, vertices_568, vertices_344, vertices_872] (by decide +kernel)
  polygons := literalFinset [vertices_37, vertices_133, vertices_261, vertices_517, vertices_41, vertices_73, vertices_137, vertices_97, vertices_193, vertices_577, vertices_385, vertices_769, vertices_54, vertices_134, vertices_262, vertices_518, vertices_146, vertices_274, vertices_530, vertices_386, vertices_770, vertices_164, vertices_548, vertices_388, vertices_56, vertices_88, vertices_152, vertices_280, vertices_536, vertices_104, vertices_168, vertices_552, vertices_328, vertices_776, vertices_176, vertices_560, vertices_208, vertices_336, vertices_608, vertices_448, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_775), (false, vertices_173), (false, vertices_613), (false, vertices_389), (false, vertices_217), (false, vertices_105), (false, vertices_961), (true, vertices_54), (true, vertices_134), (true, vertices_146), (true, vertices_274), (true, vertices_530), (true, vertices_386), (true, vertices_56), (true, vertices_280), (true, vertices_536), (true, vertices_552), (true, vertices_328), (true, vertices_776), (true, vertices_176), (true, vertices_560), (true, vertices_336)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 16 19 22 24 25 26 28 29 30
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_775) then 17 else
  if p.val = (false, vertices_173) then 20 else
  if p.val = (false, vertices_613) then 21 else
  if p.val = (false, vertices_389) then 0 else
  if p.val = (false, vertices_217) then 23 else
  if p.val = (false, vertices_105) then 1 else
  if p.val = (false, vertices_961) then 27 else
  if p.val = (true, vertices_54) then 18 else
  if p.val = (true, vertices_134) then 2 else
  if p.val = (true, vertices_146) then 3 else
  if p.val = (true, vertices_274) then 4 else
  if p.val = (true, vertices_530) then 5 else
  if p.val = (true, vertices_386) then 6 else
  if p.val = (true, vertices_56) then 7 else
  if p.val = (true, vertices_280) then 8 else
  if p.val = (true, vertices_536) then 9 else
  if p.val = (true, vertices_552) then 10 else
  if p.val = (true, vertices_328) then 11 else
  if p.val = (true, vertices_776) then 12 else
  if p.val = (true, vertices_176) then 13 else
  if p.val = (true, vertices_560) then 14 else
  if p.val = (true, vertices_336) then 15 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_389), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_105), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_134), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_146), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_274), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_530), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_386), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_56), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_280), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_536), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_552), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_328), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_776), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_176), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_560), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_336), by decide +kernel⟩
  | 16 => Sum.inl 0
  | 17 => Sum.inr ⟨(false, vertices_775), by decide +kernel⟩
  | 18 => Sum.inr ⟨(true, vertices_54), by decide +kernel⟩
  | 19 => Sum.inl 1
  | 20 => Sum.inr ⟨(false, vertices_173), by decide +kernel⟩
  | 21 => Sum.inr ⟨(false, vertices_613), by decide +kernel⟩
  | 22 => Sum.inl 2
  | 23 => Sum.inr ⟨(false, vertices_217), by decide +kernel⟩
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
cert_row_2 0 0 1 3 4 54
cert_row_4 1 0 3 5 6 7 466 146 2
cert_row_4 2 0 2 3 7 8 794 274 1
cert_row_4 3 2 4 5 7 8 872 104 3
cert_rows
cert_pivot_2 1 6 0 2
cert_heightProof 4
cert_coverFacet 0 182
cert_cover_5 0 0 0 1 3 6 54 182 3
cert_coverFacet 1 566
cert_cover_5 1 0 0 1 3 8 54 566 3
cert_coverFacet 2 390
cert_cover_2 2 1 0 6 7 134 390 3
cert_coverFacet 3 794
cert_cover_5 3 2 0 2 3 7 274 794 1
cert_coverFacet 4 466
cert_cover_5 4 1 0 3 5 6 146 466 2
cert_coverFacet 5 184
cert_cover_2 5 3 2 4 6 56 184 3
cert_coverFacet 6 568
cert_cover_2 6 3 2 4 8 56 568 3
cert_coverFacet 7 344
cert_cover_2 7 3 2 5 7 88 344 3
cert_coverFacet 8 872
cert_cover_5 8 3 2 4 5 7 104 872 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0739

end
end BundlePart28

section BundlePart29
/- Source: ProjectionCertificates/R_m16e10q1_0740.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0740

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [787, 109, 181, 597, 185, 281, 841, 662, 154, 282, 458, 930, 868, 676, 232, 480, 21, 37, 69, 25, 41, 73, 265, 177, 273, 529, 577, 769, 26, 138, 266, 146, 274, 530, 386, 642, 770, 148, 532, 100, 164, 548, 580, 644, 152, 280, 104, 168, 200, 328, 224, 352, 416, 672, 800, 448, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_787, vertices_109, vertices_181, vertices_597, vertices_185, vertices_281, vertices_841, vertices_662, vertices_154, vertices_282, vertices_458, vertices_930, vertices_868, vertices_676, vertices_232, vertices_480] (by decide +kernel)
  polygons := literalFinset [vertices_21, vertices_37, vertices_69, vertices_25, vertices_41, vertices_73, vertices_265, vertices_177, vertices_273, vertices_529, vertices_577, vertices_769, vertices_26, vertices_138, vertices_266, vertices_146, vertices_274, vertices_530, vertices_386, vertices_642, vertices_770, vertices_148, vertices_532, vertices_100, vertices_164, vertices_548, vertices_580, vertices_644, vertices_152, vertices_280, vertices_104, vertices_168, vertices_200, vertices_328, vertices_224, vertices_352, vertices_416, vertices_672, vertices_800, vertices_448, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_787), (false, vertices_109), (false, vertices_181), (false, vertices_597), (false, vertices_185), (false, vertices_281), (false, vertices_841), (true, vertices_26), (true, vertices_138), (true, vertices_266), (true, vertices_146), (true, vertices_386), (true, vertices_642), (true, vertices_548), (true, vertices_644), (true, vertices_200), (true, vertices_224), (true, vertices_352), (true, vertices_416), (true, vertices_672), (true, vertices_800), (true, vertices_448)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 16 18 21 23 26 27 28 29 30
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_787) then 17 else
  if p.val = (false, vertices_109) then 19 else
  if p.val = (false, vertices_181) then 24 else
  if p.val = (false, vertices_597) then 20 else
  if p.val = (false, vertices_185) then 25 else
  if p.val = (false, vertices_281) then 0 else
  if p.val = (false, vertices_841) then 22 else
  if p.val = (true, vertices_26) then 1 else
  if p.val = (true, vertices_138) then 2 else
  if p.val = (true, vertices_266) then 3 else
  if p.val = (true, vertices_146) then 4 else
  if p.val = (true, vertices_386) then 5 else
  if p.val = (true, vertices_642) then 6 else
  if p.val = (true, vertices_548) then 7 else
  if p.val = (true, vertices_644) then 8 else
  if p.val = (true, vertices_200) then 9 else
  if p.val = (true, vertices_224) then 10 else
  if p.val = (true, vertices_352) then 11 else
  if p.val = (true, vertices_416) then 12 else
  if p.val = (true, vertices_672) then 13 else
  if p.val = (true, vertices_800) then 14 else
  if p.val = (true, vertices_448) then 15 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_281), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_26), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_138), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_266), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_146), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_386), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_642), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_548), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_644), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_200), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_224), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_352), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_416), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_672), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_800), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_448), by decide +kernel⟩
  | 16 => Sum.inl 0
  | 17 => Sum.inr ⟨(false, vertices_787), by decide +kernel⟩
  | 18 => Sum.inl 1
  | 19 => Sum.inr ⟨(false, vertices_109), by decide +kernel⟩
  | 20 => Sum.inr ⟨(false, vertices_597), by decide +kernel⟩
  | 21 => Sum.inl 2
  | 22 => Sum.inr ⟨(false, vertices_841), by decide +kernel⟩
  | 23 => Sum.inl 3
  | 24 => Sum.inr ⟨(false, vertices_181), by decide +kernel⟩
  | 25 => Sum.inr ⟨(false, vertices_185), by decide +kernel⟩
  | 26 => Sum.inl 4
  | 27 => Sum.inl 5
  | 28 => Sum.inl 6
  | 29 => Sum.inl 7
  | 30 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 3 6 8 662 146 1
cert_row_4 1 0 2 5 6 7 458 138 2
cert_row_4 2 0 4 6 7 8 930 386 1
cert_row_4 3 1 4 5 7 8 868 100 3
cert_rows
cert_pivot_2 3 2 0 1
cert_heightProof 4
cert_coverFacet 0 662
cert_cover_5 0 0 0 1 3 6 146 662 1
cert_coverFacet 1 154
cert_cover_2 1 2 0 3 6 26 154 3
cert_coverFacet 2 282
cert_cover_2 2 2 0 3 7 26 282 3
cert_coverFacet 3 458
cert_cover_5 3 1 0 2 5 6 138 458 2
cert_coverFacet 4 930
cert_cover_5 4 2 0 4 6 7 386 930 1
cert_coverFacet 5 868
cert_cover_5 5 3 1 4 5 7 100 868 3
cert_coverFacet 6 676
cert_cover_2 6 4 1 6 8 164 676 3
cert_coverFacet 7 232
cert_cover_2 7 4 2 5 6 104 232 3
cert_coverFacet 8 480
cert_cover_2 8 5 4 6 7 224 480 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0740

end
end BundlePart29

-- Public target certificates; internal witness data stays private.
namespace Nonrational.TerminalVerification
open Papers.RationalityTen.ChirotopeDensity.FiniteProjection
open Nonrational.TerminalData
set_option maxRecDepth 100000
set_option maxHeartbeats 0

public theorem projection_4593 : Certifies 4593 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0711.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_4594 : Certifies 4594 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0712.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_4595 : Certifies 4595 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0713.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_4596 : Certifies 4596 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0714.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_4597 : Certifies 4597 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0715.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_4598 : Certifies 4598 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0716.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_4599 : Certifies 4599 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0717.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_4600 : Certifies 4600 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0718.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_4601 : Certifies 4601 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0719.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_4602 : Certifies 4602 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0720.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_4603 : Certifies 4603 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0721.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_4604 : Certifies 4604 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0722.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_4605 : Certifies 4605 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0723.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_4606 : Certifies 4606 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0724.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_4607 : Certifies 4607 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0725.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_4608 : Certifies 4608 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0726.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_4609 : Certifies 4609 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0727.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_4610 : Certifies 4610 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0728.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_4611 : Certifies 4611 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0729.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_4612 : Certifies 4612 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0730.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_4613 : Certifies 4613 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0731.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_4614 : Certifies 4614 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0732.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_4615 : Certifies 4615 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0733.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_4616 : Certifies 4616 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0734.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_4617 : Certifies 4617 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0735.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_4618 : Certifies 4618 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0736.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_4619 : Certifies 4619 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0737.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_4620 : Certifies 4620 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0738.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_4621 : Certifies 4621 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0739.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_4622 : Certifies 4622 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0740.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem certified_B152 (j : Fin 30) :
    Certifies (4593 + j.val) := by
  fin_cases j
  · exact projection_4593
  · exact projection_4594
  · exact projection_4595
  · exact projection_4596
  · exact projection_4597
  · exact projection_4598
  · exact projection_4599
  · exact projection_4600
  · exact projection_4601
  · exact projection_4602
  · exact projection_4603
  · exact projection_4604
  · exact projection_4605
  · exact projection_4606
  · exact projection_4607
  · exact projection_4608
  · exact projection_4609
  · exact projection_4610
  · exact projection_4611
  · exact projection_4612
  · exact projection_4613
  · exact projection_4614
  · exact projection_4615
  · exact projection_4616
  · exact projection_4617
  · exact projection_4618
  · exact projection_4619
  · exact projection_4620
  · exact projection_4621
  · exact projection_4622

end Nonrational.TerminalVerification
-- Explicit facial frame witnesses, with lexical vector tracking.
