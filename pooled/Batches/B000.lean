module
public meta import LowerSchemas.Batches
public import SharedProjectionVertexSets
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Tactic.FinCases
public import Papers.FiniteProjectionChecks

@[expose] public section
set_option debug.skipKernelTC false

section BundlePart0
/- Source: ProjectionCertificates/P0_000.lean -/





@[expose] public section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_000

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
open _root_.Nonrational.SharedProjectionVertexSets

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_87, vertices_391, vertices_179, vertices_357, vertices_425, vertices_625, vertices_198, vertices_722, vertices_460, vertices_696, vertices_872, vertices_712] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_19, vertices_131, vertices_69, vertices_261, vertices_49, vertices_81, vertices_97, vertices_161, vertices_289, vertices_385, vertices_70, vertices_134, vertices_82, vertices_146, vertices_194, vertices_196, vertices_324, vertices_388, vertices_168, vertices_296, vertices_552, vertices_200, vertices_328, vertices_584, vertices_392, vertices_648, vertices_176, vertices_560, vertices_592, vertices_656, vertices_352, vertices_608, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_87), (false, vertices_391), (false, vertices_179), (false, vertices_357), (false, vertices_425), (false, vertices_625), (true, vertices_194), (true, vertices_196), (true, vertices_552), (true, vertices_200), (true, vertices_328), (true, vertices_584), (true, vertices_648), (true, vertices_656), (true, vertices_704)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 9 13 15 17 19 20 21 22 23
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_87) then 10 else
  if p.val = (false, vertices_391) then 11 else
  if p.val = (false, vertices_179) then 12 else
  if p.val = (false, vertices_357) then 14 else
  if p.val = (false, vertices_425) then 16 else
  if p.val = (false, vertices_625) then 18 else
  if p.val = (true, vertices_194) then 0 else
  if p.val = (true, vertices_196) then 1 else
  if p.val = (true, vertices_552) then 2 else
  if p.val = (true, vertices_200) then 3 else
  if p.val = (true, vertices_328) then 4 else
  if p.val = (true, vertices_584) then 5 else
  if p.val = (true, vertices_648) then 6 else
  if p.val = (true, vertices_656) then 7 else
  if p.val = (true, vertices_704) then 8 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_194), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_196), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_552), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_200), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_328), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_584), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_648), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_656), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_704), by decide +kernel⟩
  | 9 => Sum.inl 0
  | 10 => Sum.inr ⟨(false, vertices_87), by decide +kernel⟩
  | 11 => Sum.inr ⟨(false, vertices_391), by decide +kernel⟩
  | 12 => Sum.inr ⟨(false, vertices_179), by decide +kernel⟩
  | 13 => Sum.inl 1
  | 14 => Sum.inr ⟨(false, vertices_357), by decide +kernel⟩
  | 15 => Sum.inl 2
  | 16 => Sum.inr ⟨(false, vertices_425), by decide +kernel⟩
  | 17 => Sum.inl 3
  | 18 => Sum.inr ⟨(false, vertices_625), by decide +kernel⟩
  | 19 => Sum.inl 4
  | 20 => Sum.inl 5
  | 21 => Sum.inl 6
  | 22 => Sum.inl 7
  | 23 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row 0 0 3 5 6 8 722
cert_row 1 1 2 5 6 7 460
cert_row 2 3 2 4 6 8 696
cert_row 3 2 4 5 7 8 872
cert_rows
cert_pivot_2 0 1 3 2
cert_heightProof 4
cert_coverFacet 0 198
cert_cover_4 0 0 1 5 6
cert_coverFacet 1 722
cert_cover_3 1 0 0 3 5 6
cert_coverFacet 2 460
cert_cover_3 2 1 1 2 5 6
cert_coverFacet 3 696
cert_cover_3 3 2 2 3 4 6
cert_coverFacet 4 872
cert_cover_3 4 2 3 4 5 7
cert_coverFacet 5 712
cert_cover_4 5 2 5 6 8
cert_coveringFacets
cert_coveringProof_6
cert_certificate 4 6
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_000

end
end BundlePart0

section BundlePart1
/- Source: ProjectionCertificates/P0_045.lean -/





@[expose] public section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_045

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
open _root_.Nonrational.SharedProjectionVertexSets

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_295, vertices_179, vertices_275, vertices_173, vertices_205, vertices_837, vertices_721, vertices_785, vertices_426, vertices_914, vertices_364, vertices_968] (by decide +kernel)
  polygons := literalFinset [vertices_19, vertices_35, vertices_259, vertices_141, vertices_37, vertices_69, vertices_261, vertices_145, vertices_273, vertices_529, vertices_161, vertices_193, vertices_577, vertices_769, vertices_146, vertices_274, vertices_162, vertices_290, vertices_386, vertices_44, vertices_76, vertices_292, vertices_324, vertices_168, vertices_296, vertices_200, vertices_328, vertices_392, vertices_656, vertices_784, vertices_704, vertices_832, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_295), (false, vertices_179), (false, vertices_275), (false, vertices_173), (false, vertices_205), (false, vertices_837), (false, vertices_721), (false, vertices_785), (true, vertices_386), (true, vertices_296), (true, vertices_328), (true, vertices_392), (true, vertices_896)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 7 10 14 15 17 18 19 20 21
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_295) then 8 else
  if p.val = (false, vertices_179) then 9 else
  if p.val = (false, vertices_275) then 5 else
  if p.val = (false, vertices_173) then 12 else
  if p.val = (false, vertices_205) then 13 else
  if p.val = (false, vertices_837) then 11 else
  if p.val = (false, vertices_721) then 16 else
  if p.val = (false, vertices_785) then 6 else
  if p.val = (true, vertices_386) then 0 else
  if p.val = (true, vertices_296) then 1 else
  if p.val = (true, vertices_328) then 2 else
  if p.val = (true, vertices_392) then 3 else
  if p.val = (true, vertices_896) then 4 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_386), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_296), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_328), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_392), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_896), by decide +kernel⟩
  | 5 => Sum.inr ⟨(false, vertices_275), by decide +kernel⟩
  | 6 => Sum.inr ⟨(false, vertices_785), by decide +kernel⟩
  | 7 => Sum.inl 0
  | 8 => Sum.inr ⟨(false, vertices_295), by decide +kernel⟩
  | 9 => Sum.inr ⟨(false, vertices_179), by decide +kernel⟩
  | 10 => Sum.inl 1
  | 11 => Sum.inr ⟨(false, vertices_837), by decide +kernel⟩
  | 12 => Sum.inr ⟨(false, vertices_173), by decide +kernel⟩
  | 13 => Sum.inr ⟨(false, vertices_205), by decide +kernel⟩
  | 14 => Sum.inl 2
  | 15 => Sum.inl 3
  | 16 => Sum.inr ⟨(false, vertices_721), by decide +kernel⟩
  | 17 => Sum.inl 4
  | 18 => Sum.inl 5
  | 19 => Sum.inl 6
  | 20 => Sum.inl 7
  | 21 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row 0 3 0 6 7 8 914
cert_row 1 0 2 4 6 7 426
cert_row 2 1 2 4 5 7 364
cert_row 3 2 5 6 7 8 968
cert_rows
cert_pivot_2 3 0 1 2
cert_heightProof 4
cert_coverFacet 0 426
cert_cover_3 0 0 1 2 4 6
cert_coverFacet 1 914
cert_cover_3 1 0 0 3 6 7
cert_coverFacet 2 364
cert_cover_3 2 1 2 2 4 5
cert_coverFacet 3 968
cert_cover_3 3 2 3 5 6 7
noncomputable def coveringFacets : Fin 4 → boundary.facets := ![coverFacet0, coverFacet1, coverFacet2, coverFacet3]
noncomputable def coveringProof (j : Fin 4) : FacetCoverage heightProof (coveringFacets j) :=
  (Fin.cases (motive := fun j => FacetCoverage heightProof (coveringFacets j)) cover0 (Fin.cases cover1 (Fin.cases cover2 (Fin.cases cover3 (fun i => Fin.elim0 i))))) j

cert_certificate 4 4
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_045

end
end BundlePart1

section BundlePart2
/- Source: ProjectionCertificates/R_one_six_1831.lean -/





@[expose] public section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1831

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
open _root_.Nonrational.SharedProjectionVertexSets

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_71, vertices_75, vertices_229, vertices_425, vertices_841, vertices_961, vertices_790, vertices_198, vertices_902, vertices_602, vertices_706, vertices_436, vertices_824] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_67, vertices_37, vertices_69, vertices_41, vertices_73, vertices_265, vertices_161, vertices_193, vertices_833, vertices_385, vertices_22, vertices_70, vertices_134, vertices_774, vertices_26, vertices_74, vertices_530, vertices_194, vertices_578, vertices_642, vertices_52, vertices_276, vertices_164, vertices_196, vertices_388, vertices_56, vertices_536, vertices_296, vertices_584, vertices_776, vertices_304, vertices_784, vertices_416, vertices_704, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_71), (false, vertices_75), (false, vertices_229), (false, vertices_425), (false, vertices_841), (false, vertices_961), (true, vertices_134), (true, vertices_774), (true, vertices_530), (true, vertices_194), (true, vertices_578), (true, vertices_642), (true, vertices_276), (true, vertices_388), (true, vertices_536), (true, vertices_304), (true, vertices_784)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 12 14 17 19 20 21 24 25 26
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 15 else
  if p.val = (false, vertices_71) then 0 else
  if p.val = (false, vertices_75) then 1 else
  if p.val = (false, vertices_229) then 16 else
  if p.val = (false, vertices_425) then 18 else
  if p.val = (false, vertices_841) then 22 else
  if p.val = (false, vertices_961) then 23 else
  if p.val = (true, vertices_134) then 2 else
  if p.val = (true, vertices_774) then 13 else
  if p.val = (true, vertices_530) then 3 else
  if p.val = (true, vertices_194) then 4 else
  if p.val = (true, vertices_578) then 5 else
  if p.val = (true, vertices_642) then 6 else
  if p.val = (true, vertices_276) then 7 else
  if p.val = (true, vertices_388) then 8 else
  if p.val = (true, vertices_536) then 9 else
  if p.val = (true, vertices_304) then 10 else
  if p.val = (true, vertices_784) then 11 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_71), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_75), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_134), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_530), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_194), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_578), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_642), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_276), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_388), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_536), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_304), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_784), by decide +kernel⟩
  | 12 => Sum.inl 0
  | 13 => Sum.inr ⟨(true, vertices_774), by decide +kernel⟩
  | 14 => Sum.inl 1
  | 15 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 16 => Sum.inr ⟨(false, vertices_229), by decide +kernel⟩
  | 17 => Sum.inl 2
  | 18 => Sum.inr ⟨(false, vertices_425), by decide +kernel⟩
  | 19 => Sum.inl 3
  | 20 => Sum.inl 4
  | 21 => Sum.inl 5
  | 22 => Sum.inr ⟨(false, vertices_841), by decide +kernel⟩
  | 23 => Sum.inr ⟨(false, vertices_961), by decide +kernel⟩
  | 24 => Sum.inl 6
  | 25 => Sum.inl 7
  | 26 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row 0 8 0 2 3 5 602
cert_row_3 1 1 0 7 8 774
cert_row 2 7 1 3 4 6 436
cert_row 3 8 2 3 4 7 824
cert_rows
cert_pivot_2 5 0 1 2
cert_heightProof 4
cert_coverFacet 0 790
cert_cover_3 0 0 1 1 3 7
cert_coverFacet 1 198
cert_cover_4 1 0 1 5 6
cert_coverFacet 2 902
cert_cover_3 2 0 1 1 6 7
cert_coverFacet 3 602
cert_cover_3 3 0 0 2 3 5
cert_coverFacet 4 706
cert_cover_4 4 0 5 6 8
cert_coverFacet 5 436
cert_cover_3 5 1 2 3 4 6
cert_coverFacet 6 824
cert_cover_3 6 2 3 3 4 7
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1831

end
end BundlePart2

section BundlePart3
/- Source: ProjectionCertificates/P0_001.lean -/





@[expose] public section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_001

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
open _root_.Nonrational.SharedProjectionVertexSets

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_295, vertices_647, vertices_611, vertices_453, vertices_361, vertices_721, vertices_774, vertices_810, vertices_908, vertices_120, vertices_696, vertices_472, vertices_624] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_35, vertices_515, vertices_133, vertices_261, vertices_97, vertices_289, vertices_193, vertices_321, vertices_577, vertices_641, vertices_262, vertices_518, vertices_290, vertices_546, vertices_770, vertices_388, vertices_644, vertices_772, vertices_56, vertices_88, vertices_152, vertices_104, vertices_296, vertices_552, vertices_328, vertices_392, vertices_648, vertices_776, vertices_112, vertices_560, vertices_208, vertices_592, vertices_656, vertices_608, vertices_448] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_295), (false, vertices_647), (false, vertices_611), (false, vertices_453), (false, vertices_361), (false, vertices_721), (true, vertices_770), (true, vertices_772), (true, vertices_56), (true, vertices_88), (true, vertices_152), (true, vertices_552), (true, vertices_392), (true, vertices_648), (true, vertices_776), (true, vertices_112), (true, vertices_560)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 11 15 17 19 21 22 23 24 25
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_295) then 12 else
  if p.val = (false, vertices_647) then 13 else
  if p.val = (false, vertices_611) then 14 else
  if p.val = (false, vertices_453) then 16 else
  if p.val = (false, vertices_361) then 18 else
  if p.val = (false, vertices_721) then 20 else
  if p.val = (true, vertices_770) then 0 else
  if p.val = (true, vertices_772) then 1 else
  if p.val = (true, vertices_56) then 2 else
  if p.val = (true, vertices_88) then 3 else
  if p.val = (true, vertices_152) then 4 else
  if p.val = (true, vertices_552) then 5 else
  if p.val = (true, vertices_392) then 6 else
  if p.val = (true, vertices_648) then 7 else
  if p.val = (true, vertices_776) then 8 else
  if p.val = (true, vertices_112) then 9 else
  if p.val = (true, vertices_560) then 10 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_770), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_772), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_56), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_88), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_152), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_552), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_392), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_648), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_776), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_112), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_560), by decide +kernel⟩
  | 11 => Sum.inl 0
  | 12 => Sum.inr ⟨(false, vertices_295), by decide +kernel⟩
  | 13 => Sum.inr ⟨(false, vertices_647), by decide +kernel⟩
  | 14 => Sum.inr ⟨(false, vertices_611), by decide +kernel⟩
  | 15 => Sum.inl 1
  | 16 => Sum.inr ⟨(false, vertices_453), by decide +kernel⟩
  | 17 => Sum.inl 2
  | 18 => Sum.inr ⟨(false, vertices_361), by decide +kernel⟩
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
cert_row 0 0 2 4 7 8 810
cert_row 1 1 2 6 7 8 908
cert_row 2 4 2 3 6 8 696
cert_row 3 2 3 5 6 7 472
cert_rows
cert_pivot_2 0 1 4 2
cert_heightProof 4
cert_coverFacet 0 774
cert_cover_4 0 0 1 7 8
cert_coverFacet 1 810
cert_cover_3 1 0 0 2 4 7
cert_coverFacet 2 908
cert_cover_3 2 1 1 2 6 7
cert_coverFacet 3 120
cert_cover_4 3 2 3 4 5
cert_coverFacet 4 696
cert_cover_3 4 2 2 3 4 6
cert_coverFacet 5 472
cert_cover_3 5 2 3 3 5 6
cert_coverFacet 6 624
cert_cover_4 6 3 4 5 8
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_001

end
end BundlePart3

section BundlePart4
/- Source: ProjectionCertificates/P0_002.lean -/





@[expose] public section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_002

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
open _root_.Nonrational.SharedProjectionVertexSets

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_307, vertices_595, vertices_451, vertices_421, vertices_713, vertices_689, vertices_790, vertices_842, vertices_684, vertices_460, vertices_780, vertices_308, vertices_564] (by decide +kernel)
  polygons := literalFinset [vertices_19, vertices_67, vertices_259, vertices_49, vertices_529, vertices_161, vertices_289, vertices_193, vertices_577, vertices_385, vertices_641, vertices_274, vertices_530, vertices_322, vertices_578, vertices_770, vertices_140, vertices_268, vertices_524, vertices_52, vertices_276, vertices_532, vertices_164, vertices_292, vertices_548, vertices_388, vertices_772, vertices_200, vertices_328, vertices_584, vertices_648, vertices_776, vertices_304, vertices_560, vertices_672, vertices_448] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_307), (false, vertices_595), (false, vertices_451), (false, vertices_421), (false, vertices_713), (false, vertices_689), (true, vertices_770), (true, vertices_140), (true, vertices_268), (true, vertices_524), (true, vertices_52), (true, vertices_276), (true, vertices_532), (true, vertices_548), (true, vertices_772), (true, vertices_328), (true, vertices_776)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 11 15 17 19 21 22 23 24 25
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_307) then 12 else
  if p.val = (false, vertices_595) then 13 else
  if p.val = (false, vertices_451) then 14 else
  if p.val = (false, vertices_421) then 16 else
  if p.val = (false, vertices_713) then 18 else
  if p.val = (false, vertices_689) then 20 else
  if p.val = (true, vertices_770) then 0 else
  if p.val = (true, vertices_140) then 1 else
  if p.val = (true, vertices_268) then 2 else
  if p.val = (true, vertices_524) then 3 else
  if p.val = (true, vertices_52) then 4 else
  if p.val = (true, vertices_276) then 5 else
  if p.val = (true, vertices_532) then 6 else
  if p.val = (true, vertices_548) then 7 else
  if p.val = (true, vertices_772) then 8 else
  if p.val = (true, vertices_328) then 9 else
  if p.val = (true, vertices_776) then 10 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_770), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_140), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_268), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_524), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_52), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_276), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_532), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_548), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_772), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_328), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_776), by decide +kernel⟩
  | 11 => Sum.inl 0
  | 12 => Sum.inr ⟨(false, vertices_307), by decide +kernel⟩
  | 13 => Sum.inr ⟨(false, vertices_595), by decide +kernel⟩
  | 14 => Sum.inr ⟨(false, vertices_451), by decide +kernel⟩
  | 15 => Sum.inl 1
  | 16 => Sum.inr ⟨(false, vertices_421), by decide +kernel⟩
  | 17 => Sum.inl 2
  | 18 => Sum.inr ⟨(false, vertices_713), by decide +kernel⟩
  | 19 => Sum.inl 3
  | 20 => Sum.inr ⟨(false, vertices_689), by decide +kernel⟩
  | 21 => Sum.inl 4
  | 22 => Sum.inl 5
  | 23 => Sum.inl 6
  | 24 => Sum.inl 7
  | 25 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row 0 3 0 1 7 8 790
cert_row 1 0 2 5 7 8 842
cert_row 2 4 1 2 6 8 684
cert_row 3 1 2 5 6 7 460
cert_rows
cert_pivot_2 3 0 4 1
cert_heightProof 4
cert_coverFacet 0 790
cert_cover_3 0 0 0 1 3 7
cert_coverFacet 1 842
cert_cover_3 1 0 1 2 5 7
cert_coverFacet 2 684
cert_cover_3 2 1 2 2 4 6
cert_coverFacet 3 460
cert_cover_3 3 1 3 2 5 6
cert_coverFacet 4 780
cert_cover_4 4 1 2 7 8
cert_coverFacet 5 308
cert_cover_4 5 1 3 4 7
cert_coverFacet 6 564
cert_cover_4 6 1 3 4 8
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_002

end
end BundlePart4

section BundlePart5
/- Source: ProjectionCertificates/P0_003.lean -/





@[expose] public section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_003

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
open _root_.Nonrational.SharedProjectionVertexSets

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_583, vertices_651, vertices_83, vertices_403, vertices_557, vertices_397, vertices_341, vertices_722, vertices_364, vertices_612, vertices_920, vertices_808, vertices_880] (by decide +kernel)
  polygons := literalFinset [vertices_19, vertices_67, vertices_131, vertices_515, vertices_13, vertices_69, vertices_261, vertices_517, vertices_137, vertices_521, vertices_81, vertices_273, vertices_385, vertices_82, vertices_146, vertices_578, vertices_642, vertices_44, vertices_268, vertices_100, vertices_548, vertices_324, vertices_580, vertices_296, vertices_552, vertices_392, vertices_648, vertices_776, vertices_336, vertices_592, vertices_400, vertices_656, vertices_784, vertices_352, vertices_608, vertices_800] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_583), (false, vertices_651), (false, vertices_83), (false, vertices_403), (false, vertices_557), (false, vertices_397), (false, vertices_341), (true, vertices_100), (true, vertices_296), (true, vertices_776), (true, vertices_592), (true, vertices_656), (true, vertices_784), (true, vertices_352), (true, vertices_608), (true, vertices_800)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 10 14 18 19 20 21 22 23 24
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_583) then 11 else
  if p.val = (false, vertices_651) then 12 else
  if p.val = (false, vertices_83) then 9 else
  if p.val = (false, vertices_403) then 13 else
  if p.val = (false, vertices_557) then 15 else
  if p.val = (false, vertices_397) then 16 else
  if p.val = (false, vertices_341) then 17 else
  if p.val = (true, vertices_100) then 0 else
  if p.val = (true, vertices_296) then 1 else
  if p.val = (true, vertices_776) then 2 else
  if p.val = (true, vertices_592) then 3 else
  if p.val = (true, vertices_656) then 4 else
  if p.val = (true, vertices_784) then 5 else
  if p.val = (true, vertices_352) then 6 else
  if p.val = (true, vertices_608) then 7 else
  if p.val = (true, vertices_800) then 8 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_100), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_296), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_776), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_592), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_656), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_784), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_352), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_608), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_800), by decide +kernel⟩
  | 9 => Sum.inr ⟨(false, vertices_83), by decide +kernel⟩
  | 10 => Sum.inl 0
  | 11 => Sum.inr ⟨(false, vertices_583), by decide +kernel⟩
  | 12 => Sum.inr ⟨(false, vertices_651), by decide +kernel⟩
  | 13 => Sum.inr ⟨(false, vertices_403), by decide +kernel⟩
  | 14 => Sum.inl 1
  | 15 => Sum.inr ⟨(false, vertices_557), by decide +kernel⟩
  | 16 => Sum.inr ⟨(false, vertices_397), by decide +kernel⟩
  | 17 => Sum.inr ⟨(false, vertices_341), by decide +kernel⟩
  | 18 => Sum.inl 2
  | 19 => Sum.inl 3
  | 20 => Sum.inl 4
  | 21 => Sum.inl 5
  | 22 => Sum.inl 6
  | 23 => Sum.inl 7
  | 24 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row 0 0 3 5 6 8 722
cert_row 1 1 2 4 5 7 364
cert_row 2 2 3 6 7 8 920
cert_row 3 3 4 5 7 8 880
cert_rows
cert_pivot_2 0 1 2 3
cert_heightProof 4
cert_coverFacet 0 722
cert_cover_3 0 0 0 3 5 6
cert_coverFacet 1 364
cert_cover_3 1 1 1 2 4 5
cert_coverFacet 2 612
cert_cover_4 2 1 4 5 8
cert_coverFacet 3 920
cert_cover_3 3 2 2 3 6 7
cert_coverFacet 4 808
cert_cover_4 4 2 4 7 8
cert_coverFacet 5 880
cert_cover_3 5 3 3 4 5 7
cert_coveringFacets
cert_coveringProof_6
cert_certificate 4 6
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_003

end
end BundlePart5

section BundlePart6
/- Source: ProjectionCertificates/P0_004.lean -/





@[expose] public section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_004

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
open _root_.Nonrational.SharedProjectionVertexSets

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_107, vertices_651, vertices_595, vertices_661, vertices_409, vertices_297, vertices_369, vertices_810, vertices_610, vertices_908, vertices_468, vertices_596, vertices_868] (by decide +kernel)
  polygons := literalFinset [vertices_11, vertices_67, vertices_515, vertices_41, vertices_137, vertices_265, vertices_81, vertices_145, vertices_273, vertices_529, vertices_97, vertices_289, vertices_641, vertices_42, vertices_522, vertices_98, vertices_546, vertices_578, vertices_84, vertices_148, vertices_532, vertices_324, vertices_580, vertices_388, vertices_644, vertices_772, vertices_296, vertices_392, vertices_648, vertices_776, vertices_336, vertices_592, vertices_400, vertices_352, vertices_608, vertices_800] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_107), (false, vertices_651), (false, vertices_595), (false, vertices_661), (false, vertices_409), (false, vertices_297), (false, vertices_369), (true, vertices_546), (true, vertices_84), (true, vertices_324), (true, vertices_580), (true, vertices_388), (true, vertices_772), (true, vertices_776), (true, vertices_608), (true, vertices_800)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 10 14 16 18 20 21 22 23 24
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_107) then 11 else
  if p.val = (false, vertices_651) then 12 else
  if p.val = (false, vertices_595) then 13 else
  if p.val = (false, vertices_661) then 15 else
  if p.val = (false, vertices_409) then 17 else
  if p.val = (false, vertices_297) then 9 else
  if p.val = (false, vertices_369) then 19 else
  if p.val = (true, vertices_546) then 0 else
  if p.val = (true, vertices_84) then 1 else
  if p.val = (true, vertices_324) then 2 else
  if p.val = (true, vertices_580) then 3 else
  if p.val = (true, vertices_388) then 4 else
  if p.val = (true, vertices_772) then 5 else
  if p.val = (true, vertices_776) then 6 else
  if p.val = (true, vertices_608) then 7 else
  if p.val = (true, vertices_800) then 8 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_546), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_84), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_324), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_580), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_388), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_772), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_776), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_608), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_800), by decide +kernel⟩
  | 9 => Sum.inr ⟨(false, vertices_297), by decide +kernel⟩
  | 10 => Sum.inl 0
  | 11 => Sum.inr ⟨(false, vertices_107), by decide +kernel⟩
  | 12 => Sum.inr ⟨(false, vertices_651), by decide +kernel⟩
  | 13 => Sum.inr ⟨(false, vertices_595), by decide +kernel⟩
  | 14 => Sum.inl 1
  | 15 => Sum.inr ⟨(false, vertices_661), by decide +kernel⟩
  | 16 => Sum.inl 2
  | 17 => Sum.inr ⟨(false, vertices_409), by decide +kernel⟩
  | 18 => Sum.inl 3
  | 19 => Sum.inr ⟨(false, vertices_369), by decide +kernel⟩
  | 20 => Sum.inl 4
  | 21 => Sum.inl 5
  | 22 => Sum.inl 6
  | 23 => Sum.inl 7
  | 24 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row 0 0 2 4 7 8 810
cert_row 1 2 1 6 7 8 908
cert_row 2 3 1 5 6 7 468
cert_row 3 1 4 5 7 8 868
cert_rows
cert_pivot_2 0 2 3 1
cert_heightProof 4
cert_coverFacet 0 810
cert_cover_3 0 0 0 2 4 7
cert_coverFacet 1 610
cert_cover_4 1 0 4 5 8
cert_coverFacet 2 908
cert_cover_3 2 1 1 2 6 7
cert_coverFacet 3 468
cert_cover_3 3 1 2 3 5 6
cert_coverFacet 4 596
cert_cover_4 4 1 3 5 8
cert_coverFacet 5 868
cert_cover_3 5 1 3 4 5 7
cert_coveringFacets
cert_coveringProof_6
cert_certificate 4 6
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_004

end
end BundlePart6

section BundlePart7
/- Source: ProjectionCertificates/P0_005.lean -/





@[expose] public section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_005

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
open _root_.Nonrational.SharedProjectionVertexSets

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_647, vertices_779, vertices_419, vertices_229, vertices_837, vertices_369, vertices_410, vertices_650, vertices_628, vertices_676, vertices_696, vertices_856, vertices_432] (by decide +kernel)
  polygons := literalFinset [vertices_131, vertices_259, vertices_515, vertices_69, vertices_133, vertices_517, vertices_97, vertices_161, vertices_289, vertices_321, vertices_769, vertices_138, vertices_266, vertices_522, vertices_386, vertices_642, vertices_100, vertices_164, vertices_548, vertices_580, vertices_644, vertices_152, vertices_280, vertices_536, vertices_648, vertices_776, vertices_112, vertices_176, vertices_304, vertices_560, vertices_336, vertices_592, vertices_400, vertices_416, vertices_672, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_647), (false, vertices_779), (false, vertices_419), (false, vertices_229), (false, vertices_837), (false, vertices_369), (true, vertices_138), (true, vertices_548), (true, vertices_152), (true, vertices_280), (true, vertices_536), (true, vertices_648), (true, vertices_176), (true, vertices_560), (true, vertices_592), (true, vertices_400), (true, vertices_672)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 11 15 18 19 21 22 23 24 25
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_647) then 12 else
  if p.val = (false, vertices_779) then 13 else
  if p.val = (false, vertices_419) then 14 else
  if p.val = (false, vertices_229) then 16 else
  if p.val = (false, vertices_837) then 17 else
  if p.val = (false, vertices_369) then 20 else
  if p.val = (true, vertices_138) then 0 else
  if p.val = (true, vertices_548) then 1 else
  if p.val = (true, vertices_152) then 2 else
  if p.val = (true, vertices_280) then 3 else
  if p.val = (true, vertices_536) then 4 else
  if p.val = (true, vertices_648) then 5 else
  if p.val = (true, vertices_176) then 6 else
  if p.val = (true, vertices_560) then 7 else
  if p.val = (true, vertices_592) then 8 else
  if p.val = (true, vertices_400) then 9 else
  if p.val = (true, vertices_672) then 10 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_138), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_548), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_152), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_280), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_536), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_648), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_176), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_560), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_592), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_400), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_672), by decide +kernel⟩
  | 11 => Sum.inl 0
  | 12 => Sum.inr ⟨(false, vertices_647), by decide +kernel⟩
  | 13 => Sum.inr ⟨(false, vertices_779), by decide +kernel⟩
  | 14 => Sum.inr ⟨(false, vertices_419), by decide +kernel⟩
  | 15 => Sum.inl 1
  | 16 => Sum.inr ⟨(false, vertices_229), by decide +kernel⟩
  | 17 => Sum.inr ⟨(false, vertices_837), by decide +kernel⟩
  | 18 => Sum.inl 2
  | 19 => Sum.inl 3
  | 20 => Sum.inr ⟨(false, vertices_369), by decide +kernel⟩
  | 21 => Sum.inl 4
  | 22 => Sum.inl 5
  | 23 => Sum.inl 6
  | 24 => Sum.inl 7
  | 25 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row 0 0 2 3 6 7 410
cert_row 1 1 3 4 5 8 628
cert_row 2 4 2 3 6 8 696
cert_row 3 2 3 5 7 8 856
cert_rows
cert_pivot_2 0 1 4 2
cert_heightProof 4
cert_coverFacet 0 410
cert_cover_3 0 0 0 2 3 6
cert_coverFacet 1 650
cert_cover_4 1 0 2 6 8
cert_coverFacet 2 628
cert_cover_3 2 1 1 3 4 5
cert_coverFacet 3 676
cert_cover_4 3 1 4 6 8
cert_coverFacet 4 696
cert_cover_3 4 2 2 3 4 6
cert_coverFacet 5 856
cert_cover_3 5 2 3 3 5 7
cert_coverFacet 6 432
cert_cover_4 6 3 4 6 7
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_005

end
end BundlePart7

section BundlePart8
/- Source: ProjectionCertificates/P0_006.lean -/





@[expose] public section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_006

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
open _root_.Nonrational.SharedProjectionVertexSets

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_299, vertices_653, vertices_213, vertices_613, vertices_409, vertices_553, vertices_369, vertices_618, vertices_906, vertices_850, vertices_354, vertices_596, vertices_916] (by decide +kernel)
  polygons := literalFinset [vertices_69, vertices_133, vertices_517, vertices_41, vertices_137, vertices_265, vertices_521, vertices_81, vertices_145, vertices_273, vertices_97, vertices_289, vertices_545, vertices_42, vertices_266, vertices_522, vertices_98, vertices_290, vertices_322, vertices_578, vertices_770, vertices_84, vertices_148, vertices_532, vertices_580, vertices_644, vertices_552, vertices_392, vertices_648, vertices_336, vertices_592, vertices_400, vertices_784, vertices_352, vertices_608, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_299), (false, vertices_653), (false, vertices_213), (false, vertices_613), (false, vertices_409), (false, vertices_553), (false, vertices_369), (true, vertices_522), (true, vertices_98), (true, vertices_322), (true, vertices_578), (true, vertices_770), (true, vertices_532), (true, vertices_592), (true, vertices_784), (true, vertices_896)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 10 12 16 18 20 21 22 23 24
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_299) then 11 else
  if p.val = (false, vertices_653) then 13 else
  if p.val = (false, vertices_213) then 14 else
  if p.val = (false, vertices_613) then 15 else
  if p.val = (false, vertices_409) then 17 else
  if p.val = (false, vertices_553) then 9 else
  if p.val = (false, vertices_369) then 19 else
  if p.val = (true, vertices_522) then 0 else
  if p.val = (true, vertices_98) then 1 else
  if p.val = (true, vertices_322) then 2 else
  if p.val = (true, vertices_578) then 3 else
  if p.val = (true, vertices_770) then 4 else
  if p.val = (true, vertices_532) then 5 else
  if p.val = (true, vertices_592) then 6 else
  if p.val = (true, vertices_784) then 7 else
  if p.val = (true, vertices_896) then 8 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_522), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_98), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_322), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_578), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_770), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_532), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_592), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_784), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_896), by decide +kernel⟩
  | 9 => Sum.inr ⟨(false, vertices_553), by decide +kernel⟩
  | 10 => Sum.inl 0
  | 11 => Sum.inr ⟨(false, vertices_299), by decide +kernel⟩
  | 12 => Sum.inl 1
  | 13 => Sum.inr ⟨(false, vertices_653), by decide +kernel⟩
  | 14 => Sum.inr ⟨(false, vertices_213), by decide +kernel⟩
  | 15 => Sum.inr ⟨(false, vertices_613), by decide +kernel⟩
  | 16 => Sum.inl 2
  | 17 => Sum.inr ⟨(false, vertices_409), by decide +kernel⟩
  | 18 => Sum.inl 3
  | 19 => Sum.inr ⟨(false, vertices_369), by decide +kernel⟩
  | 20 => Sum.inl 4
  | 21 => Sum.inl 5
  | 22 => Sum.inl 6
  | 23 => Sum.inl 7
  | 24 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row 0 4 0 2 5 8 618
cert_row 1 2 0 6 7 8 906
cert_row 2 0 3 5 7 8 850
cert_row 3 1 3 6 7 8 916
cert_rows
cert_pivot_2 4 2 0 1
cert_heightProof 4
cert_coverFacet 0 618
cert_cover_3 0 0 0 2 4 5
cert_coverFacet 1 906
cert_cover_3 1 0 1 2 6 7
cert_coverFacet 2 850
cert_cover_3 2 0 2 3 5 7
cert_coverFacet 3 354
cert_cover_4 3 0 4 5 7
cert_coverFacet 4 596
cert_cover_4 4 1 3 5 8
cert_coverFacet 5 916
cert_cover_3 5 1 3 3 6 7
cert_coveringFacets
cert_coveringProof_6
cert_certificate 4 6
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_006

end
end BundlePart8

section BundlePart9
/- Source: ProjectionCertificates/P0_007.lean -/





@[expose] public section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_007

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
open _root_.Nonrational.SharedProjectionVertexSets

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_647, vertices_781, vertices_421, vertices_313, vertices_601, vertices_689, vertices_454, vertices_774, vertices_842, vertices_722, vertices_120, vertices_488, vertices_240] (by decide +kernel)
  polygons := literalFinset [vertices_133, vertices_261, vertices_517, vertices_25, vertices_265, vertices_521, vertices_49, vertices_529, vertices_161, vertices_289, vertices_641, vertices_134, vertices_262, vertices_518, vertices_194, vertices_322, vertices_578, vertices_642, vertices_770, vertices_388, vertices_772, vertices_56, vertices_88, vertices_104, vertices_296, vertices_328, vertices_584, vertices_776, vertices_112, vertices_176, vertices_208, vertices_592, vertices_656, vertices_224, vertices_416, vertices_448] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_647), (false, vertices_781), (false, vertices_421), (false, vertices_313), (false, vertices_601), (false, vertices_689), (true, vertices_262), (true, vertices_194), (true, vertices_322), (true, vertices_578), (true, vertices_770), (true, vertices_104), (true, vertices_328), (true, vertices_112), (true, vertices_208), (true, vertices_224), (true, vertices_448)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 11 13 16 19 21 22 23 24 25
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_647) then 12 else
  if p.val = (false, vertices_781) then 14 else
  if p.val = (false, vertices_421) then 15 else
  if p.val = (false, vertices_313) then 17 else
  if p.val = (false, vertices_601) then 18 else
  if p.val = (false, vertices_689) then 20 else
  if p.val = (true, vertices_262) then 0 else
  if p.val = (true, vertices_194) then 1 else
  if p.val = (true, vertices_322) then 2 else
  if p.val = (true, vertices_578) then 3 else
  if p.val = (true, vertices_770) then 4 else
  if p.val = (true, vertices_104) then 5 else
  if p.val = (true, vertices_328) then 6 else
  if p.val = (true, vertices_112) then 7 else
  if p.val = (true, vertices_208) then 8 else
  if p.val = (true, vertices_224) then 9 else
  if p.val = (true, vertices_448) then 10 else
  0
cert_priority
cert_nodeAtPriority_59 0 262 1 194 2 322 578 770 104 328 112 208 224 448 647 781 421 313 601 689
cert_priority_injective
cert_incidenceProof
cert_row 0 1 0 5 6 7 454
cert_row 1 3 0 5 6 8 722
cert_row 2 0 2 5 7 8 842
cert_row 3 2 4 5 6 7 488
cert_rows
cert_pivot_2 1 3 0 2
cert_heightProof 4
cert_coverFacet 0 454
cert_cover_3 0 0 0 1 5 6
cert_coverFacet 1 774
cert_cover_4 1 0 1 7 8
cert_coverFacet 2 842
cert_cover_3 2 0 2 2 5 7
cert_coverFacet 3 722
cert_cover_3 3 0 1 3 5 6
cert_coverFacet 4 120
cert_cover_4 4 2 3 4 5
cert_coverFacet 5 488
cert_cover_3 5 2 3 4 5 6
cert_coverFacet 6 240
cert_cover_4 6 3 4 5 6
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_007

end
end BundlePart9

section BundlePart10
/- Source: ProjectionCertificates/P0_008.lean -/





@[expose] public section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_008

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
open _root_.Nonrational.SharedProjectionVertexSets

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_647, vertices_779, vertices_419, vertices_229, vertices_837, vertices_369, vertices_666, vertices_394, vertices_628, vertices_676, vertices_440, vertices_856, vertices_688] (by decide +kernel)
  polygons := literalFinset [vertices_131, vertices_259, vertices_515, vertices_69, vertices_133, vertices_517, vertices_97, vertices_161, vertices_289, vertices_321, vertices_769, vertices_138, vertices_266, vertices_522, vertices_386, vertices_642, vertices_100, vertices_164, vertices_548, vertices_580, vertices_644, vertices_152, vertices_280, vertices_536, vertices_392, vertices_776, vertices_112, vertices_176, vertices_304, vertices_560, vertices_336, vertices_592, vertices_656, vertices_416, vertices_672, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_647), (false, vertices_779), (false, vertices_419), (false, vertices_229), (false, vertices_837), (false, vertices_369), (true, vertices_138), (true, vertices_548), (true, vertices_152), (true, vertices_280), (true, vertices_536), (true, vertices_392), (true, vertices_176), (true, vertices_560), (true, vertices_592), (true, vertices_656), (true, vertices_672)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 11 15 18 19 21 22 23 24 25
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_647) then 12 else
  if p.val = (false, vertices_779) then 13 else
  if p.val = (false, vertices_419) then 14 else
  if p.val = (false, vertices_229) then 16 else
  if p.val = (false, vertices_837) then 17 else
  if p.val = (false, vertices_369) then 20 else
  if p.val = (true, vertices_138) then 0 else
  if p.val = (true, vertices_548) then 1 else
  if p.val = (true, vertices_152) then 2 else
  if p.val = (true, vertices_280) then 3 else
  if p.val = (true, vertices_536) then 4 else
  if p.val = (true, vertices_392) then 5 else
  if p.val = (true, vertices_176) then 6 else
  if p.val = (true, vertices_560) then 7 else
  if p.val = (true, vertices_592) then 8 else
  if p.val = (true, vertices_656) then 9 else
  if p.val = (true, vertices_672) then 10 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_138), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_548), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_152), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_280), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_536), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_392), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_176), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_560), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_592), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_656), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_672), by decide +kernel⟩
  | 11 => Sum.inl 0
  | 12 => Sum.inr ⟨(false, vertices_647), by decide +kernel⟩
  | 13 => Sum.inr ⟨(false, vertices_779), by decide +kernel⟩
  | 14 => Sum.inr ⟨(false, vertices_419), by decide +kernel⟩
  | 15 => Sum.inl 1
  | 16 => Sum.inr ⟨(false, vertices_229), by decide +kernel⟩
  | 17 => Sum.inr ⟨(false, vertices_837), by decide +kernel⟩
  | 18 => Sum.inl 2
  | 19 => Sum.inl 3
  | 20 => Sum.inr ⟨(false, vertices_369), by decide +kernel⟩
  | 21 => Sum.inl 4
  | 22 => Sum.inl 5
  | 23 => Sum.inl 6
  | 24 => Sum.inl 7
  | 25 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row 0 0 2 3 6 8 666
cert_row 1 1 3 4 5 8 628
cert_row 2 4 2 3 6 7 440
cert_row 3 2 3 5 7 8 856
cert_rows
cert_pivot_2 0 1 4 2
cert_heightProof 4
cert_coverFacet 0 666
cert_cover_3 0 0 0 2 3 6
cert_coverFacet 1 394
cert_cover_4 1 0 2 6 7
cert_coverFacet 2 628
cert_cover_3 2 1 1 3 4 5
cert_coverFacet 3 676
cert_cover_4 3 1 4 6 8
cert_coverFacet 4 440
cert_cover_3 4 2 2 3 4 6
cert_coverFacet 5 856
cert_cover_3 5 2 3 3 5 7
cert_coverFacet 6 688
cert_cover_4 6 3 4 6 8
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_008

end
end BundlePart10

section BundlePart11
/- Source: ProjectionCertificates/P0_009.lean -/





@[expose] public section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_009

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
open _root_.Nonrational.SharedProjectionVertexSets

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_391, vertices_651, vertices_563, vertices_339, vertices_205, vertices_325, vertices_121, vertices_553, vertices_914, vertices_620, vertices_908, vertices_852, vertices_624] (by decide +kernel)
  polygons := literalFinset [vertices_19, vertices_131, vertices_259, vertices_515, vertices_69, vertices_133, vertices_261, vertices_41, vertices_73, vertices_137, vertices_521, vertices_49, vertices_81, vertices_545, vertices_321, vertices_274, vertices_530, vertices_386, vertices_642, vertices_76, vertices_140, vertices_524, vertices_324, vertices_580, vertices_388, vertices_772, vertices_104, vertices_552, vertices_648, vertices_112, vertices_560, vertices_336, vertices_592, vertices_784, vertices_608, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_391), (false, vertices_651), (false, vertices_563), (false, vertices_339), (false, vertices_205), (false, vertices_325), (false, vertices_121), (false, vertices_553), (true, vertices_524), (true, vertices_580), (true, vertices_772), (true, vertices_592), (true, vertices_784), (true, vertices_608), (true, vertices_896)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 12 9 16 18 19 20 21 22 23
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_391) then 10 else
  if p.val = (false, vertices_651) then 13 else
  if p.val = (false, vertices_563) then 14 else
  if p.val = (false, vertices_339) then 15 else
  if p.val = (false, vertices_205) then 11 else
  if p.val = (false, vertices_325) then 7 else
  if p.val = (false, vertices_121) then 17 else
  if p.val = (false, vertices_553) then 8 else
  if p.val = (true, vertices_524) then 0 else
  if p.val = (true, vertices_580) then 1 else
  if p.val = (true, vertices_772) then 2 else
  if p.val = (true, vertices_592) then 3 else
  if p.val = (true, vertices_784) then 4 else
  if p.val = (true, vertices_608) then 5 else
  if p.val = (true, vertices_896) then 6 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_524), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_580), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_772), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_592), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_784), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_608), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_896), by decide +kernel⟩
  | 7 => Sum.inr ⟨(false, vertices_325), by decide +kernel⟩
  | 8 => Sum.inr ⟨(false, vertices_553), by decide +kernel⟩
  | 9 => Sum.inl 1
  | 10 => Sum.inr ⟨(false, vertices_391), by decide +kernel⟩
  | 11 => Sum.inr ⟨(false, vertices_205), by decide +kernel⟩
  | 12 => Sum.inl 0
  | 13 => Sum.inr ⟨(false, vertices_651), by decide +kernel⟩
  | 14 => Sum.inr ⟨(false, vertices_563), by decide +kernel⟩
  | 15 => Sum.inr ⟨(false, vertices_339), by decide +kernel⟩
  | 16 => Sum.inl 2
  | 17 => Sum.inr ⟨(false, vertices_121), by decide +kernel⟩
  | 18 => Sum.inl 3
  | 19 => Sum.inl 4
  | 20 => Sum.inl 5
  | 21 => Sum.inl 6
  | 22 => Sum.inl 7
  | 23 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row 0 0 3 6 7 8 914
cert_row 1 4 1 2 5 8 620
cert_row 2 2 1 6 7 8 908
cert_row 3 1 3 5 7 8 852
cert_rows
cert_pivot_2 0 4 2 1
cert_heightProof 4
cert_coverFacet 0 914
cert_cover_3 0 0 0 3 6 7
cert_coverFacet 1 620
cert_cover_3 1 1 1 2 4 5
cert_coverFacet 2 908
cert_cover_3 2 1 2 2 6 7
cert_coverFacet 3 852
cert_cover_3 3 1 3 3 5 7
cert_coverFacet 4 624
cert_cover_4 4 3 4 5 8
cert_coveringFacets_3
cert_coveringProof_7
cert_certificate 4 5
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_009

end
end BundlePart11

section BundlePart12
/- Source: ProjectionCertificates/P0_010.lean -/





@[expose] public section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_010

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
open _root_.Nonrational.SharedProjectionVertexSets

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_647, vertices_779, vertices_307, vertices_227, vertices_205, vertices_525, vertices_345, vertices_113, vertices_930, vertices_604, vertices_740, vertices_824, vertices_624] (by decide +kernel)
  polygons := literalFinset [vertices_35, vertices_131, vertices_259, vertices_515, vertices_13, vertices_133, vertices_517, vertices_73, vertices_265, vertices_521, vertices_49, vertices_81, vertices_273, vertices_97, vertices_193, vertices_162, vertices_290, vertices_642, vertices_770, vertices_76, vertices_524, vertices_196, vertices_580, vertices_644, vertices_88, vertices_280, vertices_536, vertices_776, vertices_112, vertices_304, vertices_560, vertices_592, vertices_224, vertices_608, vertices_672, vertices_800] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_647), (false, vertices_779), (false, vertices_307), (false, vertices_227), (false, vertices_205), (false, vertices_525), (false, vertices_345), (false, vertices_113), (true, vertices_580), (true, vertices_536), (true, vertices_560), (true, vertices_592), (true, vertices_608), (true, vertices_672), (true, vertices_800)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 12 9 16 18 19 20 21 22 23
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_647) then 10 else
  if p.val = (false, vertices_779) then 13 else
  if p.val = (false, vertices_307) then 14 else
  if p.val = (false, vertices_227) then 15 else
  if p.val = (false, vertices_205) then 11 else
  if p.val = (false, vertices_525) then 7 else
  if p.val = (false, vertices_345) then 17 else
  if p.val = (false, vertices_113) then 8 else
  if p.val = (true, vertices_580) then 0 else
  if p.val = (true, vertices_536) then 1 else
  if p.val = (true, vertices_560) then 2 else
  if p.val = (true, vertices_592) then 3 else
  if p.val = (true, vertices_608) then 4 else
  if p.val = (true, vertices_672) then 5 else
  if p.val = (true, vertices_800) then 6 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_580), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_536), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_560), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_592), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_608), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_672), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_800), by decide +kernel⟩
  | 7 => Sum.inr ⟨(false, vertices_525), by decide +kernel⟩
  | 8 => Sum.inr ⟨(false, vertices_113), by decide +kernel⟩
  | 9 => Sum.inl 1
  | 10 => Sum.inr ⟨(false, vertices_647), by decide +kernel⟩
  | 11 => Sum.inr ⟨(false, vertices_205), by decide +kernel⟩
  | 12 => Sum.inl 0
  | 13 => Sum.inr ⟨(false, vertices_779), by decide +kernel⟩
  | 14 => Sum.inr ⟨(false, vertices_307), by decide +kernel⟩
  | 15 => Sum.inr ⟨(false, vertices_227), by decide +kernel⟩
  | 16 => Sum.inl 2
  | 17 => Sum.inr ⟨(false, vertices_345), by decide +kernel⟩
  | 18 => Sum.inl 3
  | 19 => Sum.inl 4
  | 20 => Sum.inl 5
  | 21 => Sum.inl 6
  | 22 => Sum.inl 7
  | 23 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row 0 0 4 6 7 8 930
cert_row 1 6 1 4 5 8 740
cert_row 2 1 2 3 5 8 604
cert_row 3 2 3 4 7 8 824
cert_rows
cert_pivot_2 0 6 1 2
cert_heightProof 4
cert_coverFacet 0 930
cert_cover_3 0 0 0 4 6 7
cert_coverFacet 1 604
cert_cover_3 1 1 2 2 3 5
cert_coverFacet 2 740
cert_cover_3 2 1 1 4 5 6
cert_coverFacet 3 824
cert_cover_3 3 2 3 3 4 7
cert_coverFacet 4 624
cert_cover_4 4 3 4 5 8
cert_coveringFacets_3
cert_coveringProof_7
cert_certificate 4 5
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_010

end
end BundlePart12

section BundlePart13
/- Source: ProjectionCertificates/P0_011.lean -/





@[expose] public section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_011

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
open _root_.Nonrational.SharedProjectionVertexSets

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_551, vertices_587, vertices_227, vertices_301, vertices_525, vertices_457, vertices_433, vertices_690, vertices_962, vertices_844, vertices_308, vertices_564, vertices_916] (by decide +kernel)
  polygons := literalFinset [vertices_35, vertices_67, vertices_515, vertices_13, vertices_37, vertices_517, vertices_73, vertices_265, vertices_521, vertices_161, vertices_289, vertices_193, vertices_385, vertices_162, vertices_546, vertices_194, vertices_578, vertices_642, vertices_268, vertices_524, vertices_52, vertices_276, vertices_532, vertices_292, vertices_548, vertices_772, vertices_328, vertices_584, vertices_176, vertices_304, vertices_560, vertices_400, vertices_656, vertices_448, vertices_832, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_551), (false, vertices_587), (false, vertices_227), (false, vertices_301), (false, vertices_525), (false, vertices_457), (false, vertices_433), (true, vertices_642), (true, vertices_52), (true, vertices_276), (true, vertices_532), (true, vertices_772), (true, vertices_560), (true, vertices_656), (true, vertices_832), (true, vertices_896)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 10 14 16 18 20 21 22 23 24
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_551) then 11 else
  if p.val = (false, vertices_587) then 12 else
  if p.val = (false, vertices_227) then 13 else
  if p.val = (false, vertices_301) then 15 else
  if p.val = (false, vertices_525) then 9 else
  if p.val = (false, vertices_457) then 17 else
  if p.val = (false, vertices_433) then 19 else
  if p.val = (true, vertices_642) then 0 else
  if p.val = (true, vertices_52) then 1 else
  if p.val = (true, vertices_276) then 2 else
  if p.val = (true, vertices_532) then 3 else
  if p.val = (true, vertices_772) then 4 else
  if p.val = (true, vertices_560) then 5 else
  if p.val = (true, vertices_656) then 6 else
  if p.val = (true, vertices_832) then 7 else
  if p.val = (true, vertices_896) then 8 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_642), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_52), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_276), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_532), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_772), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_560), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_656), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_832), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_896), by decide +kernel⟩
  | 9 => Sum.inr ⟨(false, vertices_525), by decide +kernel⟩
  | 10 => Sum.inl 0
  | 11 => Sum.inr ⟨(false, vertices_551), by decide +kernel⟩
  | 12 => Sum.inr ⟨(false, vertices_587), by decide +kernel⟩
  | 13 => Sum.inr ⟨(false, vertices_227), by decide +kernel⟩
  | 14 => Sum.inl 1
  | 15 => Sum.inr ⟨(false, vertices_301), by decide +kernel⟩
  | 16 => Sum.inl 2
  | 17 => Sum.inr ⟨(false, vertices_457), by decide +kernel⟩
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
cert_row 0 4 0 3 6 8 690
cert_row 1 0 5 6 7 8 962
cert_row 2 2 1 5 7 8 844
cert_row 3 1 3 6 7 8 916
cert_rows
cert_pivot_2 4 0 2 1
cert_heightProof 4
cert_coverFacet 0 690
cert_cover_3 0 0 0 3 4 6
cert_coverFacet 1 962
cert_cover_3 1 0 1 5 6 7
cert_coverFacet 2 844
cert_cover_3 2 1 2 2 5 7
cert_coverFacet 3 308
cert_cover_4 3 1 3 4 7
cert_coverFacet 4 564
cert_cover_4 4 1 3 4 8
cert_coverFacet 5 916
cert_cover_3 5 1 3 3 6 7
cert_coveringFacets
cert_coveringProof_6
cert_certificate 4 6
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_011

end
end BundlePart13

section BundlePart14
/- Source: ProjectionCertificates/P0_012.lean -/





@[expose] public section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_012

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
open _root_.Nonrational.SharedProjectionVertexSets

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_527, vertices_203, vertices_675, vertices_333, vertices_309, vertices_549, vertices_241, vertices_337, vertices_586, vertices_722, vertices_812, vertices_856, vertices_944] (by decide +kernel)
  polygons := literalFinset [vertices_11, vertices_131, vertices_515, vertices_13, vertices_37, vertices_261, vertices_517, vertices_73, vertices_49, vertices_81, vertices_273, vertices_161, vertices_545, vertices_193, vertices_321, vertices_74, vertices_522, vertices_194, vertices_578, vertices_642, vertices_268, vertices_524, vertices_292, vertices_548, vertices_328, vertices_584, vertices_776, vertices_176, vertices_304, vertices_208, vertices_336, vertices_592, vertices_656, vertices_784, vertices_672, vertices_800] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_527), (false, vertices_203), (false, vertices_675), (false, vertices_333), (false, vertices_309), (false, vertices_549), (false, vertices_241), (false, vertices_337), (true, vertices_578), (true, vertices_584), (true, vertices_776), (true, vertices_592), (true, vertices_656), (true, vertices_784), (true, vertices_800)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 9 13 16 17 19 20 21 22 23
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_527) then 10 else
  if p.val = (false, vertices_203) then 11 else
  if p.val = (false, vertices_675) then 12 else
  if p.val = (false, vertices_333) then 14 else
  if p.val = (false, vertices_309) then 15 else
  if p.val = (false, vertices_549) then 7 else
  if p.val = (false, vertices_241) then 18 else
  if p.val = (false, vertices_337) then 8 else
  if p.val = (true, vertices_578) then 0 else
  if p.val = (true, vertices_584) then 1 else
  if p.val = (true, vertices_776) then 2 else
  if p.val = (true, vertices_592) then 3 else
  if p.val = (true, vertices_656) then 4 else
  if p.val = (true, vertices_784) then 5 else
  if p.val = (true, vertices_800) then 6 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_578), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_584), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_776), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_592), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_656), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_784), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_800), by decide +kernel⟩
  | 7 => Sum.inr ⟨(false, vertices_549), by decide +kernel⟩
  | 8 => Sum.inr ⟨(false, vertices_337), by decide +kernel⟩
  | 9 => Sum.inl 0
  | 10 => Sum.inr ⟨(false, vertices_527), by decide +kernel⟩
  | 11 => Sum.inr ⟨(false, vertices_203), by decide +kernel⟩
  | 12 => Sum.inr ⟨(false, vertices_675), by decide +kernel⟩
  | 13 => Sum.inl 1
  | 14 => Sum.inr ⟨(false, vertices_333), by decide +kernel⟩
  | 15 => Sum.inr ⟨(false, vertices_309), by decide +kernel⟩
  | 16 => Sum.inl 2
  | 17 => Sum.inl 3
  | 18 => Sum.inr ⟨(false, vertices_241), by decide +kernel⟩
  | 19 => Sum.inl 4
  | 20 => Sum.inl 5
  | 21 => Sum.inl 6
  | 22 => Sum.inl 7
  | 23 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row 0 0 3 5 6 8 722
cert_row 1 1 2 4 7 8 812
cert_row 2 2 3 5 7 8 856
cert_row 3 3 4 6 7 8 944
cert_rows
cert_pivot_2 0 1 2 3
cert_heightProof 4
cert_coverFacet 0 586
cert_cover_4 0 0 2 5 8
cert_coverFacet 1 722
cert_cover_3 1 0 0 3 5 6
cert_coverFacet 2 812
cert_cover_3 2 1 1 2 4 7
cert_coverFacet 3 856
cert_cover_3 3 2 2 3 5 7
cert_coverFacet 4 944
cert_cover_3 4 3 3 4 6 7
cert_coveringFacets_3
cert_coveringProof_7
cert_certificate 4 5
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_012

end
end BundlePart14

section BundlePart15
/- Source: ProjectionCertificates/P0_013.lean -/





@[expose] public section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_013

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
open _root_.Nonrational.SharedProjectionVertexSets

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_555, vertices_597, vertices_405, vertices_677, vertices_793, vertices_425, vertices_710, vertices_362, vertices_778, vertices_850, vertices_226, vertices_674, vertices_212, vertices_496] (by decide +kernel)
  polygons := literalFinset [vertices_21, vertices_133, vertices_517, vertices_41, vertices_265, vertices_521, vertices_273, vertices_529, vertices_161, vertices_545, vertices_385, vertices_42, vertices_266, vertices_522, vertices_98, vertices_162, vertices_546, vertices_194, vertices_322, vertices_578, vertices_642, vertices_770, vertices_84, vertices_148, vertices_196, vertices_580, vertices_644, vertices_296, vertices_776, vertices_208, vertices_336, vertices_592, vertices_400, vertices_784, vertices_224, vertices_352, vertices_416, vertices_672] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_555), (false, vertices_597), (false, vertices_405), (false, vertices_677), (false, vertices_793), (false, vertices_425), (true, vertices_266), (true, vertices_98), (true, vertices_162), (true, vertices_194), (true, vertices_322), (true, vertices_578), (true, vertices_642), (true, vertices_770), (true, vertices_196), (true, vertices_208), (true, vertices_336), (true, vertices_224), (true, vertices_352)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 13 15 19 22 23 24 25 26 27
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_555) then 14 else
  if p.val = (false, vertices_597) then 16 else
  if p.val = (false, vertices_405) then 17 else
  if p.val = (false, vertices_677) then 18 else
  if p.val = (false, vertices_793) then 20 else
  if p.val = (false, vertices_425) then 21 else
  if p.val = (true, vertices_266) then 0 else
  if p.val = (true, vertices_98) then 1 else
  if p.val = (true, vertices_162) then 2 else
  if p.val = (true, vertices_194) then 3 else
  if p.val = (true, vertices_322) then 4 else
  if p.val = (true, vertices_578) then 5 else
  if p.val = (true, vertices_642) then 6 else
  if p.val = (true, vertices_770) then 7 else
  if p.val = (true, vertices_196) then 8 else
  if p.val = (true, vertices_208) then 9 else
  if p.val = (true, vertices_336) then 10 else
  if p.val = (true, vertices_224) then 11 else
  if p.val = (true, vertices_352) then 12 else
  0
cert_priority
cert_nodeAtPriority 0 266 1 98 2 162 194 322 578 642 770 196 208 336 224 352 555 597 405 677 793 425
cert_priority_injective
cert_incidenceProof
cert_row 0 1 0 5 6 8 710
cert_row 1 2 0 4 5 7 362
cert_row 2 0 3 5 7 8 850
cert_row 3 3 4 5 6 7 496
cert_rows
cert_pivot_2 1 2 0 3
cert_heightProof 4
cert_coverFacet 0 710
cert_cover_3 0 0 0 1 5 6
cert_coverFacet 1 362
cert_cover_3 1 0 1 2 4 5
cert_coverFacet 2 778
cert_cover_4 2 0 2 7 8
cert_coverFacet 3 850
cert_cover_3 3 0 2 3 5 7
cert_coverFacet 4 226
cert_cover_4 4 0 4 5 6
cert_coverFacet 5 674
cert_cover_4 5 0 4 6 8
cert_coverFacet 6 212
cert_cover_4 6 1 3 5 6
cert_coverFacet 7 496
cert_cover_3 7 3 3 4 5 6
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_013

end
end BundlePart15

section BundlePart16
/- Source: ProjectionCertificates/P0_014.lean -/





@[expose] public section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_014

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
open _root_.Nonrational.SharedProjectionVertexSets

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_707, vertices_285, vertices_589, vertices_453, vertices_665, vertices_433, vertices_570, vertices_242, vertices_658, vertices_866, vertices_812, vertices_836, vertices_312, vertices_480] (by decide +kernel)
  polygons := literalFinset [vertices_13, vertices_69, vertices_261, vertices_25, vertices_521, vertices_145, vertices_273, vertices_193, vertices_577, vertices_385, vertices_641, vertices_50, vertices_146, vertices_530, vertices_98, vertices_546, vertices_194, vertices_578, vertices_642, vertices_268, vertices_524, vertices_324, vertices_580, vertices_772, vertices_56, vertices_280, vertices_536, vertices_296, vertices_552, vertices_176, vertices_304, vertices_656, vertices_224, vertices_352, vertices_416, vertices_800, vertices_448, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_707), (false, vertices_285), (false, vertices_589), (false, vertices_453), (false, vertices_665), (false, vertices_433), (true, vertices_50), (true, vertices_146), (true, vertices_530), (true, vertices_98), (true, vertices_546), (true, vertices_772), (true, vertices_56), (true, vertices_296), (true, vertices_552), (true, vertices_224), (true, vertices_352), (true, vertices_800), (true, vertices_832)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 13 15 19 21 23 24 25 26 27
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_707) then 14 else
  if p.val = (false, vertices_285) then 16 else
  if p.val = (false, vertices_589) then 17 else
  if p.val = (false, vertices_453) then 18 else
  if p.val = (false, vertices_665) then 20 else
  if p.val = (false, vertices_433) then 22 else
  if p.val = (true, vertices_50) then 0 else
  if p.val = (true, vertices_146) then 1 else
  if p.val = (true, vertices_530) then 2 else
  if p.val = (true, vertices_98) then 3 else
  if p.val = (true, vertices_546) then 4 else
  if p.val = (true, vertices_772) then 5 else
  if p.val = (true, vertices_56) then 6 else
  if p.val = (true, vertices_296) then 7 else
  if p.val = (true, vertices_552) then 8 else
  if p.val = (true, vertices_224) then 9 else
  if p.val = (true, vertices_352) then 10 else
  if p.val = (true, vertices_800) then 11 else
  if p.val = (true, vertices_832) then 12 else
  0
cert_priority
cert_nodeAtPriority_11 50 146 530 98 546 772 56 296 552 224 352 800 832 707 285 589 453 665 433
cert_priority_injective
cert_incidenceProof
cert_row 0 6 0 3 4 5 242
cert_row 1 3 0 2 4 8 570
cert_row 2 0 4 5 7 8 866
cert_row 3 1 2 4 7 8 812
cert_rows
cert_pivot_2 6 3 0 1
cert_heightProof 4
cert_coverFacet 0 570
cert_cover_3 0 0 1 2 3 4
cert_coverFacet 1 242
cert_cover_3 1 0 0 3 4 5
cert_coverFacet 2 658
cert_cover_4 2 0 3 6 8
cert_coverFacet 3 866
cert_cover_3 3 0 2 4 5 7
cert_coverFacet 4 812
cert_cover_3 4 1 3 2 4 7
cert_coverFacet 5 836
cert_cover_4 5 1 5 7 8
cert_coverFacet 6 312
cert_cover_4 6 2 3 4 7
cert_coverFacet 7 480
cert_cover_4 7 4 5 6 7
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_014

end
end BundlePart16

section BundlePart17
/- Source: ProjectionCertificates/P0_015.lean -/





@[expose] public section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_015

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
open _root_.Nonrational.SharedProjectionVertexSets

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_595, vertices_541, vertices_173, vertices_213, vertices_617, vertices_481, vertices_790, vertices_810, vertices_370, vertices_610, vertices_908, vertices_404, vertices_424, vertices_464] (by decide +kernel)
  polygons := literalFinset [vertices_13, vertices_21, vertices_133, vertices_41, vertices_521, vertices_81, vertices_529, vertices_97, vertices_161, vertices_193, vertices_577, vertices_82, vertices_274, vertices_530, vertices_98, vertices_290, vertices_546, vertices_578, vertices_770, vertices_140, vertices_524, vertices_148, vertices_276, vertices_532, vertices_388, vertices_772, vertices_168, vertices_296, vertices_552, vertices_392, vertices_776, vertices_208, vertices_336, vertices_400, vertices_352, vertices_608, vertices_416, vertices_448] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_595), (false, vertices_541), (false, vertices_173), (false, vertices_213), (false, vertices_617), (false, vertices_481), (true, vertices_274), (true, vertices_98), (true, vertices_290), (true, vertices_546), (true, vertices_770), (true, vertices_276), (true, vertices_388), (true, vertices_772), (true, vertices_296), (true, vertices_392), (true, vertices_776), (true, vertices_336), (true, vertices_400)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 13 15 19 21 22 24 25 26 27
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_595) then 14 else
  if p.val = (false, vertices_541) then 16 else
  if p.val = (false, vertices_173) then 17 else
  if p.val = (false, vertices_213) then 18 else
  if p.val = (false, vertices_617) then 20 else
  if p.val = (false, vertices_481) then 23 else
  if p.val = (true, vertices_274) then 0 else
  if p.val = (true, vertices_98) then 1 else
  if p.val = (true, vertices_290) then 2 else
  if p.val = (true, vertices_546) then 3 else
  if p.val = (true, vertices_770) then 4 else
  if p.val = (true, vertices_276) then 5 else
  if p.val = (true, vertices_388) then 6 else
  if p.val = (true, vertices_772) then 7 else
  if p.val = (true, vertices_296) then 8 else
  if p.val = (true, vertices_392) then 9 else
  if p.val = (true, vertices_776) then 10 else
  if p.val = (true, vertices_336) then 11 else
  if p.val = (true, vertices_400) then 12 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_274), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_98), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_290), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_546), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_770), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_276), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_388), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_772), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_296), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_392), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_776), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_336), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_400), by decide +kernel⟩
  | 13 => Sum.inl 0
  | 14 => Sum.inr ⟨(false, vertices_595), by decide +kernel⟩
  | 15 => Sum.inl 1
  | 16 => Sum.inr ⟨(false, vertices_541), by decide +kernel⟩
  | 17 => Sum.inr ⟨(false, vertices_173), by decide +kernel⟩
  | 18 => Sum.inr ⟨(false, vertices_213), by decide +kernel⟩
  | 19 => Sum.inl 2
  | 20 => Sum.inr ⟨(false, vertices_617), by decide +kernel⟩
  | 21 => Sum.inl 3
  | 22 => Sum.inl 4
  | 23 => Sum.inr ⟨(false, vertices_481), by decide +kernel⟩
  | 24 => Sum.inl 5
  | 25 => Sum.inl 6
  | 26 => Sum.inl 7
  | 27 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row 0 5 0 3 4 7 370
cert_row 1 3 0 1 7 8 790
cert_row 2 0 2 4 7 8 810
cert_row 3 1 2 6 7 8 908
cert_rows
cert_pivot_2 5 3 0 1
cert_heightProof 4
cert_coverFacet 0 790
cert_cover_3 0 0 1 1 3 7
cert_coverFacet 1 810
cert_cover_3 1 0 2 2 4 7
cert_coverFacet 2 370
cert_cover_3 2 0 0 3 4 5
cert_coverFacet 3 610
cert_cover_4 3 0 4 5 8
cert_coverFacet 4 908
cert_cover_3 4 1 3 2 6 7
cert_coverFacet 5 404
cert_cover_4 5 1 3 6 7
cert_coverFacet 6 424
cert_cover_4 6 2 4 6 7
cert_coverFacet 7 464
cert_cover_4 7 3 5 6 7
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_015

end
end BundlePart17

section BundlePart18
/- Source: ProjectionCertificates/P0_016.lean -/





@[expose] public section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_016

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
open _root_.Nonrational.SharedProjectionVertexSets

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_551, vertices_331, vertices_651, vertices_291, vertices_205, vertices_661, vertices_357, vertices_810, vertices_244, vertices_564, vertices_920, vertices_456, vertices_880, vertices_464] (by decide +kernel)
  polygons := literalFinset [vertices_11, vertices_35, vertices_259, vertices_515, vertices_37, vertices_69, vertices_133, vertices_517, vertices_73, vertices_137, vertices_289, vertices_321, vertices_641, vertices_266, vertices_522, vertices_290, vertices_546, vertices_52, vertices_148, vertices_532, vertices_100, vertices_548, vertices_196, vertices_200, vertices_328, vertices_392, vertices_648, vertices_776, vertices_112, vertices_560, vertices_208, vertices_336, vertices_400, vertices_656, vertices_784, vertices_352, vertices_800, vertices_448] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_551), (false, vertices_331), (false, vertices_651), (false, vertices_291), (false, vertices_205), (false, vertices_661), (false, vertices_357), (true, vertices_52), (true, vertices_392), (true, vertices_776), (true, vertices_112), (true, vertices_560), (true, vertices_208), (true, vertices_336), (true, vertices_400), (true, vertices_784), (true, vertices_800), (true, vertices_448)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 12 16 20 21 22 23 24 25 26
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_551) then 13 else
  if p.val = (false, vertices_331) then 14 else
  if p.val = (false, vertices_651) then 15 else
  if p.val = (false, vertices_291) then 11 else
  if p.val = (false, vertices_205) then 17 else
  if p.val = (false, vertices_661) then 18 else
  if p.val = (false, vertices_357) then 19 else
  if p.val = (true, vertices_52) then 0 else
  if p.val = (true, vertices_392) then 1 else
  if p.val = (true, vertices_776) then 2 else
  if p.val = (true, vertices_112) then 3 else
  if p.val = (true, vertices_560) then 4 else
  if p.val = (true, vertices_208) then 5 else
  if p.val = (true, vertices_336) then 6 else
  if p.val = (true, vertices_400) then 7 else
  if p.val = (true, vertices_784) then 8 else
  if p.val = (true, vertices_800) then 9 else
  if p.val = (true, vertices_448) then 10 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_52), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_392), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_776), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_112), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_560), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_208), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_336), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_400), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_784), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_800), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_448), by decide +kernel⟩
  | 11 => Sum.inr ⟨(false, vertices_291), by decide +kernel⟩
  | 12 => Sum.inl 0
  | 13 => Sum.inr ⟨(false, vertices_551), by decide +kernel⟩
  | 14 => Sum.inr ⟨(false, vertices_331), by decide +kernel⟩
  | 15 => Sum.inr ⟨(false, vertices_651), by decide +kernel⟩
  | 16 => Sum.inl 1
  | 17 => Sum.inr ⟨(false, vertices_205), by decide +kernel⟩
  | 18 => Sum.inr ⟨(false, vertices_661), by decide +kernel⟩
  | 19 => Sum.inr ⟨(false, vertices_357), by decide +kernel⟩
  | 20 => Sum.inl 2
  | 21 => Sum.inl 3
  | 22 => Sum.inl 4
  | 23 => Sum.inl 5
  | 24 => Sum.inl 6
  | 25 => Sum.inl 7
  | 26 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row 0 0 2 4 7 8 810
cert_row 1 1 3 4 5 6 244
cert_row 2 2 3 6 7 8 920
cert_row 3 3 4 5 7 8 880
cert_rows
cert_pivot_2 0 1 2 3
cert_heightProof 4
cert_coverFacet 0 810
cert_cover_3 0 0 0 2 4 7
cert_coverFacet 1 244
cert_cover_3 1 1 1 3 4 5
cert_coverFacet 2 564
cert_cover_4 2 1 3 4 8
cert_coverFacet 3 920
cert_cover_3 3 2 2 3 6 7
cert_coverFacet 4 456
cert_cover_4 4 2 5 6 7
cert_coverFacet 5 880
cert_cover_3 5 3 3 4 5 7
cert_coverFacet 6 464
cert_cover_4 6 3 5 6 7
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_016

end
end BundlePart18

section BundlePart19
/- Source: ProjectionCertificates/P0_017.lean -/





@[expose] public section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_017

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
open _root_.Nonrational.SharedProjectionVertexSets

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_803, vertices_93, vertices_781, vertices_613, vertices_313, vertices_241, vertices_710, vertices_906, vertices_434, vertices_226, vertices_610, vertices_668, vertices_212, vertices_408] (by decide +kernel)
  polygons := literalFinset [vertices_13, vertices_69, vertices_517, vertices_25, vertices_265, vertices_49, vertices_81, vertices_97, vertices_289, vertices_545, vertices_769, vertices_98, vertices_162, vertices_290, vertices_546, vertices_194, vertices_578, vertices_386, vertices_642, vertices_770, vertices_28, vertices_524, vertices_84, vertices_148, vertices_196, vertices_580, vertices_644, vertices_152, vertices_280, vertices_392, vertices_648, vertices_776, vertices_176, vertices_304, vertices_208, vertices_400, vertices_224, vertices_608] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_803), (false, vertices_93), (false, vertices_781), (false, vertices_613), (false, vertices_313), (false, vertices_241), (true, vertices_98), (true, vertices_162), (true, vertices_194), (true, vertices_578), (true, vertices_386), (true, vertices_642), (true, vertices_148), (true, vertices_196), (true, vertices_644), (true, vertices_152), (true, vertices_392), (true, vertices_648), (true, vertices_400)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 13 15 19 21 23 24 25 26 27
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_803) then 14 else
  if p.val = (false, vertices_93) then 16 else
  if p.val = (false, vertices_781) then 17 else
  if p.val = (false, vertices_613) then 18 else
  if p.val = (false, vertices_313) then 20 else
  if p.val = (false, vertices_241) then 22 else
  if p.val = (true, vertices_98) then 0 else
  if p.val = (true, vertices_162) then 1 else
  if p.val = (true, vertices_194) then 2 else
  if p.val = (true, vertices_578) then 3 else
  if p.val = (true, vertices_386) then 4 else
  if p.val = (true, vertices_642) then 5 else
  if p.val = (true, vertices_148) then 6 else
  if p.val = (true, vertices_196) then 7 else
  if p.val = (true, vertices_644) then 8 else
  if p.val = (true, vertices_152) then 9 else
  if p.val = (true, vertices_392) then 10 else
  if p.val = (true, vertices_648) then 11 else
  if p.val = (true, vertices_400) then 12 else
  0
cert_priority
cert_nodeAtPriority_11 98 162 194 578 386 642 148 196 644 152 392 648 400 803 93 781 613 313 241
cert_priority_injective
cert_incidenceProof
cert_row 0 5 0 1 6 8 710
cert_row 1 4 0 3 6 7 434
cert_row 2 0 2 6 7 8 906
cert_row 3 1 2 3 6 8 668
cert_rows
cert_pivot_2 5 4 0 1
cert_heightProof 4
cert_coverFacet 0 710
cert_cover_3 0 0 0 1 5 6
cert_coverFacet 1 906
cert_cover_3 1 0 2 2 6 7
cert_coverFacet 2 434
cert_cover_3 2 0 1 3 4 6
cert_coverFacet 3 226
cert_cover_4 3 0 4 5 6
cert_coverFacet 4 610
cert_cover_4 4 0 4 5 8
cert_coverFacet 5 668
cert_cover_3 5 1 3 2 3 6
cert_coverFacet 6 212
cert_cover_4 6 1 3 5 6
cert_coverFacet 7 408
cert_cover_4 7 2 3 6 7
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_017

end
end BundlePart19

section BundlePart20
/- Source: ProjectionCertificates/P0_018.lean -/





@[expose] public section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_018

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
open _root_.Nonrational.SharedProjectionVertexSets

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_339, vertices_659, vertices_611, vertices_677, vertices_361, vertices_433, vertices_790, vertices_842, vertices_412, vertices_620, vertices_172, vertices_780, vertices_660, vertices_424] (by decide +kernel)
  polygons := literalFinset [vertices_19, vertices_67, vertices_515, vertices_145, vertices_273, vertices_97, vertices_161, vertices_289, vertices_545, vertices_321, vertices_641, vertices_274, vertices_530, vertices_322, vertices_578, vertices_770, vertices_44, vertices_140, vertices_268, vertices_524, vertices_148, vertices_276, vertices_532, vertices_164, vertices_548, vertices_644, vertices_772, vertices_104, vertices_168, vertices_296, vertices_328, vertices_584, vertices_392, vertices_776, vertices_400, vertices_656, vertices_608, vertices_416] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_339), (false, vertices_659), (false, vertices_611), (false, vertices_677), (false, vertices_361), (false, vertices_433), (true, vertices_770), (true, vertices_44), (true, vertices_140), (true, vertices_268), (true, vertices_524), (true, vertices_148), (true, vertices_276), (true, vertices_532), (true, vertices_772), (true, vertices_168), (true, vertices_584), (true, vertices_392), (true, vertices_776)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 13 17 19 21 23 24 25 26 27
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_339) then 14 else
  if p.val = (false, vertices_659) then 15 else
  if p.val = (false, vertices_611) then 16 else
  if p.val = (false, vertices_677) then 18 else
  if p.val = (false, vertices_361) then 20 else
  if p.val = (false, vertices_433) then 22 else
  if p.val = (true, vertices_770) then 0 else
  if p.val = (true, vertices_44) then 1 else
  if p.val = (true, vertices_140) then 2 else
  if p.val = (true, vertices_268) then 3 else
  if p.val = (true, vertices_524) then 4 else
  if p.val = (true, vertices_148) then 5 else
  if p.val = (true, vertices_276) then 6 else
  if p.val = (true, vertices_532) then 7 else
  if p.val = (true, vertices_772) then 8 else
  if p.val = (true, vertices_168) then 9 else
  if p.val = (true, vertices_584) then 10 else
  if p.val = (true, vertices_392) then 11 else
  if p.val = (true, vertices_776) then 12 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_770), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_44), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_140), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_268), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_524), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_148), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_276), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_532), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_772), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_168), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_584), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_392), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_776), by decide +kernel⟩
  | 13 => Sum.inl 0
  | 14 => Sum.inr ⟨(false, vertices_339), by decide +kernel⟩
  | 15 => Sum.inr ⟨(false, vertices_659), by decide +kernel⟩
  | 16 => Sum.inr ⟨(false, vertices_611), by decide +kernel⟩
  | 17 => Sum.inl 1
  | 18 => Sum.inr ⟨(false, vertices_677), by decide +kernel⟩
  | 19 => Sum.inl 2
  | 20 => Sum.inr ⟨(false, vertices_361), by decide +kernel⟩
  | 21 => Sum.inl 3
  | 22 => Sum.inr ⟨(false, vertices_433), by decide +kernel⟩
  | 23 => Sum.inl 4
  | 24 => Sum.inl 5
  | 25 => Sum.inl 6
  | 26 => Sum.inl 7
  | 27 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row 0 6 1 2 3 7 412
cert_row 1 3 0 1 7 8 790
cert_row 2 0 2 5 7 8 842
cert_row 3 1 2 4 5 8 620
cert_rows
cert_pivot_2 6 3 0 1
cert_heightProof 4
cert_coverFacet 0 790
cert_cover_3 0 0 1 1 3 7
cert_coverFacet 1 842
cert_cover_3 1 0 2 2 5 7
cert_coverFacet 2 412
cert_cover_3 2 1 0 2 3 6
cert_coverFacet 3 620
cert_cover_3 3 1 3 2 4 5
cert_coverFacet 4 172
cert_cover_4 4 1 2 4 6
cert_coverFacet 5 780
cert_cover_4 5 1 2 7 8
cert_coverFacet 6 660
cert_cover_4 6 1 3 6 8
cert_coverFacet 7 424
cert_cover_4 7 2 4 6 7
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_018

end
end BundlePart20

section BundlePart21
/- Source: ProjectionCertificates/P0_019.lean -/





@[expose] public section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_019

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
open _root_.Nonrational.SharedProjectionVertexSets

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_651, vertices_563, vertices_227, vertices_541, vertices_281, vertices_457, vertices_369, vertices_614, vertices_962, vertices_316, vertices_908, vertices_564, vertices_356, vertices_836] (by decide +kernel)
  polygons := literalFinset [vertices_35, vertices_131, vertices_515, vertices_25, vertices_137, vertices_265, vertices_521, vertices_49, vertices_273, vertices_529, vertices_97, vertices_193, vertices_321, vertices_98, vertices_546, vertices_194, vertices_578, vertices_642, vertices_28, vertices_268, vertices_524, vertices_52, vertices_532, vertices_100, vertices_292, vertices_548, vertices_324, vertices_580, vertices_772, vertices_280, vertices_392, vertices_648, vertices_304, vertices_560, vertices_352, vertices_448, vertices_832, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_651), (false, vertices_563), (false, vertices_227), (false, vertices_541), (false, vertices_281), (false, vertices_457), (false, vertices_369), (true, vertices_578), (true, vertices_268), (true, vertices_52), (true, vertices_100), (true, vertices_292), (true, vertices_548), (true, vertices_324), (true, vertices_580), (true, vertices_772), (true, vertices_832), (true, vertices_896)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 12 16 18 20 22 23 24 25 26
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_651) then 13 else
  if p.val = (false, vertices_563) then 14 else
  if p.val = (false, vertices_227) then 15 else
  if p.val = (false, vertices_541) then 17 else
  if p.val = (false, vertices_281) then 11 else
  if p.val = (false, vertices_457) then 19 else
  if p.val = (false, vertices_369) then 21 else
  if p.val = (true, vertices_578) then 0 else
  if p.val = (true, vertices_268) then 1 else
  if p.val = (true, vertices_52) then 2 else
  if p.val = (true, vertices_100) then 3 else
  if p.val = (true, vertices_292) then 4 else
  if p.val = (true, vertices_548) then 5 else
  if p.val = (true, vertices_324) then 6 else
  if p.val = (true, vertices_580) then 7 else
  if p.val = (true, vertices_772) then 8 else
  if p.val = (true, vertices_832) then 9 else
  if p.val = (true, vertices_896) then 10 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_578), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_268), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_52), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_100), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_292), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_548), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_324), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_580), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_772), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_832), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_896), by decide +kernel⟩
  | 11 => Sum.inr ⟨(false, vertices_281), by decide +kernel⟩
  | 12 => Sum.inl 0
  | 13 => Sum.inr ⟨(false, vertices_651), by decide +kernel⟩
  | 14 => Sum.inr ⟨(false, vertices_563), by decide +kernel⟩
  | 15 => Sum.inr ⟨(false, vertices_227), by decide +kernel⟩
  | 16 => Sum.inl 1
  | 17 => Sum.inr ⟨(false, vertices_541), by decide +kernel⟩
  | 18 => Sum.inl 2
  | 19 => Sum.inr ⟨(false, vertices_457), by decide +kernel⟩
  | 20 => Sum.inl 3
  | 21 => Sum.inr ⟨(false, vertices_369), by decide +kernel⟩
  | 22 => Sum.inl 4
  | 23 => Sum.inl 5
  | 24 => Sum.inl 6
  | 25 => Sum.inl 7
  | 26 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row 0 3 1 2 4 7 316
cert_row 1 4 0 1 5 8 614
cert_row 2 0 5 6 7 8 962
cert_row 3 1 2 6 7 8 908
cert_rows
cert_pivot_2 3 4 0 1
cert_heightProof 4
cert_coverFacet 0 614
cert_cover_3 0 0 1 1 4 5
cert_coverFacet 1 962
cert_cover_3 1 0 2 5 6 7
cert_coverFacet 2 316
cert_cover_3 2 1 0 2 3 4
cert_coverFacet 3 908
cert_cover_3 3 1 3 2 6 7
cert_coverFacet 4 564
cert_cover_4 4 1 3 4 8
cert_coverFacet 5 356
cert_cover_4 5 1 4 5 7
cert_coverFacet 6 836
cert_cover_4 6 1 5 7 8
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_019

end
end BundlePart21

section BundlePart22
/- Source: ProjectionCertificates/P0_020.lean -/





@[expose] public section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_020

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
open _root_.Nonrational.SharedProjectionVertexSets

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_651, vertices_563, vertices_227, vertices_541, vertices_313, vertices_457, vertices_353, vertices_614, vertices_962, vertices_284, vertices_908, vertices_372, vertices_564, vertices_836] (by decide +kernel)
  polygons := literalFinset [vertices_35, vertices_131, vertices_515, vertices_25, vertices_137, vertices_265, vertices_521, vertices_49, vertices_529, vertices_97, vertices_289, vertices_193, vertices_321, vertices_98, vertices_546, vertices_194, vertices_578, vertices_642, vertices_28, vertices_268, vertices_524, vertices_52, vertices_276, vertices_532, vertices_100, vertices_548, vertices_324, vertices_580, vertices_772, vertices_280, vertices_392, vertices_648, vertices_304, vertices_560, vertices_352, vertices_448, vertices_832, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_651), (false, vertices_563), (false, vertices_227), (false, vertices_541), (false, vertices_313), (false, vertices_457), (false, vertices_353), (true, vertices_578), (true, vertices_268), (true, vertices_52), (true, vertices_276), (true, vertices_100), (true, vertices_548), (true, vertices_324), (true, vertices_580), (true, vertices_772), (true, vertices_832), (true, vertices_896)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 12 16 18 21 22 23 24 25 26
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_651) then 13 else
  if p.val = (false, vertices_563) then 14 else
  if p.val = (false, vertices_227) then 15 else
  if p.val = (false, vertices_541) then 17 else
  if p.val = (false, vertices_313) then 19 else
  if p.val = (false, vertices_457) then 20 else
  if p.val = (false, vertices_353) then 11 else
  if p.val = (true, vertices_578) then 0 else
  if p.val = (true, vertices_268) then 1 else
  if p.val = (true, vertices_52) then 2 else
  if p.val = (true, vertices_276) then 3 else
  if p.val = (true, vertices_100) then 4 else
  if p.val = (true, vertices_548) then 5 else
  if p.val = (true, vertices_324) then 6 else
  if p.val = (true, vertices_580) then 7 else
  if p.val = (true, vertices_772) then 8 else
  if p.val = (true, vertices_832) then 9 else
  if p.val = (true, vertices_896) then 10 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_578), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_268), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_52), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_276), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_100), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_548), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_324), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_580), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_772), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_832), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_896), by decide +kernel⟩
  | 11 => Sum.inr ⟨(false, vertices_353), by decide +kernel⟩
  | 12 => Sum.inl 0
  | 13 => Sum.inr ⟨(false, vertices_651), by decide +kernel⟩
  | 14 => Sum.inr ⟨(false, vertices_563), by decide +kernel⟩
  | 15 => Sum.inr ⟨(false, vertices_227), by decide +kernel⟩
  | 16 => Sum.inl 1
  | 17 => Sum.inr ⟨(false, vertices_541), by decide +kernel⟩
  | 18 => Sum.inl 2
  | 19 => Sum.inr ⟨(false, vertices_313), by decide +kernel⟩
  | 20 => Sum.inr ⟨(false, vertices_457), by decide +kernel⟩
  | 21 => Sum.inl 3
  | 22 => Sum.inl 4
  | 23 => Sum.inl 5
  | 24 => Sum.inl 6
  | 25 => Sum.inl 7
  | 26 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row 0 2 1 6 7 8 908
cert_row 1 6 0 5 7 8 962
cert_row 2 0 1 4 5 8 614
cert_row 3 1 3 4 5 7 372
cert_rows
cert_pivot_2 2 6 0 1
cert_heightProof 4
cert_coverFacet 0 614
cert_cover_3 0 0 2 1 4 5
cert_coverFacet 1 962
cert_cover_3 1 0 1 5 6 7
cert_coverFacet 2 284
cert_cover_4 2 1 2 3 7
cert_coverFacet 3 908
cert_cover_3 3 1 0 2 6 7
cert_coverFacet 4 372
cert_cover_3 4 1 3 3 4 5
cert_coverFacet 5 564
cert_cover_4 5 1 3 4 8
cert_coverFacet 6 836
cert_cover_4 6 1 5 7 8
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_020

end
end BundlePart22

section BundlePart23
/- Source: ProjectionCertificates/P0_022.lean -/





@[expose] public section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_022

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
open _root_.Nonrational.SharedProjectionVertexSets

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_279, vertices_299, vertices_179, vertices_541, vertices_333, vertices_681, vertices_657, vertices_466, vertices_418, vertices_620, vertices_724, vertices_340, vertices_360, vertices_992] (by decide +kernel)
  polygons := literalFinset [vertices_19, vertices_35, vertices_259, vertices_13, vertices_21, vertices_261, vertices_41, vertices_265, vertices_521, vertices_145, vertices_529, vertices_161, vertices_641, vertices_146, vertices_274, vertices_162, vertices_290, vertices_386, vertices_76, vertices_524, vertices_84, vertices_276, vertices_532, vertices_324, vertices_580, vertices_104, vertices_296, vertices_552, vertices_328, vertices_208, vertices_336, vertices_656, vertices_352, vertices_608, vertices_416, vertices_672, vertices_448, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_279), (false, vertices_299), (false, vertices_179), (false, vertices_541), (false, vertices_333), (false, vertices_681), (false, vertices_657), (true, vertices_386), (true, vertices_84), (true, vertices_580), (true, vertices_104), (true, vertices_208), (true, vertices_336), (true, vertices_352), (true, vertices_608), (true, vertices_416), (true, vertices_448), (true, vertices_704)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 12 16 19 21 22 23 24 25 26
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_279) then 13 else
  if p.val = (false, vertices_299) then 14 else
  if p.val = (false, vertices_179) then 15 else
  if p.val = (false, vertices_541) then 17 else
  if p.val = (false, vertices_333) then 18 else
  if p.val = (false, vertices_681) then 20 else
  if p.val = (false, vertices_657) then 11 else
  if p.val = (true, vertices_386) then 0 else
  if p.val = (true, vertices_84) then 1 else
  if p.val = (true, vertices_580) then 2 else
  if p.val = (true, vertices_104) then 3 else
  if p.val = (true, vertices_208) then 4 else
  if p.val = (true, vertices_336) then 5 else
  if p.val = (true, vertices_352) then 6 else
  if p.val = (true, vertices_608) then 7 else
  if p.val = (true, vertices_416) then 8 else
  if p.val = (true, vertices_448) then 9 else
  if p.val = (true, vertices_704) then 10 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_386), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_84), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_580), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_104), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_208), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_336), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_352), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_608), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_416), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_448), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_704), by decide +kernel⟩
  | 11 => Sum.inr ⟨(false, vertices_657), by decide +kernel⟩
  | 12 => Sum.inl 0
  | 13 => Sum.inr ⟨(false, vertices_279), by decide +kernel⟩
  | 14 => Sum.inr ⟨(false, vertices_299), by decide +kernel⟩
  | 15 => Sum.inr ⟨(false, vertices_179), by decide +kernel⟩
  | 16 => Sum.inl 1
  | 17 => Sum.inr ⟨(false, vertices_541), by decide +kernel⟩
  | 18 => Sum.inr ⟨(false, vertices_333), by decide +kernel⟩
  | 19 => Sum.inl 2
  | 20 => Sum.inr ⟨(false, vertices_681), by decide +kernel⟩
  | 21 => Sum.inl 3
  | 22 => Sum.inl 4
  | 23 => Sum.inl 5
  | 24 => Sum.inl 6
  | 25 => Sum.inl 7
  | 26 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row 0 0 3 5 6 7 466
cert_row 1 2 1 4 5 8 620
cert_row 2 1 3 5 6 8 724
cert_row 3 4 5 6 7 8 992
cert_rows
cert_pivot_2 0 2 1 4
cert_heightProof 4
cert_coverFacet 0 466
cert_cover_3 0 0 0 3 5 6
cert_coverFacet 1 418
cert_cover_4 1 0 4 6 7
cert_coverFacet 2 620
cert_cover_3 2 1 1 2 4 5
cert_coverFacet 3 724
cert_cover_3 3 1 2 3 5 6
cert_coverFacet 4 340
cert_cover_4 4 1 3 5 7
cert_coverFacet 5 360
cert_cover_4 5 2 4 5 7
cert_coverFacet 6 992
cert_cover_3 6 4 3 5 6 7
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_022

end
end BundlePart23

section BundlePart24
/- Source: ProjectionCertificates/P0_023.lean -/





@[expose] public section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_023

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
open _root_.Nonrational.SharedProjectionVertexSets

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_403, vertices_109, vertices_525, vertices_565, vertices_665, vertices_457, vertices_369, vertices_614, vertices_906, vertices_690, vertices_306, vertices_354, vertices_834, vertices_844] (by decide +kernel)
  polygons := literalFinset [vertices_13, vertices_37, vertices_517, vertices_73, vertices_137, vertices_521, vertices_49, vertices_145, vertices_273, vertices_529, vertices_97, vertices_321, vertices_385, vertices_50, vertices_146, vertices_274, vertices_98, vertices_290, vertices_546, vertices_322, vertices_578, vertices_386, vertices_642, vertices_770, vertices_76, vertices_524, vertices_100, vertices_548, vertices_580, vertices_328, vertices_392, vertices_648, vertices_776, vertices_304, vertices_560, vertices_656, vertices_352, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_403), (false, vertices_109), (false, vertices_525), (false, vertices_565), (false, vertices_665), (false, vertices_457), (false, vertices_369), (true, vertices_50), (true, vertices_98), (true, vertices_290), (true, vertices_546), (true, vertices_322), (true, vertices_578), (true, vertices_642), (true, vertices_770), (true, vertices_580), (true, vertices_776), (true, vertices_832)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 12 14 17 20 22 23 24 25 26
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_403) then 13 else
  if p.val = (false, vertices_109) then 15 else
  if p.val = (false, vertices_525) then 11 else
  if p.val = (false, vertices_565) then 16 else
  if p.val = (false, vertices_665) then 18 else
  if p.val = (false, vertices_457) then 19 else
  if p.val = (false, vertices_369) then 21 else
  if p.val = (true, vertices_50) then 0 else
  if p.val = (true, vertices_98) then 1 else
  if p.val = (true, vertices_290) then 2 else
  if p.val = (true, vertices_546) then 3 else
  if p.val = (true, vertices_322) then 4 else
  if p.val = (true, vertices_578) then 5 else
  if p.val = (true, vertices_642) then 6 else
  if p.val = (true, vertices_770) then 7 else
  if p.val = (true, vertices_580) then 8 else
  if p.val = (true, vertices_776) then 9 else
  if p.val = (true, vertices_832) then 10 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_50), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_98), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_290), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_546), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_322), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_578), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_642), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_770), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_580), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_776), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_832), by decide +kernel⟩
  | 11 => Sum.inr ⟨(false, vertices_525), by decide +kernel⟩
  | 12 => Sum.inl 0
  | 13 => Sum.inr ⟨(false, vertices_403), by decide +kernel⟩
  | 14 => Sum.inl 1
  | 15 => Sum.inr ⟨(false, vertices_109), by decide +kernel⟩
  | 16 => Sum.inr ⟨(false, vertices_565), by decide +kernel⟩
  | 17 => Sum.inl 2
  | 18 => Sum.inr ⟨(false, vertices_665), by decide +kernel⟩
  | 19 => Sum.inr ⟨(false, vertices_457), by decide +kernel⟩
  | 20 => Sum.inl 3
  | 21 => Sum.inr ⟨(false, vertices_369), by decide +kernel⟩
  | 22 => Sum.inl 4
  | 23 => Sum.inl 5
  | 24 => Sum.inl 6
  | 25 => Sum.inl 7
  | 26 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row 0 3 0 4 6 8 690
cert_row 1 4 0 1 5 8 614
cert_row 2 0 2 6 7 8 906
cert_row 3 1 2 5 7 8 844
cert_rows
cert_pivot_2 3 4 0 1
cert_heightProof 4
cert_coverFacet 0 614
cert_cover_3 0 0 1 1 4 5
cert_coverFacet 1 906
cert_cover_3 1 0 2 2 6 7
cert_coverFacet 2 690
cert_cover_3 2 0 0 3 4 6
cert_coverFacet 3 306
cert_cover_4 3 0 3 4 7
cert_coverFacet 4 354
cert_cover_4 4 0 4 5 7
cert_coverFacet 5 834
cert_cover_4 5 0 5 7 8
cert_coverFacet 6 844
cert_cover_3 6 1 3 2 5 7
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_023

end
end BundlePart24

section BundlePart25
/- Source: ProjectionCertificates/P0_024.lean -/





@[expose] public section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_024

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
open _root_.Nonrational.SharedProjectionVertexSets

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_271, vertices_587, vertices_307, vertices_531, vertices_205, vertices_181, vertices_293, vertices_721, vertices_794, vertices_364, vertices_740, vertices_840, vertices_944, vertices_864] (by decide +kernel)
  polygons := literalFinset [vertices_11, vertices_19, vertices_259, vertices_515, vertices_13, vertices_37, vertices_133, vertices_261, vertices_73, vertices_49, vertices_145, vertices_529, vertices_289, vertices_193, vertices_577, vertices_266, vertices_522, vertices_274, vertices_530, vertices_76, vertices_268, vertices_100, vertices_164, vertices_292, vertices_196, vertices_328, vertices_584, vertices_776, vertices_176, vertices_304, vertices_656, vertices_784, vertices_352, vertices_608, vertices_672, vertices_800, vertices_704, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_271), (false, vertices_587), (false, vertices_307), (false, vertices_531), (false, vertices_205), (false, vertices_181), (false, vertices_293), (false, vertices_721), (true, vertices_100), (true, vertices_328), (true, vertices_776), (true, vertices_784), (true, vertices_352), (true, vertices_608), (true, vertices_672), (true, vertices_800), (true, vertices_832)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 11 15 18 19 21 22 23 24 25
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_271) then 12 else
  if p.val = (false, vertices_587) then 13 else
  if p.val = (false, vertices_307) then 14 else
  if p.val = (false, vertices_531) then 9 else
  if p.val = (false, vertices_205) then 16 else
  if p.val = (false, vertices_181) then 17 else
  if p.val = (false, vertices_293) then 10 else
  if p.val = (false, vertices_721) then 20 else
  if p.val = (true, vertices_100) then 0 else
  if p.val = (true, vertices_328) then 1 else
  if p.val = (true, vertices_776) then 2 else
  if p.val = (true, vertices_784) then 3 else
  if p.val = (true, vertices_352) then 4 else
  if p.val = (true, vertices_608) then 5 else
  if p.val = (true, vertices_672) then 6 else
  if p.val = (true, vertices_800) then 7 else
  if p.val = (true, vertices_832) then 8 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_100), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_328), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_776), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_784), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_352), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_608), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_672), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_800), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_832), by decide +kernel⟩
  | 9 => Sum.inr ⟨(false, vertices_531), by decide +kernel⟩
  | 10 => Sum.inr ⟨(false, vertices_293), by decide +kernel⟩
  | 11 => Sum.inl 0
  | 12 => Sum.inr ⟨(false, vertices_271), by decide +kernel⟩
  | 13 => Sum.inr ⟨(false, vertices_587), by decide +kernel⟩
  | 14 => Sum.inr ⟨(false, vertices_307), by decide +kernel⟩
  | 15 => Sum.inl 1
  | 16 => Sum.inr ⟨(false, vertices_205), by decide +kernel⟩
  | 17 => Sum.inr ⟨(false, vertices_181), by decide +kernel⟩
  | 18 => Sum.inl 2
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
cert_row 0 0 2 3 7 8 794
cert_row 1 2 1 4 5 7 364
cert_row 2 1 4 5 6 8 740
cert_row 3 3 4 6 7 8 944
cert_rows
cert_pivot_2 0 2 1 3
cert_heightProof 4
cert_coverFacet 0 794
cert_cover_3 0 0 0 2 3 7
cert_coverFacet 1 364
cert_cover_3 1 1 1 2 4 5
cert_coverFacet 2 740
cert_cover_3 2 1 2 4 5 6
cert_coverFacet 3 840
cert_cover_4 3 2 5 7 8
cert_coverFacet 4 944
cert_cover_3 4 3 3 4 6 7
cert_coverFacet 5 864
cert_cover_4 5 4 5 7 8
cert_coveringFacets
cert_coveringProof_6
cert_certificate 4 6
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_024

end
end BundlePart25

section BundlePart26
/- Source: ProjectionCertificates/P0_025.lean -/





@[expose] public section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_025

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
open _root_.Nonrational.SharedProjectionVertexSets

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_555, vertices_179, vertices_595, vertices_589, vertices_345, vertices_425, vertices_401, vertices_678, vertices_914, vertices_364, vertices_556, vertices_852, vertices_420, vertices_900] (by decide +kernel)
  polygons := literalFinset [vertices_19, vertices_35, vertices_515, vertices_41, vertices_73, vertices_265, vertices_521, vertices_81, vertices_145, vertices_273, vertices_161, vertices_577, vertices_385, vertices_146, vertices_530, vertices_162, vertices_546, vertices_642, vertices_44, vertices_76, vertices_524, vertices_164, vertices_292, vertices_548, vertices_324, vertices_580, vertices_388, vertices_644, vertices_772, vertices_296, vertices_552, vertices_328, vertices_336, vertices_592, vertices_400, vertices_784, vertices_416, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_555), (false, vertices_179), (false, vertices_595), (false, vertices_589), (false, vertices_345), (false, vertices_425), (false, vertices_401), (true, vertices_642), (true, vertices_44), (true, vertices_164), (true, vertices_292), (true, vertices_548), (true, vertices_324), (true, vertices_388), (true, vertices_644), (true, vertices_772), (true, vertices_784), (true, vertices_896)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 12 16 18 21 22 23 24 25 26
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_555) then 13 else
  if p.val = (false, vertices_179) then 14 else
  if p.val = (false, vertices_595) then 15 else
  if p.val = (false, vertices_589) then 17 else
  if p.val = (false, vertices_345) then 19 else
  if p.val = (false, vertices_425) then 20 else
  if p.val = (false, vertices_401) then 11 else
  if p.val = (true, vertices_642) then 0 else
  if p.val = (true, vertices_44) then 1 else
  if p.val = (true, vertices_164) then 2 else
  if p.val = (true, vertices_292) then 3 else
  if p.val = (true, vertices_548) then 4 else
  if p.val = (true, vertices_324) then 5 else
  if p.val = (true, vertices_388) then 6 else
  if p.val = (true, vertices_644) then 7 else
  if p.val = (true, vertices_772) then 8 else
  if p.val = (true, vertices_784) then 9 else
  if p.val = (true, vertices_896) then 10 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_642), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_44), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_164), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_292), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_548), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_324), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_388), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_644), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_772), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_784), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_896), by decide +kernel⟩
  | 11 => Sum.inr ⟨(false, vertices_401), by decide +kernel⟩
  | 12 => Sum.inl 0
  | 13 => Sum.inr ⟨(false, vertices_555), by decide +kernel⟩
  | 14 => Sum.inr ⟨(false, vertices_179), by decide +kernel⟩
  | 15 => Sum.inr ⟨(false, vertices_595), by decide +kernel⟩
  | 16 => Sum.inl 1
  | 17 => Sum.inr ⟨(false, vertices_589), by decide +kernel⟩
  | 18 => Sum.inl 2
  | 19 => Sum.inr ⟨(false, vertices_345), by decide +kernel⟩
  | 20 => Sum.inr ⟨(false, vertices_425), by decide +kernel⟩
  | 21 => Sum.inl 3
  | 22 => Sum.inl 4
  | 23 => Sum.inl 5
  | 24 => Sum.inl 6
  | 25 => Sum.inl 7
  | 26 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row 0 2 1 4 5 7 364
cert_row 1 4 0 1 6 8 678
cert_row 2 0 3 6 7 8 914
cert_row 3 1 3 5 7 8 852
cert_rows
cert_pivot_2 2 4 0 1
cert_heightProof 4
cert_coverFacet 0 678
cert_cover_3 0 0 1 1 4 6
cert_coverFacet 1 914
cert_cover_3 1 0 2 3 6 7
cert_coverFacet 2 364
cert_cover_3 2 1 0 2 4 5
cert_coverFacet 3 556
cert_cover_4 3 1 2 4 8
cert_coverFacet 4 852
cert_cover_3 4 1 3 3 5 7
cert_coverFacet 5 420
cert_cover_4 5 1 4 6 7
cert_coverFacet 6 900
cert_cover_4 6 1 6 7 8
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_025

end
end BundlePart26

section BundlePart27
/- Source: ProjectionCertificates/P0_026.lean -/





@[expose] public section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_026

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
open _root_.Nonrational.SharedProjectionVertexSets

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_103, vertices_171, vertices_211, vertices_597, vertices_549, vertices_569, vertices_409, vertices_422, vertices_838, vertices_450, vertices_812, vertices_856, vertices_424, vertices_464] (by decide +kernel)
  polygons := literalFinset [vertices_35, vertices_67, vertices_131, vertices_37, vertices_69, vertices_517, vertices_25, vertices_41, vertices_137, vertices_81, vertices_145, vertices_529, vertices_545, vertices_38, vertices_70, vertices_262, vertices_162, vertices_194, vertices_322, vertices_386, vertices_292, vertices_548, vertices_580, vertices_772, vertices_280, vertices_536, vertices_168, vertices_296, vertices_552, vertices_392, vertices_776, vertices_208, vertices_336, vertices_592, vertices_400, vertices_416, vertices_448, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_103), (false, vertices_171), (false, vertices_211), (false, vertices_597), (false, vertices_549), (false, vertices_569), (false, vertices_409), (true, vertices_262), (true, vertices_322), (true, vertices_386), (true, vertices_292), (true, vertices_772), (true, vertices_296), (true, vertices_776), (true, vertices_336), (true, vertices_416), (true, vertices_448), (true, vertices_832)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 12 16 18 21 22 23 24 25 26
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_103) then 13 else
  if p.val = (false, vertices_171) then 14 else
  if p.val = (false, vertices_211) then 15 else
  if p.val = (false, vertices_597) then 17 else
  if p.val = (false, vertices_549) then 11 else
  if p.val = (false, vertices_569) then 19 else
  if p.val = (false, vertices_409) then 20 else
  if p.val = (true, vertices_262) then 0 else
  if p.val = (true, vertices_322) then 1 else
  if p.val = (true, vertices_386) then 2 else
  if p.val = (true, vertices_292) then 3 else
  if p.val = (true, vertices_772) then 4 else
  if p.val = (true, vertices_296) then 5 else
  if p.val = (true, vertices_776) then 6 else
  if p.val = (true, vertices_336) then 7 else
  if p.val = (true, vertices_416) then 8 else
  if p.val = (true, vertices_448) then 9 else
  if p.val = (true, vertices_832) then 10 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_262), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_322), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_386), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_292), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_772), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_296), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_776), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_336), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_416), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_448), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_832), by decide +kernel⟩
  | 11 => Sum.inr ⟨(false, vertices_549), by decide +kernel⟩
  | 12 => Sum.inl 0
  | 13 => Sum.inr ⟨(false, vertices_103), by decide +kernel⟩
  | 14 => Sum.inr ⟨(false, vertices_171), by decide +kernel⟩
  | 15 => Sum.inr ⟨(false, vertices_211), by decide +kernel⟩
  | 16 => Sum.inl 1
  | 17 => Sum.inr ⟨(false, vertices_597), by decide +kernel⟩
  | 18 => Sum.inl 2
  | 19 => Sum.inr ⟨(false, vertices_569), by decide +kernel⟩
  | 20 => Sum.inr ⟨(false, vertices_409), by decide +kernel⟩
  | 21 => Sum.inl 3
  | 22 => Sum.inl 4
  | 23 => Sum.inl 5
  | 24 => Sum.inl 6
  | 25 => Sum.inl 7
  | 26 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row 0 6 0 1 4 7 422
cert_row 1 0 1 5 7 8 838
cert_row 2 1 2 4 7 8 812
cert_row 3 2 3 5 7 8 856
cert_rows
cert_pivot_2 6 0 1 2
cert_heightProof 4
cert_coverFacet 0 422
cert_cover_3 0 0 0 1 4 6
cert_coverFacet 1 838
cert_cover_3 1 0 1 1 5 7
cert_coverFacet 2 450
cert_cover_4 2 0 5 6 7
cert_coverFacet 3 812
cert_cover_3 3 1 2 2 4 7
cert_coverFacet 4 856
cert_cover_3 4 2 3 3 5 7
cert_coverFacet 5 424
cert_cover_4 5 2 4 6 7
cert_coverFacet 6 464
cert_cover_4 6 3 5 6 7
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_026

end
end BundlePart27

section BundlePart28
/- Source: ProjectionCertificates/P0_027.lean -/





@[expose] public section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_027

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
open _root_.Nonrational.SharedProjectionVertexSets

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_647, vertices_587, vertices_83, vertices_403, vertices_557, vertices_181, vertices_121, vertices_370, vertices_962, vertices_364, vertices_908, vertices_420, vertices_840, vertices_432] (by decide +kernel)
  polygons := literalFinset [vertices_19, vertices_67, vertices_131, vertices_515, vertices_37, vertices_133, vertices_517, vertices_41, vertices_73, vertices_521, vertices_49, vertices_81, vertices_145, vertices_82, vertices_274, vertices_322, vertices_578, vertices_386, vertices_642, vertices_44, vertices_268, vertices_524, vertices_164, vertices_292, vertices_388, vertices_644, vertices_104, vertices_328, vertices_584, vertices_776, vertices_112, vertices_176, vertices_304, vertices_400, vertices_352, vertices_416, vertices_832, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_647), (false, vertices_587), (false, vertices_83), (false, vertices_403), (false, vertices_557), (false, vertices_181), (false, vertices_121), (true, vertices_322), (true, vertices_268), (true, vertices_292), (true, vertices_388), (true, vertices_328), (true, vertices_776), (true, vertices_304), (true, vertices_352), (true, vertices_416), (true, vertices_832), (true, vertices_896)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 12 16 19 21 22 23 24 25 26
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_647) then 13 else
  if p.val = (false, vertices_587) then 14 else
  if p.val = (false, vertices_83) then 11 else
  if p.val = (false, vertices_403) then 15 else
  if p.val = (false, vertices_557) then 17 else
  if p.val = (false, vertices_181) then 18 else
  if p.val = (false, vertices_121) then 20 else
  if p.val = (true, vertices_322) then 0 else
  if p.val = (true, vertices_268) then 1 else
  if p.val = (true, vertices_292) then 2 else
  if p.val = (true, vertices_388) then 3 else
  if p.val = (true, vertices_328) then 4 else
  if p.val = (true, vertices_776) then 5 else
  if p.val = (true, vertices_304) then 6 else
  if p.val = (true, vertices_352) then 7 else
  if p.val = (true, vertices_416) then 8 else
  if p.val = (true, vertices_832) then 9 else
  if p.val = (true, vertices_896) then 10 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_322), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_268), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_292), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_388), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_328), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_776), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_304), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_352), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_416), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_832), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_896), by decide +kernel⟩
  | 11 => Sum.inr ⟨(false, vertices_83), by decide +kernel⟩
  | 12 => Sum.inl 0
  | 13 => Sum.inr ⟨(false, vertices_647), by decide +kernel⟩
  | 14 => Sum.inr ⟨(false, vertices_587), by decide +kernel⟩
  | 15 => Sum.inr ⟨(false, vertices_403), by decide +kernel⟩
  | 16 => Sum.inl 1
  | 17 => Sum.inr ⟨(false, vertices_557), by decide +kernel⟩
  | 18 => Sum.inr ⟨(false, vertices_181), by decide +kernel⟩
  | 19 => Sum.inl 2
  | 20 => Sum.inr ⟨(false, vertices_121), by decide +kernel⟩
  | 21 => Sum.inl 3
  | 22 => Sum.inl 4
  | 23 => Sum.inl 5
  | 24 => Sum.inl 6
  | 25 => Sum.inl 7
  | 26 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row 0 3 0 4 5 7 370
cert_row 1 0 5 6 7 8 962
cert_row 2 4 1 2 5 7 364
cert_row 3 1 2 6 7 8 908
cert_rows
cert_pivot_2 3 0 4 1
cert_heightProof 4
cert_coverFacet 0 370
cert_cover_3 0 0 0 3 4 5
cert_coverFacet 1 962
cert_cover_3 1 0 1 5 6 7
cert_coverFacet 2 364
cert_cover_3 2 1 2 2 4 5
cert_coverFacet 3 908
cert_cover_3 3 1 3 2 6 7
cert_coverFacet 4 420
cert_cover_4 4 1 4 6 7
cert_coverFacet 5 840
cert_cover_4 5 2 5 7 8
cert_coverFacet 6 432
cert_cover_4 6 3 4 6 7
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_027

end
end BundlePart28

section BundlePart29
/- Source: ProjectionCertificates/P0_028.lean -/





@[expose] public section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_028

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
open _root_.Nonrational.SharedProjectionVertexSets

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_391, vertices_781, vertices_661, vertices_601, vertices_457, vertices_241, vertices_806, vertices_646, vertices_362, vertices_690, vertices_226, vertices_450, vertices_120, vertices_824] (by decide +kernel)
  polygons := literalFinset [vertices_133, vertices_261, vertices_517, vertices_73, vertices_265, vertices_521, vertices_81, vertices_145, vertices_529, vertices_193, vertices_385, vertices_134, vertices_262, vertices_518, vertices_98, vertices_162, vertices_290, vertices_546, vertices_194, vertices_322, vertices_386, vertices_642, vertices_644, vertices_772, vertices_56, vertices_88, vertices_536, vertices_104, vertices_296, vertices_328, vertices_776, vertices_112, vertices_176, vertices_560, vertices_656, vertices_224, vertices_800, vertices_448] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_391), (false, vertices_781), (false, vertices_661), (false, vertices_601), (false, vertices_457), (false, vertices_241), (true, vertices_518), (true, vertices_98), (true, vertices_162), (true, vertices_290), (true, vertices_546), (true, vertices_194), (true, vertices_322), (true, vertices_642), (true, vertices_56), (true, vertices_104), (true, vertices_296), (true, vertices_560), (true, vertices_800)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 13 15 18 21 23 24 25 26 27
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_391) then 14 else
  if p.val = (false, vertices_781) then 16 else
  if p.val = (false, vertices_661) then 17 else
  if p.val = (false, vertices_601) then 19 else
  if p.val = (false, vertices_457) then 20 else
  if p.val = (false, vertices_241) then 22 else
  if p.val = (true, vertices_518) then 0 else
  if p.val = (true, vertices_98) then 1 else
  if p.val = (true, vertices_162) then 2 else
  if p.val = (true, vertices_290) then 3 else
  if p.val = (true, vertices_546) then 4 else
  if p.val = (true, vertices_194) then 5 else
  if p.val = (true, vertices_322) then 6 else
  if p.val = (true, vertices_642) then 7 else
  if p.val = (true, vertices_56) then 8 else
  if p.val = (true, vertices_104) then 9 else
  if p.val = (true, vertices_296) then 10 else
  if p.val = (true, vertices_560) then 11 else
  if p.val = (true, vertices_800) then 12 else
  0
cert_priority
cert_nodeAtPriority_12 518 1 98 2 162 290 546 194 322 642 56 104 296 560 800 391 781 661 601 457 241
cert_priority_injective
cert_incidenceProof
cert_row 0 1 0 4 7 8 806
cert_row 1 5 0 2 4 7 362
cert_row 2 0 3 4 6 8 690
cert_row 3 2 3 4 7 8 824
cert_rows
cert_pivot_2 1 5 0 2
cert_heightProof 4
cert_coverFacet 0 806
cert_cover_3 0 0 0 1 4 7
cert_coverFacet 1 646
cert_cover_4 1 0 1 6 8
cert_coverFacet 2 362
cert_cover_3 2 0 1 2 4 5
cert_coverFacet 3 690
cert_cover_3 3 0 2 3 4 6
cert_coverFacet 4 226
cert_cover_4 4 0 4 5 6
cert_coverFacet 5 450
cert_cover_4 5 0 5 6 7
cert_coverFacet 6 120
cert_cover_4 6 2 3 4 5
cert_coverFacet 7 824
cert_cover_3 7 2 3 3 4 7
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_028

end
end BundlePart29
