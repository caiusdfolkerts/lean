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
/- Source: ProjectionCertificates/R_one_six_0939.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0939

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 647, 779, 533, 361, 817, 206, 458, 898, 124, 724, 624, 992, 7, 11, 515, 21, 517, 41, 265, 49, 529, 289, 769, 14, 134, 202, 266, 386, 642, 770, 60, 76, 84, 532, 196, 644, 104, 328, 112, 560, 592, 352, 608, 800, 448, 704, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_647, vertices_779, vertices_533, vertices_361, vertices_817, vertices_206, vertices_458, vertices_898, vertices_124, vertices_724, vertices_624, vertices_992] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_515, vertices_21, vertices_517, vertices_41, vertices_265, vertices_49, vertices_529, vertices_289, vertices_769, vertices_14, vertices_134, vertices_202, vertices_266, vertices_386, vertices_642, vertices_770, vertices_60, vertices_76, vertices_84, vertices_532, vertices_196, vertices_644, vertices_104, vertices_328, vertices_112, vertices_560, vertices_592, vertices_352, vertices_608, vertices_800, vertices_448, vertices_704, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_647), (false, vertices_779), (false, vertices_533), (false, vertices_361), (false, vertices_817), (true, vertices_202), (true, vertices_386), (true, vertices_76), (true, vertices_84), (true, vertices_196), (true, vertices_112), (true, vertices_592), (true, vertices_608), (true, vertices_448), (true, vertices_704), (true, vertices_896)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 16 11 19 13 21 22 23 24 25
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 14 else
  if p.val = (false, vertices_647) then 12 else
  if p.val = (false, vertices_779) then 17 else
  if p.val = (false, vertices_533) then 0 else
  if p.val = (false, vertices_361) then 20 else
  if p.val = (false, vertices_817) then 15 else
  if p.val = (true, vertices_202) then 18 else
  if p.val = (true, vertices_386) then 1 else
  if p.val = (true, vertices_76) then 2 else
  if p.val = (true, vertices_84) then 3 else
  if p.val = (true, vertices_196) then 4 else
  if p.val = (true, vertices_112) then 5 else
  if p.val = (true, vertices_592) then 6 else
  if p.val = (true, vertices_608) then 7 else
  if p.val = (true, vertices_448) then 8 else
  if p.val = (true, vertices_704) then 9 else
  if p.val = (true, vertices_896) then 10 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_533), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_386), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_76), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_84), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_196), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_112), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_592), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_608), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_448), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_704), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_896), by decide +kernel⟩
  | 11 => Sum.inl 1
  | 12 => Sum.inr ⟨(false, vertices_647), by decide +kernel⟩
  | 13 => Sum.inl 3
  | 14 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 15 => Sum.inr ⟨(false, vertices_817), by decide +kernel⟩
  | 16 => Sum.inl 0
  | 17 => Sum.inr ⟨(false, vertices_779), by decide +kernel⟩
  | 18 => Sum.inr ⟨(true, vertices_202), by decide +kernel⟩
  | 19 => Sum.inl 2
  | 20 => Sum.inr ⟨(false, vertices_361), by decide +kernel⟩
  | 21 => Sum.inl 4
  | 22 => Sum.inl 5
  | 23 => Sum.inl 6
  | 24 => Sum.inl 7
  | 25 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 2 5 6 202
cert_row_2 1 1 2 3 4 60
cert_row_4 2 1 3 5 6 8 724 84 3
cert_row_4 3 4 5 6 7 8 992 352 2
cert_rows
cert_pivot_2 0 2 1 4
cert_heightProof 4
cert_coverFacet 0 206
cert_cover_5 0 0 0 1 2 5 14 206 3
cert_coverFacet 1 458
cert_cover_5 1 0 0 2 5 7 202 458 3
cert_coverFacet 2 898
cert_cover_2 2 6 0 7 8 386 898 3
cert_coverFacet 3 124
cert_cover_5 3 1 1 2 3 5 60 124 3
cert_coverFacet 4 724
cert_cover_5 4 2 1 3 5 6 84 724 3
cert_coverFacet 5 624
cert_cover_2 5 4 3 5 8 112 624 3
cert_coverFacet 6 992
cert_cover_5 6 3 4 5 6 7 352 992 2
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0939

end
end BundlePart0

section BundlePart1
/- Source: ProjectionCertificates/R_one_six_0940.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0940

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 647, 779, 533, 361, 817, 206, 458, 898, 124, 724, 496, 912, 7, 11, 515, 21, 517, 41, 265, 49, 529, 289, 769, 14, 134, 202, 266, 386, 642, 770, 60, 76, 84, 532, 196, 644, 104, 328, 112, 304, 208, 400, 656, 784, 352, 448, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_647, vertices_779, vertices_533, vertices_361, vertices_817, vertices_206, vertices_458, vertices_898, vertices_124, vertices_724, vertices_496, vertices_912] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_515, vertices_21, vertices_517, vertices_41, vertices_265, vertices_49, vertices_529, vertices_289, vertices_769, vertices_14, vertices_134, vertices_202, vertices_266, vertices_386, vertices_642, vertices_770, vertices_60, vertices_76, vertices_84, vertices_532, vertices_196, vertices_644, vertices_104, vertices_328, vertices_112, vertices_304, vertices_208, vertices_400, vertices_656, vertices_784, vertices_352, vertices_448, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_647), (false, vertices_779), (false, vertices_533), (false, vertices_361), (false, vertices_817), (true, vertices_202), (true, vertices_386), (true, vertices_76), (true, vertices_84), (true, vertices_196), (true, vertices_112), (true, vertices_208), (true, vertices_400), (true, vertices_656), (true, vertices_448), (true, vertices_896)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 16 11 19 13 21 22 23 24 25
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 14 else
  if p.val = (false, vertices_647) then 12 else
  if p.val = (false, vertices_779) then 17 else
  if p.val = (false, vertices_533) then 0 else
  if p.val = (false, vertices_361) then 20 else
  if p.val = (false, vertices_817) then 15 else
  if p.val = (true, vertices_202) then 18 else
  if p.val = (true, vertices_386) then 1 else
  if p.val = (true, vertices_76) then 2 else
  if p.val = (true, vertices_84) then 3 else
  if p.val = (true, vertices_196) then 4 else
  if p.val = (true, vertices_112) then 5 else
  if p.val = (true, vertices_208) then 6 else
  if p.val = (true, vertices_400) then 7 else
  if p.val = (true, vertices_656) then 8 else
  if p.val = (true, vertices_448) then 9 else
  if p.val = (true, vertices_896) then 10 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_533), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_386), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_76), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_84), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_196), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_112), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_208), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_400), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_656), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_448), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_896), by decide +kernel⟩
  | 11 => Sum.inl 1
  | 12 => Sum.inr ⟨(false, vertices_647), by decide +kernel⟩
  | 13 => Sum.inl 3
  | 14 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 15 => Sum.inr ⟨(false, vertices_817), by decide +kernel⟩
  | 16 => Sum.inl 0
  | 17 => Sum.inr ⟨(false, vertices_779), by decide +kernel⟩
  | 18 => Sum.inr ⟨(true, vertices_202), by decide +kernel⟩
  | 19 => Sum.inl 2
  | 20 => Sum.inr ⟨(false, vertices_361), by decide +kernel⟩
  | 21 => Sum.inl 4
  | 22 => Sum.inl 5
  | 23 => Sum.inl 6
  | 24 => Sum.inl 7
  | 25 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 2 5 6 202
cert_row_2 1 1 2 3 4 60
cert_row_4 2 1 3 5 6 8 724 84 3
cert_row_4 3 3 4 5 6 7 496 112 3
cert_rows
cert_pivot_2 0 2 1 3
cert_heightProof 4
cert_coverFacet 0 206
cert_cover_5 0 0 0 1 2 5 14 206 3
cert_coverFacet 1 458
cert_cover_5 1 0 0 2 5 7 202 458 3
cert_coverFacet 2 898
cert_cover_2 2 6 0 7 8 386 898 3
cert_coverFacet 3 124
cert_cover_5 3 1 1 2 3 5 60 124 3
cert_coverFacet 4 724
cert_cover_5 4 2 1 3 5 6 84 724 3
cert_coverFacet 5 496
cert_cover_5 5 3 3 4 5 6 112 496 3
cert_coverFacet 6 912
cert_cover_2 6 6 3 7 8 400 912 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0940

end
end BundlePart1

section BundlePart2
/- Source: ProjectionCertificates/R_one_six_0941.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0941

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 647, 779, 533, 361, 817, 206, 458, 898, 124, 212, 916, 496, 7, 11, 515, 21, 517, 41, 265, 49, 529, 289, 769, 14, 134, 202, 266, 386, 642, 770, 60, 76, 84, 148, 532, 196, 644, 104, 328, 112, 304, 208, 400, 784, 352, 448, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_647, vertices_779, vertices_533, vertices_361, vertices_817, vertices_206, vertices_458, vertices_898, vertices_124, vertices_212, vertices_916, vertices_496] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_515, vertices_21, vertices_517, vertices_41, vertices_265, vertices_49, vertices_529, vertices_289, vertices_769, vertices_14, vertices_134, vertices_202, vertices_266, vertices_386, vertices_642, vertices_770, vertices_60, vertices_76, vertices_84, vertices_148, vertices_532, vertices_196, vertices_644, vertices_104, vertices_328, vertices_112, vertices_304, vertices_208, vertices_400, vertices_784, vertices_352, vertices_448, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_647), (false, vertices_779), (false, vertices_533), (false, vertices_361), (false, vertices_817), (true, vertices_202), (true, vertices_386), (true, vertices_76), (true, vertices_84), (true, vertices_148), (true, vertices_196), (true, vertices_112), (true, vertices_208), (true, vertices_400), (true, vertices_448), (true, vertices_896)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 16 11 19 13 21 22 23 24 25
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 14 else
  if p.val = (false, vertices_647) then 12 else
  if p.val = (false, vertices_779) then 17 else
  if p.val = (false, vertices_533) then 0 else
  if p.val = (false, vertices_361) then 20 else
  if p.val = (false, vertices_817) then 15 else
  if p.val = (true, vertices_202) then 18 else
  if p.val = (true, vertices_386) then 1 else
  if p.val = (true, vertices_76) then 2 else
  if p.val = (true, vertices_84) then 3 else
  if p.val = (true, vertices_148) then 4 else
  if p.val = (true, vertices_196) then 5 else
  if p.val = (true, vertices_112) then 6 else
  if p.val = (true, vertices_208) then 7 else
  if p.val = (true, vertices_400) then 8 else
  if p.val = (true, vertices_448) then 9 else
  if p.val = (true, vertices_896) then 10 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_533), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_386), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_76), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_84), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_148), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_196), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_112), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_208), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_400), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_448), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_896), by decide +kernel⟩
  | 11 => Sum.inl 1
  | 12 => Sum.inr ⟨(false, vertices_647), by decide +kernel⟩
  | 13 => Sum.inl 3
  | 14 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 15 => Sum.inr ⟨(false, vertices_817), by decide +kernel⟩
  | 16 => Sum.inl 0
  | 17 => Sum.inr ⟨(false, vertices_779), by decide +kernel⟩
  | 18 => Sum.inr ⟨(true, vertices_202), by decide +kernel⟩
  | 19 => Sum.inl 2
  | 20 => Sum.inr ⟨(false, vertices_361), by decide +kernel⟩
  | 21 => Sum.inl 4
  | 22 => Sum.inl 5
  | 23 => Sum.inl 6
  | 24 => Sum.inl 7
  | 25 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 2 5 6 202
cert_row_2 1 1 2 3 4 60
cert_row_4 2 1 3 6 7 8 916 148 3
cert_row_4 3 3 4 5 6 7 496 112 3
cert_rows
cert_pivot_2 0 2 1 3
cert_heightProof 4
cert_coverFacet 0 206
cert_cover_5 0 0 0 1 2 5 14 206 3
cert_coverFacet 1 458
cert_cover_5 1 0 0 2 5 7 202 458 3
cert_coverFacet 2 898
cert_cover_2 2 6 0 7 8 386 898 3
cert_coverFacet 3 124
cert_cover_5 3 1 1 2 3 5 60 124 3
cert_coverFacet 4 212
cert_cover_2 4 3 1 5 6 84 212 3
cert_coverFacet 5 916
cert_cover_5 5 2 1 3 6 7 148 916 3
cert_coverFacet 6 496
cert_cover_5 6 3 3 4 5 6 112 496 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0941

end
end BundlePart2

section BundlePart3
/- Source: ProjectionCertificates/R_one_six_0942.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0942

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 647, 203, 789, 121, 721, 782, 458, 898, 364, 308, 880, 960, 7, 11, 131, 21, 517, 57, 73, 81, 529, 193, 641, 14, 518, 202, 266, 386, 642, 770, 44, 268, 52, 276, 292, 772, 104, 328, 112, 304, 592, 784, 352, 448, 704, 832, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_647, vertices_203, vertices_789, vertices_121, vertices_721, vertices_782, vertices_458, vertices_898, vertices_364, vertices_308, vertices_880, vertices_960] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_131, vertices_21, vertices_517, vertices_57, vertices_73, vertices_81, vertices_529, vertices_193, vertices_641, vertices_14, vertices_518, vertices_202, vertices_266, vertices_386, vertices_642, vertices_770, vertices_44, vertices_268, vertices_52, vertices_276, vertices_292, vertices_772, vertices_104, vertices_328, vertices_112, vertices_304, vertices_592, vertices_784, vertices_352, vertices_448, vertices_704, vertices_832, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_647), (false, vertices_203), (false, vertices_789), (false, vertices_121), (false, vertices_721), (true, vertices_266), (true, vertices_386), (true, vertices_770), (true, vertices_268), (true, vertices_292), (true, vertices_328), (true, vertices_304), (true, vertices_352), (true, vertices_448), (true, vertices_832), (true, vertices_896)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 11 14 16 19 21 22 23 24 25
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 17 else
  if p.val = (false, vertices_647) then 12 else
  if p.val = (false, vertices_203) then 13 else
  if p.val = (false, vertices_789) then 15 else
  if p.val = (false, vertices_121) then 18 else
  if p.val = (false, vertices_721) then 20 else
  if p.val = (true, vertices_266) then 0 else
  if p.val = (true, vertices_386) then 1 else
  if p.val = (true, vertices_770) then 2 else
  if p.val = (true, vertices_268) then 3 else
  if p.val = (true, vertices_292) then 4 else
  if p.val = (true, vertices_328) then 5 else
  if p.val = (true, vertices_304) then 6 else
  if p.val = (true, vertices_352) then 7 else
  if p.val = (true, vertices_448) then 8 else
  if p.val = (true, vertices_832) then 9 else
  if p.val = (true, vertices_896) then 10 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_266), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_386), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_770), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_268), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_292), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_328), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_304), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_352), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_448), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_832), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_896), by decide +kernel⟩
  | 11 => Sum.inl 0
  | 12 => Sum.inr ⟨(false, vertices_647), by decide +kernel⟩
  | 13 => Sum.inr ⟨(false, vertices_203), by decide +kernel⟩
  | 14 => Sum.inl 1
  | 15 => Sum.inr ⟨(false, vertices_789), by decide +kernel⟩
  | 16 => Sum.inl 2
  | 17 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 18 => Sum.inr ⟨(false, vertices_121), by decide +kernel⟩
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
cert_row_2 0 0 2 5 6 202
cert_row_4 1 0 1 2 7 8 782 14 3
cert_row_4 2 1 2 4 5 7 364 44 3
cert_row_4 3 3 4 5 7 8 880 112 3
cert_rows
cert_pivot_2 6 0 1 3
cert_heightProof 4
cert_coverFacet 0 782
cert_cover_5 0 1 0 1 2 7 14 782 3
cert_coverFacet 1 458
cert_cover_5 1 0 0 2 5 7 202 458 3
cert_coverFacet 2 898
cert_cover_2 2 6 0 7 8 386 898 3
cert_coverFacet 3 364
cert_cover_5 3 2 1 2 4 5 44 364 3
cert_coverFacet 4 308
cert_cover_2 4 3 1 4 7 52 308 3
cert_coverFacet 5 880
cert_cover_5 5 3 3 4 5 7 112 880 3
cert_coverFacet 6 960
cert_cover_2 6 6 5 7 8 448 960 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0942

end
end BundlePart3

section BundlePart4
/- Source: ProjectionCertificates/R_one_six_0943.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0943

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 647, 203, 789, 121, 721, 782, 458, 898, 364, 308, 496, 912, 7, 11, 131, 21, 517, 57, 73, 81, 529, 193, 641, 14, 518, 202, 266, 386, 642, 770, 44, 268, 52, 276, 292, 772, 104, 328, 112, 304, 208, 400, 656, 784, 352, 448, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_647, vertices_203, vertices_789, vertices_121, vertices_721, vertices_782, vertices_458, vertices_898, vertices_364, vertices_308, vertices_496, vertices_912] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_131, vertices_21, vertices_517, vertices_57, vertices_73, vertices_81, vertices_529, vertices_193, vertices_641, vertices_14, vertices_518, vertices_202, vertices_266, vertices_386, vertices_642, vertices_770, vertices_44, vertices_268, vertices_52, vertices_276, vertices_292, vertices_772, vertices_104, vertices_328, vertices_112, vertices_304, vertices_208, vertices_400, vertices_656, vertices_784, vertices_352, vertices_448, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_647), (false, vertices_203), (false, vertices_789), (false, vertices_121), (false, vertices_721), (true, vertices_266), (true, vertices_386), (true, vertices_770), (true, vertices_268), (true, vertices_292), (true, vertices_328), (true, vertices_304), (true, vertices_400), (true, vertices_352), (true, vertices_448), (true, vertices_896)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 11 14 16 19 21 22 23 24 25
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 17 else
  if p.val = (false, vertices_647) then 12 else
  if p.val = (false, vertices_203) then 13 else
  if p.val = (false, vertices_789) then 15 else
  if p.val = (false, vertices_121) then 18 else
  if p.val = (false, vertices_721) then 20 else
  if p.val = (true, vertices_266) then 0 else
  if p.val = (true, vertices_386) then 1 else
  if p.val = (true, vertices_770) then 2 else
  if p.val = (true, vertices_268) then 3 else
  if p.val = (true, vertices_292) then 4 else
  if p.val = (true, vertices_328) then 5 else
  if p.val = (true, vertices_304) then 6 else
  if p.val = (true, vertices_400) then 7 else
  if p.val = (true, vertices_352) then 8 else
  if p.val = (true, vertices_448) then 9 else
  if p.val = (true, vertices_896) then 10 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_266), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_386), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_770), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_268), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_292), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_328), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_304), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_400), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_352), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_448), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_896), by decide +kernel⟩
  | 11 => Sum.inl 0
  | 12 => Sum.inr ⟨(false, vertices_647), by decide +kernel⟩
  | 13 => Sum.inr ⟨(false, vertices_203), by decide +kernel⟩
  | 14 => Sum.inl 1
  | 15 => Sum.inr ⟨(false, vertices_789), by decide +kernel⟩
  | 16 => Sum.inl 2
  | 17 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 18 => Sum.inr ⟨(false, vertices_121), by decide +kernel⟩
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
cert_row_4 0 0 1 2 7 8 782 14 3
cert_row_2 1 0 2 5 6 202
cert_row_4 2 1 2 4 5 7 364 44 3
cert_row_4 3 3 4 5 6 7 496 112 3
cert_rows
cert_pivot_2 8 0 1 3
cert_heightProof 4
cert_coverFacet 0 782
cert_cover_5 0 0 0 1 2 7 14 782 3
cert_coverFacet 1 458
cert_cover_5 1 1 0 2 5 7 202 458 3
cert_coverFacet 2 898
cert_cover_2 2 6 0 7 8 386 898 3
cert_coverFacet 3 364
cert_cover_5 3 2 1 2 4 5 44 364 3
cert_coverFacet 4 308
cert_cover_2 4 3 1 4 7 52 308 3
cert_coverFacet 5 496
cert_cover_5 5 3 3 4 5 6 112 496 3
cert_coverFacet 6 912
cert_cover_2 6 6 3 7 8 400 912 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0943

end
end BundlePart4

section BundlePart5
/- Source: ProjectionCertificates/R_one_six_0944.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0944

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 519, 779, 661, 361, 817, 206, 902, 458, 124, 212, 496, 912, 7, 11, 515, 21, 517, 41, 265, 49, 529, 289, 769, 14, 134, 518, 202, 266, 386, 770, 60, 76, 84, 148, 196, 644, 104, 328, 112, 304, 208, 400, 656, 784, 352, 448, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_519, vertices_779, vertices_661, vertices_361, vertices_817, vertices_206, vertices_902, vertices_458, vertices_124, vertices_212, vertices_496, vertices_912] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_515, vertices_21, vertices_517, vertices_41, vertices_265, vertices_49, vertices_529, vertices_289, vertices_769, vertices_14, vertices_134, vertices_518, vertices_202, vertices_266, vertices_386, vertices_770, vertices_60, vertices_76, vertices_84, vertices_148, vertices_196, vertices_644, vertices_104, vertices_328, vertices_112, vertices_304, vertices_208, vertices_400, vertices_656, vertices_784, vertices_352, vertices_448, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_519), (false, vertices_779), (false, vertices_661), (false, vertices_361), (false, vertices_817), (true, vertices_134), (true, vertices_202), (true, vertices_386), (true, vertices_76), (true, vertices_84), (true, vertices_196), (true, vertices_112), (true, vertices_208), (true, vertices_400), (true, vertices_448), (true, vertices_896)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 16 11 19 13 21 22 23 24 25
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 14 else
  if p.val = (false, vertices_519) then 0 else
  if p.val = (false, vertices_779) then 17 else
  if p.val = (false, vertices_661) then 12 else
  if p.val = (false, vertices_361) then 20 else
  if p.val = (false, vertices_817) then 15 else
  if p.val = (true, vertices_134) then 1 else
  if p.val = (true, vertices_202) then 18 else
  if p.val = (true, vertices_386) then 2 else
  if p.val = (true, vertices_76) then 3 else
  if p.val = (true, vertices_84) then 4 else
  if p.val = (true, vertices_196) then 5 else
  if p.val = (true, vertices_112) then 6 else
  if p.val = (true, vertices_208) then 7 else
  if p.val = (true, vertices_400) then 8 else
  if p.val = (true, vertices_448) then 9 else
  if p.val = (true, vertices_896) then 10 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_519), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_134), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_386), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_76), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_84), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_196), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_112), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_208), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_400), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_448), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_896), by decide +kernel⟩
  | 11 => Sum.inl 1
  | 12 => Sum.inr ⟨(false, vertices_661), by decide +kernel⟩
  | 13 => Sum.inl 3
  | 14 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 15 => Sum.inr ⟨(false, vertices_817), by decide +kernel⟩
  | 16 => Sum.inl 0
  | 17 => Sum.inr ⟨(false, vertices_779), by decide +kernel⟩
  | 18 => Sum.inr ⟨(true, vertices_202), by decide +kernel⟩
  | 19 => Sum.inl 2
  | 20 => Sum.inr ⟨(false, vertices_361), by decide +kernel⟩
  | 21 => Sum.inl 4
  | 22 => Sum.inl 5
  | 23 => Sum.inl 6
  | 24 => Sum.inl 7
  | 25 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 6 7 8 902 134 3
cert_row_2 1 0 2 5 6 202
cert_row_2 2 1 2 3 4 60
cert_row_4 3 3 4 5 6 7 496 112 3
cert_rows
cert_pivot_2 8 0 1 3
cert_heightProof 4
cert_coverFacet 0 206
cert_cover_5 0 1 0 1 2 5 14 206 3
cert_coverFacet 1 902
cert_cover_5 1 0 0 1 6 7 134 902 3
cert_coverFacet 2 458
cert_cover_5 2 1 0 2 5 7 202 458 3
cert_coverFacet 3 124
cert_cover_5 3 2 1 2 3 5 60 124 3
cert_coverFacet 4 212
cert_cover_2 4 3 1 5 6 84 212 3
cert_coverFacet 5 496
cert_cover_5 5 3 3 4 5 6 112 496 3
cert_coverFacet 6 912
cert_cover_2 6 6 3 7 8 400 912 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0944

end
end BundlePart5

section BundlePart6
/- Source: ProjectionCertificates/R_one_six_0945.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0945

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 519, 779, 661, 361, 817, 206, 902, 458, 124, 212, 368, 976, 7, 11, 515, 21, 517, 41, 265, 49, 529, 289, 769, 14, 134, 518, 202, 266, 386, 770, 60, 76, 84, 148, 196, 644, 104, 328, 112, 304, 208, 336, 656, 784, 352, 448, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_519, vertices_779, vertices_661, vertices_361, vertices_817, vertices_206, vertices_902, vertices_458, vertices_124, vertices_212, vertices_368, vertices_976] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_515, vertices_21, vertices_517, vertices_41, vertices_265, vertices_49, vertices_529, vertices_289, vertices_769, vertices_14, vertices_134, vertices_518, vertices_202, vertices_266, vertices_386, vertices_770, vertices_60, vertices_76, vertices_84, vertices_148, vertices_196, vertices_644, vertices_104, vertices_328, vertices_112, vertices_304, vertices_208, vertices_336, vertices_656, vertices_784, vertices_352, vertices_448, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_519), (false, vertices_779), (false, vertices_661), (false, vertices_361), (false, vertices_817), (true, vertices_134), (true, vertices_202), (true, vertices_386), (true, vertices_76), (true, vertices_84), (true, vertices_196), (true, vertices_112), (true, vertices_208), (true, vertices_336), (true, vertices_448), (true, vertices_896)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 16 11 19 13 21 22 23 24 25
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 14 else
  if p.val = (false, vertices_519) then 0 else
  if p.val = (false, vertices_779) then 17 else
  if p.val = (false, vertices_661) then 12 else
  if p.val = (false, vertices_361) then 20 else
  if p.val = (false, vertices_817) then 15 else
  if p.val = (true, vertices_134) then 1 else
  if p.val = (true, vertices_202) then 18 else
  if p.val = (true, vertices_386) then 2 else
  if p.val = (true, vertices_76) then 3 else
  if p.val = (true, vertices_84) then 4 else
  if p.val = (true, vertices_196) then 5 else
  if p.val = (true, vertices_112) then 6 else
  if p.val = (true, vertices_208) then 7 else
  if p.val = (true, vertices_336) then 8 else
  if p.val = (true, vertices_448) then 9 else
  if p.val = (true, vertices_896) then 10 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_519), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_134), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_386), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_76), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_84), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_196), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_112), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_208), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_336), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_448), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_896), by decide +kernel⟩
  | 11 => Sum.inl 1
  | 12 => Sum.inr ⟨(false, vertices_661), by decide +kernel⟩
  | 13 => Sum.inl 3
  | 14 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 15 => Sum.inr ⟨(false, vertices_817), by decide +kernel⟩
  | 16 => Sum.inl 0
  | 17 => Sum.inr ⟨(false, vertices_779), by decide +kernel⟩
  | 18 => Sum.inr ⟨(true, vertices_202), by decide +kernel⟩
  | 19 => Sum.inl 2
  | 20 => Sum.inr ⟨(false, vertices_361), by decide +kernel⟩
  | 21 => Sum.inl 4
  | 22 => Sum.inl 5
  | 23 => Sum.inl 6
  | 24 => Sum.inl 7
  | 25 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 1 2 3 4 60
cert_row_2 1 0 2 5 6 202
cert_row_4 2 0 1 6 7 8 902 134 3
cert_row_4 3 3 5 6 7 8 976 208 3
cert_rows
cert_pivot_2 4 2 0 3
cert_heightProof 4
cert_coverFacet 0 206
cert_cover_5 0 1 0 1 2 5 14 206 3
cert_coverFacet 1 902
cert_cover_5 1 2 0 1 6 7 134 902 3
cert_coverFacet 2 458
cert_cover_5 2 1 0 2 5 7 202 458 3
cert_coverFacet 3 124
cert_cover_5 3 0 1 2 3 5 60 124 3
cert_coverFacet 4 212
cert_cover_2 4 3 1 5 6 84 212 3
cert_coverFacet 5 368
cert_cover_2 5 4 3 5 7 112 368 3
cert_coverFacet 6 976
cert_cover_5 6 3 3 5 6 7 208 976 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0945

end
end BundlePart6

section BundlePart7
/- Source: ProjectionCertificates/R_one_six_0946.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0946

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 519, 779, 661, 361, 177, 929, 206, 902, 458, 124, 212, 496, 7, 11, 515, 21, 517, 41, 265, 49, 145, 161, 289, 641, 769, 14, 134, 518, 202, 266, 386, 770, 60, 76, 84, 148, 196, 644, 104, 328, 112, 176, 208, 352, 416, 448, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_519, vertices_779, vertices_661, vertices_361, vertices_177, vertices_929, vertices_206, vertices_902, vertices_458, vertices_124, vertices_212, vertices_496] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_515, vertices_21, vertices_517, vertices_41, vertices_265, vertices_49, vertices_145, vertices_161, vertices_289, vertices_641, vertices_769, vertices_14, vertices_134, vertices_518, vertices_202, vertices_266, vertices_386, vertices_770, vertices_60, vertices_76, vertices_84, vertices_148, vertices_196, vertices_644, vertices_104, vertices_328, vertices_112, vertices_176, vertices_208, vertices_352, vertices_416, vertices_448, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_519), (false, vertices_779), (false, vertices_661), (false, vertices_361), (false, vertices_177), (false, vertices_929), (true, vertices_134), (true, vertices_202), (true, vertices_386), (true, vertices_76), (true, vertices_84), (true, vertices_196), (true, vertices_112), (true, vertices_208), (true, vertices_448)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 14 10 17 12 19 21 22 23 24
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 13 else
  if p.val = (false, vertices_519) then 0 else
  if p.val = (false, vertices_779) then 15 else
  if p.val = (false, vertices_661) then 11 else
  if p.val = (false, vertices_361) then 18 else
  if p.val = (false, vertices_177) then 1 else
  if p.val = (false, vertices_929) then 20 else
  if p.val = (true, vertices_134) then 2 else
  if p.val = (true, vertices_202) then 16 else
  if p.val = (true, vertices_386) then 3 else
  if p.val = (true, vertices_76) then 4 else
  if p.val = (true, vertices_84) then 5 else
  if p.val = (true, vertices_196) then 6 else
  if p.val = (true, vertices_112) then 7 else
  if p.val = (true, vertices_208) then 8 else
  if p.val = (true, vertices_448) then 9 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_519), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_177), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_134), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_386), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_76), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_84), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_196), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_112), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_208), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_448), by decide +kernel⟩
  | 10 => Sum.inl 1
  | 11 => Sum.inr ⟨(false, vertices_661), by decide +kernel⟩
  | 12 => Sum.inl 3
  | 13 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 14 => Sum.inl 0
  | 15 => Sum.inr ⟨(false, vertices_779), by decide +kernel⟩
  | 16 => Sum.inr ⟨(true, vertices_202), by decide +kernel⟩
  | 17 => Sum.inl 2
  | 18 => Sum.inr ⟨(false, vertices_361), by decide +kernel⟩
  | 19 => Sum.inl 4
  | 20 => Sum.inr ⟨(false, vertices_929), by decide +kernel⟩
  | 21 => Sum.inl 5
  | 22 => Sum.inl 6
  | 23 => Sum.inl 7
  | 24 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 6 7 8 902 134 3
cert_row_2 1 0 2 5 6 202
cert_row_2 2 1 2 3 4 60
cert_row_4 3 3 4 5 6 7 496 112 3
cert_rows
cert_pivot_2 8 0 1 3
cert_heightProof 4
cert_coverFacet 0 206
cert_cover_5 0 1 0 1 2 5 14 206 3
cert_coverFacet 1 902
cert_cover_5 1 0 0 1 6 7 134 902 3
cert_coverFacet 2 458
cert_cover_5 2 1 0 2 5 7 202 458 3
cert_coverFacet 3 124
cert_cover_5 3 2 1 2 3 5 60 124 3
cert_coverFacet 4 212
cert_cover_2 4 3 1 5 6 84 212 3
cert_coverFacet 5 496
cert_cover_5 5 3 3 4 5 6 112 496 3
cert_coveringFacets
cert_coveringProof_6
cert_certificate 4 6
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0946

end
end BundlePart7

section BundlePart8
/- Source: ProjectionCertificates/R_one_six_0947.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0947

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 199, 779, 451, 117, 361, 526, 902, 540, 724, 824, 624, 992, 7, 11, 195, 259, 53, 69, 41, 265, 97, 321, 14, 134, 518, 522, 386, 770, 28, 524, 84, 532, 196, 644, 56, 536, 296, 776, 112, 560, 592, 352, 608, 800, 448, 704, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_199, vertices_779, vertices_451, vertices_117, vertices_361, vertices_526, vertices_902, vertices_540, vertices_724, vertices_824, vertices_624, vertices_992] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_195, vertices_259, vertices_53, vertices_69, vertices_41, vertices_265, vertices_97, vertices_321, vertices_14, vertices_134, vertices_518, vertices_522, vertices_386, vertices_770, vertices_28, vertices_524, vertices_84, vertices_532, vertices_196, vertices_644, vertices_56, vertices_536, vertices_296, vertices_776, vertices_112, vertices_560, vertices_592, vertices_352, vertices_608, vertices_800, vertices_448, vertices_704, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_199), (false, vertices_779), (false, vertices_451), (false, vertices_117), (false, vertices_361), (true, vertices_518), (true, vertices_524), (true, vertices_532), (true, vertices_644), (true, vertices_536), (true, vertices_560), (true, vertices_592), (true, vertices_608), (true, vertices_800), (true, vertices_704), (true, vertices_896)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 17 11 13 20 21 22 23 24 25
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 14 else
  if p.val = (false, vertices_199) then 18 else
  if p.val = (false, vertices_779) then 15 else
  if p.val = (false, vertices_451) then 19 else
  if p.val = (false, vertices_117) then 12 else
  if p.val = (false, vertices_361) then 16 else
  if p.val = (true, vertices_518) then 0 else
  if p.val = (true, vertices_524) then 1 else
  if p.val = (true, vertices_532) then 2 else
  if p.val = (true, vertices_644) then 3 else
  if p.val = (true, vertices_536) then 4 else
  if p.val = (true, vertices_560) then 5 else
  if p.val = (true, vertices_592) then 6 else
  if p.val = (true, vertices_608) then 7 else
  if p.val = (true, vertices_800) then 8 else
  if p.val = (true, vertices_704) then 9 else
  if p.val = (true, vertices_896) then 10 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_518), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_524), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_532), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_644), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_536), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_560), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_592), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_608), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_800), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_704), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_896), by decide +kernel⟩
  | 11 => Sum.inl 1
  | 12 => Sum.inr ⟨(false, vertices_117), by decide +kernel⟩
  | 13 => Sum.inl 2
  | 14 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 15 => Sum.inr ⟨(false, vertices_779), by decide +kernel⟩
  | 16 => Sum.inr ⟨(false, vertices_361), by decide +kernel⟩
  | 17 => Sum.inl 0
  | 18 => Sum.inr ⟨(false, vertices_199), by decide +kernel⟩
  | 19 => Sum.inr ⟨(false, vertices_451), by decide +kernel⟩
  | 20 => Sum.inl 3
  | 21 => Sum.inl 4
  | 22 => Sum.inl 5
  | 23 => Sum.inl 6
  | 24 => Sum.inl 7
  | 25 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 6 7 8 902 134 3
cert_row_4 1 1 3 5 6 8 724 84 3
cert_row_4 2 2 3 4 7 8 824 56 3
cert_row_4 3 4 5 6 7 8 992 352 2
cert_rows
cert_pivot_2 0 1 2 4
cert_heightProof 4
cert_coverFacet 0 526
cert_cover_2 0 1 0 2 8 14 526 3
cert_coverFacet 1 902
cert_cover_5 1 0 0 1 6 7 134 902 3
cert_coverFacet 2 540
cert_cover_2 2 2 1 3 8 28 540 3
cert_coverFacet 3 724
cert_cover_5 3 1 1 3 5 6 84 724 3
cert_coverFacet 4 824
cert_cover_5 4 2 2 3 4 7 56 824 3
cert_coverFacet 5 624
cert_cover_2 5 4 3 5 8 112 624 3
cert_coverFacet 6 992
cert_cover_5 6 3 4 5 6 7 352 992 2
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0947

end
end BundlePart8

section BundlePart9
/- Source: ProjectionCertificates/R_one_six_0948.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0948

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 199, 779, 451, 117, 361, 526, 902, 540, 724, 824, 496, 912, 7, 11, 195, 259, 53, 69, 41, 265, 97, 321, 14, 134, 518, 522, 386, 770, 28, 524, 84, 532, 196, 644, 56, 536, 296, 776, 112, 304, 208, 400, 656, 784, 352, 448, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_199, vertices_779, vertices_451, vertices_117, vertices_361, vertices_526, vertices_902, vertices_540, vertices_724, vertices_824, vertices_496, vertices_912] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_195, vertices_259, vertices_53, vertices_69, vertices_41, vertices_265, vertices_97, vertices_321, vertices_14, vertices_134, vertices_518, vertices_522, vertices_386, vertices_770, vertices_28, vertices_524, vertices_84, vertices_532, vertices_196, vertices_644, vertices_56, vertices_536, vertices_296, vertices_776, vertices_112, vertices_304, vertices_208, vertices_400, vertices_656, vertices_784, vertices_352, vertices_448, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_199), (false, vertices_779), (false, vertices_451), (false, vertices_117), (false, vertices_361), (true, vertices_518), (true, vertices_524), (true, vertices_532), (true, vertices_644), (true, vertices_536), (true, vertices_304), (true, vertices_208), (true, vertices_400), (true, vertices_656), (true, vertices_784), (true, vertices_896)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 17 11 13 20 21 22 23 24 25
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 14 else
  if p.val = (false, vertices_199) then 18 else
  if p.val = (false, vertices_779) then 15 else
  if p.val = (false, vertices_451) then 19 else
  if p.val = (false, vertices_117) then 12 else
  if p.val = (false, vertices_361) then 16 else
  if p.val = (true, vertices_518) then 0 else
  if p.val = (true, vertices_524) then 1 else
  if p.val = (true, vertices_532) then 2 else
  if p.val = (true, vertices_644) then 3 else
  if p.val = (true, vertices_536) then 4 else
  if p.val = (true, vertices_304) then 5 else
  if p.val = (true, vertices_208) then 6 else
  if p.val = (true, vertices_400) then 7 else
  if p.val = (true, vertices_656) then 8 else
  if p.val = (true, vertices_784) then 9 else
  if p.val = (true, vertices_896) then 10 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_518), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_524), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_532), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_644), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_536), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_304), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_208), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_400), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_656), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_784), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_896), by decide +kernel⟩
  | 11 => Sum.inl 1
  | 12 => Sum.inr ⟨(false, vertices_117), by decide +kernel⟩
  | 13 => Sum.inl 2
  | 14 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 15 => Sum.inr ⟨(false, vertices_779), by decide +kernel⟩
  | 16 => Sum.inr ⟨(false, vertices_361), by decide +kernel⟩
  | 17 => Sum.inl 0
  | 18 => Sum.inr ⟨(false, vertices_199), by decide +kernel⟩
  | 19 => Sum.inr ⟨(false, vertices_451), by decide +kernel⟩
  | 20 => Sum.inl 3
  | 21 => Sum.inl 4
  | 22 => Sum.inl 5
  | 23 => Sum.inl 6
  | 24 => Sum.inl 7
  | 25 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 6 7 8 902 134 3
cert_row_4 1 1 3 5 6 8 724 84 3
cert_row_4 2 2 3 4 7 8 824 56 3
cert_row_4 3 3 4 5 6 7 496 112 3
cert_rows
cert_pivot_2 0 1 2 3
cert_heightProof 4
cert_coverFacet 0 526
cert_cover_2 0 1 0 2 8 14 526 3
cert_coverFacet 1 902
cert_cover_5 1 0 0 1 6 7 134 902 3
cert_coverFacet 2 540
cert_cover_2 2 2 1 3 8 28 540 3
cert_coverFacet 3 724
cert_cover_5 3 1 1 3 5 6 84 724 3
cert_coverFacet 4 824
cert_cover_5 4 2 2 3 4 7 56 824 3
cert_coverFacet 5 496
cert_cover_5 5 3 3 4 5 6 112 496 3
cert_coverFacet 6 912
cert_cover_2 6 6 3 7 8 400 912 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0948

end
end BundlePart9

section BundlePart10
/- Source: ProjectionCertificates/R_one_six_0949.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0949

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 199, 779, 451, 117, 361, 526, 902, 540, 724, 312, 920, 496, 7, 11, 195, 259, 53, 69, 41, 265, 97, 321, 14, 134, 518, 522, 386, 770, 28, 524, 84, 532, 196, 644, 56, 280, 536, 296, 776, 112, 304, 208, 400, 656, 352, 448, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_199, vertices_779, vertices_451, vertices_117, vertices_361, vertices_526, vertices_902, vertices_540, vertices_724, vertices_312, vertices_920, vertices_496] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_195, vertices_259, vertices_53, vertices_69, vertices_41, vertices_265, vertices_97, vertices_321, vertices_14, vertices_134, vertices_518, vertices_522, vertices_386, vertices_770, vertices_28, vertices_524, vertices_84, vertices_532, vertices_196, vertices_644, vertices_56, vertices_280, vertices_536, vertices_296, vertices_776, vertices_112, vertices_304, vertices_208, vertices_400, vertices_656, vertices_352, vertices_448, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_199), (false, vertices_779), (false, vertices_451), (false, vertices_117), (false, vertices_361), (true, vertices_518), (true, vertices_524), (true, vertices_532), (true, vertices_644), (true, vertices_280), (true, vertices_536), (true, vertices_304), (true, vertices_208), (true, vertices_400), (true, vertices_656), (true, vertices_896)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 17 11 13 20 21 22 23 24 25
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 14 else
  if p.val = (false, vertices_199) then 18 else
  if p.val = (false, vertices_779) then 15 else
  if p.val = (false, vertices_451) then 19 else
  if p.val = (false, vertices_117) then 12 else
  if p.val = (false, vertices_361) then 16 else
  if p.val = (true, vertices_518) then 0 else
  if p.val = (true, vertices_524) then 1 else
  if p.val = (true, vertices_532) then 2 else
  if p.val = (true, vertices_644) then 3 else
  if p.val = (true, vertices_280) then 4 else
  if p.val = (true, vertices_536) then 5 else
  if p.val = (true, vertices_304) then 6 else
  if p.val = (true, vertices_208) then 7 else
  if p.val = (true, vertices_400) then 8 else
  if p.val = (true, vertices_656) then 9 else
  if p.val = (true, vertices_896) then 10 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_518), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_524), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_532), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_644), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_280), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_536), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_304), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_208), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_400), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_656), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_896), by decide +kernel⟩
  | 11 => Sum.inl 1
  | 12 => Sum.inr ⟨(false, vertices_117), by decide +kernel⟩
  | 13 => Sum.inl 2
  | 14 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 15 => Sum.inr ⟨(false, vertices_779), by decide +kernel⟩
  | 16 => Sum.inr ⟨(false, vertices_361), by decide +kernel⟩
  | 17 => Sum.inl 0
  | 18 => Sum.inr ⟨(false, vertices_199), by decide +kernel⟩
  | 19 => Sum.inr ⟨(false, vertices_451), by decide +kernel⟩
  | 20 => Sum.inl 3
  | 21 => Sum.inl 4
  | 22 => Sum.inl 5
  | 23 => Sum.inl 6
  | 24 => Sum.inl 7
  | 25 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 6 7 8 902 134 3
cert_row_4 1 1 3 5 6 8 724 84 3
cert_row_4 2 2 3 6 7 8 920 280 2
cert_row_4 3 3 4 5 6 7 496 112 3
cert_rows
cert_pivot_2 0 1 2 3
cert_heightProof 4
cert_coverFacet 0 526
cert_cover_2 0 1 0 2 8 14 526 3
cert_coverFacet 1 902
cert_cover_5 1 0 0 1 6 7 134 902 3
cert_coverFacet 2 540
cert_cover_2 2 2 1 3 8 28 540 3
cert_coverFacet 3 724
cert_cover_5 3 1 1 3 5 6 84 724 3
cert_coverFacet 4 312
cert_cover_2 4 3 2 4 7 56 312 3
cert_coverFacet 5 920
cert_cover_5 5 2 2 3 6 7 280 920 2
cert_coverFacet 6 496
cert_cover_5 6 3 3 4 5 6 112 496 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0949

end
end BundlePart10

section BundlePart11
/- Source: ProjectionCertificates/R_one_six_0952.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0952

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 775, 267, 341, 121, 457, 654, 394, 962, 556, 820, 744, 880, 7, 11, 259, 21, 261, 57, 73, 265, 81, 321, 14, 518, 138, 266, 386, 642, 770, 44, 524, 52, 276, 548, 772, 104, 552, 200, 392, 648, 112, 816, 336, 608, 448, 704, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_775, vertices_267, vertices_341, vertices_121, vertices_457, vertices_654, vertices_394, vertices_962, vertices_556, vertices_820, vertices_744, vertices_880] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_259, vertices_21, vertices_261, vertices_57, vertices_73, vertices_265, vertices_81, vertices_321, vertices_14, vertices_518, vertices_138, vertices_266, vertices_386, vertices_642, vertices_770, vertices_44, vertices_524, vertices_52, vertices_276, vertices_548, vertices_772, vertices_104, vertices_552, vertices_200, vertices_392, vertices_648, vertices_112, vertices_816, vertices_336, vertices_608, vertices_448, vertices_704, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_775), (false, vertices_267), (false, vertices_341), (false, vertices_121), (false, vertices_457), (true, vertices_138), (true, vertices_386), (true, vertices_642), (true, vertices_524), (true, vertices_548), (true, vertices_552), (true, vertices_648), (true, vertices_816), (true, vertices_608), (true, vertices_704), (true, vertices_832)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 11 13 15 19 21 22 23 24 25
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 16 else
  if p.val = (false, vertices_775) then 12 else
  if p.val = (false, vertices_267) then 0 else
  if p.val = (false, vertices_341) then 14 else
  if p.val = (false, vertices_121) then 17 else
  if p.val = (false, vertices_457) then 18 else
  if p.val = (true, vertices_138) then 1 else
  if p.val = (true, vertices_386) then 2 else
  if p.val = (true, vertices_642) then 3 else
  if p.val = (true, vertices_524) then 4 else
  if p.val = (true, vertices_548) then 5 else
  if p.val = (true, vertices_552) then 6 else
  if p.val = (true, vertices_648) then 7 else
  if p.val = (true, vertices_816) then 20 else
  if p.val = (true, vertices_608) then 8 else
  if p.val = (true, vertices_704) then 9 else
  if p.val = (true, vertices_832) then 10 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_267), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_138), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_386), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_642), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_524), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_548), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_552), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_648), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_608), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_704), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_832), by decide +kernel⟩
  | 11 => Sum.inl 0
  | 12 => Sum.inr ⟨(false, vertices_775), by decide +kernel⟩
  | 13 => Sum.inl 1
  | 14 => Sum.inr ⟨(false, vertices_341), by decide +kernel⟩
  | 15 => Sum.inl 2
  | 16 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 17 => Sum.inr ⟨(false, vertices_121), by decide +kernel⟩
  | 18 => Sum.inr ⟨(false, vertices_457), by decide +kernel⟩
  | 19 => Sum.inl 3
  | 20 => Sum.inr ⟨(true, vertices_816), by decide +kernel⟩
  | 21 => Sum.inl 4
  | 22 => Sum.inl 5
  | 23 => Sum.inl 6
  | 24 => Sum.inl 7
  | 25 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 3 4 7 8 816
cert_row_4 1 0 1 2 6 8 654 14 3
cert_row_4 2 0 5 6 7 8 962 386 1
cert_row_4 3 2 4 5 6 8 744 104 3
cert_rows
cert_pivot_2 3 1 0 2
cert_heightProof 4
cert_coverFacet 0 654
cert_cover_5 0 1 0 1 2 6 14 654 3
cert_coverFacet 1 394
cert_cover_2 1 2 0 6 7 138 394 3
cert_coverFacet 2 962
cert_cover_5 2 2 0 5 6 7 386 962 1
cert_coverFacet 3 556
cert_cover_2 3 2 1 4 8 44 556 3
cert_coverFacet 4 820
cert_cover_5 4 0 1 3 4 7 52 820 3
cert_coverFacet 5 744
cert_cover_5 5 3 2 4 5 6 104 744 3
cert_coverFacet 6 880
cert_cover_5 6 0 3 4 5 7 112 880 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0952

end
end BundlePart11

section BundlePart12
/- Source: ProjectionCertificates/R_one_six_0953.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0953

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 775, 267, 341, 121, 457, 526, 906, 684, 820, 232, 752, 976, 7, 11, 259, 21, 261, 57, 73, 265, 81, 321, 14, 518, 266, 522, 770, 44, 524, 52, 276, 548, 772, 104, 168, 200, 392, 648, 112, 560, 720, 336, 784, 224, 672, 448, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_775, vertices_267, vertices_341, vertices_121, vertices_457, vertices_526, vertices_906, vertices_684, vertices_820, vertices_232, vertices_752, vertices_976] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_259, vertices_21, vertices_261, vertices_57, vertices_73, vertices_265, vertices_81, vertices_321, vertices_14, vertices_518, vertices_266, vertices_522, vertices_770, vertices_44, vertices_524, vertices_52, vertices_276, vertices_548, vertices_772, vertices_104, vertices_168, vertices_200, vertices_392, vertices_648, vertices_112, vertices_560, vertices_720, vertices_336, vertices_784, vertices_224, vertices_672, vertices_448, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_775), (false, vertices_267), (false, vertices_341), (false, vertices_121), (false, vertices_457), (true, vertices_522), (true, vertices_524), (true, vertices_548), (true, vertices_168), (true, vertices_648), (true, vertices_560), (true, vertices_720), (true, vertices_784), (true, vertices_224), (true, vertices_672), (true, vertices_896)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 11 13 15 19 21 22 23 24 25
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 16 else
  if p.val = (false, vertices_775) then 12 else
  if p.val = (false, vertices_267) then 0 else
  if p.val = (false, vertices_341) then 14 else
  if p.val = (false, vertices_121) then 17 else
  if p.val = (false, vertices_457) then 18 else
  if p.val = (true, vertices_522) then 1 else
  if p.val = (true, vertices_524) then 2 else
  if p.val = (true, vertices_548) then 3 else
  if p.val = (true, vertices_168) then 4 else
  if p.val = (true, vertices_648) then 5 else
  if p.val = (true, vertices_560) then 6 else
  if p.val = (true, vertices_720) then 20 else
  if p.val = (true, vertices_784) then 7 else
  if p.val = (true, vertices_224) then 8 else
  if p.val = (true, vertices_672) then 9 else
  if p.val = (true, vertices_896) then 10 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_267), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_522), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_524), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_548), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_168), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_648), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_560), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_784), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_224), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_672), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_896), by decide +kernel⟩
  | 11 => Sum.inl 0
  | 12 => Sum.inr ⟨(false, vertices_775), by decide +kernel⟩
  | 13 => Sum.inl 1
  | 14 => Sum.inr ⟨(false, vertices_341), by decide +kernel⟩
  | 15 => Sum.inl 2
  | 16 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 17 => Sum.inr ⟨(false, vertices_121), by decide +kernel⟩
  | 18 => Sum.inr ⟨(false, vertices_457), by decide +kernel⟩
  | 19 => Sum.inl 3
  | 20 => Sum.inr ⟨(true, vertices_720), by decide +kernel⟩
  | 21 => Sum.inl 4
  | 22 => Sum.inl 5
  | 23 => Sum.inl 6
  | 24 => Sum.inl 7
  | 25 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 3 5 6 8 720
cert_row_4 1 0 2 6 7 8 906 266 2
cert_row_4 2 1 2 4 6 8 684 44 3
cert_row_4 3 1 3 4 7 8 820 52 3
cert_rows
cert_pivot_2 5 0 2 1
cert_heightProof 4
cert_coverFacet 0 526
cert_cover_2 0 1 0 2 8 14 526 3
cert_coverFacet 1 906
cert_cover_5 1 1 0 2 6 7 266 906 2
cert_coverFacet 2 684
cert_cover_5 2 2 1 2 4 6 44 684 3
cert_coverFacet 3 820
cert_cover_5 3 3 1 3 4 7 52 820 3
cert_coverFacet 4 232
cert_cover_2 4 4 2 5 6 104 232 3
cert_coverFacet 5 752
cert_cover_5 5 0 3 4 5 6 112 752 3
cert_coverFacet 6 976
cert_cover_5 6 0 3 5 6 7 720 976 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0953

end
end BundlePart12

section BundlePart13
/- Source: ProjectionCertificates/R_one_six_0954.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0954

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 775, 267, 341, 121, 457, 526, 906, 556, 692, 916, 744, 496, 7, 11, 259, 21, 261, 57, 73, 265, 81, 321, 14, 518, 266, 522, 770, 44, 524, 52, 660, 276, 548, 772, 104, 552, 200, 392, 648, 112, 176, 336, 400, 224, 672, 448, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_775, vertices_267, vertices_341, vertices_121, vertices_457, vertices_526, vertices_906, vertices_556, vertices_692, vertices_916, vertices_744, vertices_496] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_259, vertices_21, vertices_261, vertices_57, vertices_73, vertices_265, vertices_81, vertices_321, vertices_14, vertices_518, vertices_266, vertices_522, vertices_770, vertices_44, vertices_524, vertices_52, vertices_660, vertices_276, vertices_548, vertices_772, vertices_104, vertices_552, vertices_200, vertices_392, vertices_648, vertices_112, vertices_176, vertices_336, vertices_400, vertices_224, vertices_672, vertices_448, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_775), (false, vertices_267), (false, vertices_341), (false, vertices_121), (false, vertices_457), (true, vertices_522), (true, vertices_524), (true, vertices_660), (true, vertices_548), (true, vertices_552), (true, vertices_648), (true, vertices_176), (true, vertices_400), (true, vertices_224), (true, vertices_672), (true, vertices_896)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 11 17 13 20 21 22 23 24 25
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 14 else
  if p.val = (false, vertices_775) then 12 else
  if p.val = (false, vertices_267) then 0 else
  if p.val = (false, vertices_341) then 18 else
  if p.val = (false, vertices_121) then 15 else
  if p.val = (false, vertices_457) then 16 else
  if p.val = (true, vertices_522) then 1 else
  if p.val = (true, vertices_524) then 2 else
  if p.val = (true, vertices_660) then 19 else
  if p.val = (true, vertices_548) then 3 else
  if p.val = (true, vertices_552) then 4 else
  if p.val = (true, vertices_648) then 5 else
  if p.val = (true, vertices_176) then 6 else
  if p.val = (true, vertices_400) then 7 else
  if p.val = (true, vertices_224) then 8 else
  if p.val = (true, vertices_672) then 9 else
  if p.val = (true, vertices_896) then 10 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_267), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_522), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_524), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_548), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_552), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_648), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_176), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_400), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_224), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_672), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_896), by decide +kernel⟩
  | 11 => Sum.inl 0
  | 12 => Sum.inr ⟨(false, vertices_775), by decide +kernel⟩
  | 13 => Sum.inl 2
  | 14 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 15 => Sum.inr ⟨(false, vertices_121), by decide +kernel⟩
  | 16 => Sum.inr ⟨(false, vertices_457), by decide +kernel⟩
  | 17 => Sum.inl 1
  | 18 => Sum.inr ⟨(false, vertices_341), by decide +kernel⟩
  | 19 => Sum.inr ⟨(true, vertices_660), by decide +kernel⟩
  | 20 => Sum.inl 3
  | 21 => Sum.inl 4
  | 22 => Sum.inl 5
  | 23 => Sum.inl 6
  | 24 => Sum.inl 7
  | 25 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 1 3 6 8 660
cert_row_4 1 0 2 6 7 8 906 266 2
cert_row_4 2 2 4 5 6 8 744 104 3
cert_row_4 3 3 4 5 6 7 496 112 3
cert_rows
cert_pivot_2 1 0 2 3
cert_heightProof 4
cert_coverFacet 0 526
cert_cover_2 0 1 0 2 8 14 526 3
cert_coverFacet 1 906
cert_cover_5 1 1 0 2 6 7 266 906 2
cert_coverFacet 2 556
cert_cover_2 2 2 1 4 8 44 556 3
cert_coverFacet 3 692
cert_cover_5 3 0 1 3 4 6 52 692 3
cert_coverFacet 4 916
cert_cover_5 4 0 1 3 6 7 660 916 3
cert_coverFacet 5 744
cert_cover_5 5 2 2 4 5 6 104 744 3
cert_coverFacet 6 496
cert_cover_5 6 3 3 4 5 6 112 496 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0954

end
end BundlePart13

section BundlePart14
/- Source: ProjectionCertificates/R_one_six_0955.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0955

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 775, 267, 533, 121, 457, 849, 654, 394, 962, 236, 692, 752, 7, 11, 259, 21, 517, 57, 73, 265, 81, 529, 321, 769, 14, 518, 138, 266, 386, 642, 770, 44, 140, 52, 532, 164, 644, 104, 200, 392, 112, 688, 592, 224, 448, 704, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_775, vertices_267, vertices_533, vertices_121, vertices_457, vertices_849, vertices_654, vertices_394, vertices_962, vertices_236, vertices_692, vertices_752] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_259, vertices_21, vertices_517, vertices_57, vertices_73, vertices_265, vertices_81, vertices_529, vertices_321, vertices_769, vertices_14, vertices_518, vertices_138, vertices_266, vertices_386, vertices_642, vertices_770, vertices_44, vertices_140, vertices_52, vertices_532, vertices_164, vertices_644, vertices_104, vertices_200, vertices_392, vertices_112, vertices_688, vertices_592, vertices_224, vertices_448, vertices_704, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_775), (false, vertices_267), (false, vertices_533), (false, vertices_121), (false, vertices_457), (false, vertices_849), (true, vertices_138), (true, vertices_386), (true, vertices_642), (true, vertices_140), (true, vertices_164), (true, vertices_644), (true, vertices_688), (true, vertices_224), (true, vertices_704)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 10 12 13 17 20 21 22 23 24
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 14 else
  if p.val = (false, vertices_775) then 11 else
  if p.val = (false, vertices_267) then 0 else
  if p.val = (false, vertices_533) then 1 else
  if p.val = (false, vertices_121) then 15 else
  if p.val = (false, vertices_457) then 16 else
  if p.val = (false, vertices_849) then 18 else
  if p.val = (true, vertices_138) then 2 else
  if p.val = (true, vertices_386) then 3 else
  if p.val = (true, vertices_642) then 4 else
  if p.val = (true, vertices_140) then 5 else
  if p.val = (true, vertices_164) then 6 else
  if p.val = (true, vertices_644) then 7 else
  if p.val = (true, vertices_688) then 19 else
  if p.val = (true, vertices_224) then 8 else
  if p.val = (true, vertices_704) then 9 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_267), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_533), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_138), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_386), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_642), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_140), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_164), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_644), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_224), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_704), by decide +kernel⟩
  | 10 => Sum.inl 0
  | 11 => Sum.inr ⟨(false, vertices_775), by decide +kernel⟩
  | 12 => Sum.inl 1
  | 13 => Sum.inl 2
  | 14 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 15 => Sum.inr ⟨(false, vertices_121), by decide +kernel⟩
  | 16 => Sum.inr ⟨(false, vertices_457), by decide +kernel⟩
  | 17 => Sum.inl 3
  | 18 => Sum.inr ⟨(false, vertices_849), by decide +kernel⟩
  | 19 => Sum.inr ⟨(true, vertices_688), by decide +kernel⟩
  | 20 => Sum.inl 4
  | 21 => Sum.inl 5
  | 22 => Sum.inl 6
  | 23 => Sum.inl 7
  | 24 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 3 4 6 8 688
cert_row_4 1 0 5 6 7 8 962 386 1
cert_row_4 2 0 1 2 6 8 654 14 3
cert_row_4 3 1 2 4 5 6 236 44 3
cert_rows
cert_pivot_2 3 7 0 1
cert_heightProof 4
cert_coverFacet 0 654
cert_cover_5 0 2 0 1 2 6 14 654 3
cert_coverFacet 1 394
cert_cover_2 1 2 0 6 7 138 394 3
cert_coverFacet 2 962
cert_cover_5 2 1 0 5 6 7 386 962 1
cert_coverFacet 3 236
cert_cover_5 3 3 1 2 4 5 44 236 3
cert_coverFacet 4 692
cert_cover_5 4 0 1 3 4 6 52 692 3
cert_coverFacet 5 752
cert_cover_5 5 0 3 4 5 6 112 752 3
cert_coveringFacets
cert_coveringProof_6
cert_certificate 4 6
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0955

end
end BundlePart14

section BundlePart15
/- Source: ProjectionCertificates/R_one_six_0956.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0956

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 775, 267, 533, 121, 457, 849, 654, 906, 236, 692, 624, 992, 7, 11, 259, 21, 517, 57, 73, 265, 81, 529, 321, 769, 14, 518, 650, 266, 770, 44, 140, 52, 532, 164, 644, 104, 200, 392, 112, 560, 592, 224, 608, 672, 448, 832, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_775, vertices_267, vertices_533, vertices_121, vertices_457, vertices_849, vertices_654, vertices_906, vertices_236, vertices_692, vertices_624, vertices_992] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_259, vertices_21, vertices_517, vertices_57, vertices_73, vertices_265, vertices_81, vertices_529, vertices_321, vertices_769, vertices_14, vertices_518, vertices_650, vertices_266, vertices_770, vertices_44, vertices_140, vertices_52, vertices_532, vertices_164, vertices_644, vertices_104, vertices_200, vertices_392, vertices_112, vertices_560, vertices_592, vertices_224, vertices_608, vertices_672, vertices_448, vertices_832, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_775), (false, vertices_267), (false, vertices_533), (false, vertices_121), (false, vertices_457), (false, vertices_849), (true, vertices_650), (true, vertices_140), (true, vertices_164), (true, vertices_644), (true, vertices_560), (true, vertices_224), (true, vertices_608), (true, vertices_672), (true, vertices_896)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 10 13 14 18 20 21 22 23 24
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 15 else
  if p.val = (false, vertices_775) then 11 else
  if p.val = (false, vertices_267) then 0 else
  if p.val = (false, vertices_533) then 1 else
  if p.val = (false, vertices_121) then 16 else
  if p.val = (false, vertices_457) then 17 else
  if p.val = (false, vertices_849) then 19 else
  if p.val = (true, vertices_650) then 12 else
  if p.val = (true, vertices_140) then 2 else
  if p.val = (true, vertices_164) then 3 else
  if p.val = (true, vertices_644) then 4 else
  if p.val = (true, vertices_560) then 5 else
  if p.val = (true, vertices_224) then 6 else
  if p.val = (true, vertices_608) then 7 else
  if p.val = (true, vertices_672) then 8 else
  if p.val = (true, vertices_896) then 9 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_267), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_533), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_140), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_164), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_644), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_560), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_224), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_608), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_672), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_896), by decide +kernel⟩
  | 10 => Sum.inl 0
  | 11 => Sum.inr ⟨(false, vertices_775), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_650), by decide +kernel⟩
  | 13 => Sum.inl 1
  | 14 => Sum.inl 2
  | 15 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 16 => Sum.inr ⟨(false, vertices_121), by decide +kernel⟩
  | 17 => Sum.inr ⟨(false, vertices_457), by decide +kernel⟩
  | 18 => Sum.inl 3
  | 19 => Sum.inr ⟨(false, vertices_849), by decide +kernel⟩
  | 20 => Sum.inl 4
  | 21 => Sum.inl 5
  | 22 => Sum.inl 6
  | 23 => Sum.inl 7
  | 24 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 2 6 8 650
cert_row_4 1 1 2 4 5 6 236 44 3
cert_row_4 2 1 3 4 6 8 692 52 3
cert_row_4 3 4 5 6 7 8 992 224 3
cert_rows
cert_pivot_2 0 2 1 4
cert_heightProof 4
cert_coverFacet 0 654
cert_cover_5 0 0 0 1 2 6 14 654 3
cert_coverFacet 1 906
cert_cover_5 1 0 0 2 6 7 650 906 3
cert_coverFacet 2 236
cert_cover_5 2 1 1 2 4 5 44 236 3
cert_coverFacet 3 692
cert_cover_5 3 2 1 3 4 6 52 692 3
cert_coverFacet 4 624
cert_cover_2 4 4 3 5 8 112 624 3
cert_coverFacet 5 992
cert_cover_5 5 3 4 5 6 7 224 992 3
cert_coveringFacets
cert_coveringProof_6
cert_certificate 4 6
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0956

end
end BundlePart15

section BundlePart16
/- Source: ProjectionCertificates/R_one_six_0957.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0957

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 775, 267, 533, 121, 457, 849, 654, 906, 236, 692, 496, 912, 7, 11, 259, 21, 517, 57, 73, 265, 81, 529, 321, 769, 14, 518, 650, 266, 770, 44, 140, 52, 532, 164, 644, 104, 200, 392, 112, 176, 336, 400, 656, 784, 224, 448, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_775, vertices_267, vertices_533, vertices_121, vertices_457, vertices_849, vertices_654, vertices_906, vertices_236, vertices_692, vertices_496, vertices_912] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_259, vertices_21, vertices_517, vertices_57, vertices_73, vertices_265, vertices_81, vertices_529, vertices_321, vertices_769, vertices_14, vertices_518, vertices_650, vertices_266, vertices_770, vertices_44, vertices_140, vertices_52, vertices_532, vertices_164, vertices_644, vertices_104, vertices_200, vertices_392, vertices_112, vertices_176, vertices_336, vertices_400, vertices_656, vertices_784, vertices_224, vertices_448, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_775), (false, vertices_267), (false, vertices_533), (false, vertices_121), (false, vertices_457), (false, vertices_849), (true, vertices_650), (true, vertices_140), (true, vertices_164), (true, vertices_644), (true, vertices_176), (true, vertices_400), (true, vertices_656), (true, vertices_224), (true, vertices_896)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 10 13 14 18 20 21 22 23 24
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 15 else
  if p.val = (false, vertices_775) then 11 else
  if p.val = (false, vertices_267) then 0 else
  if p.val = (false, vertices_533) then 1 else
  if p.val = (false, vertices_121) then 16 else
  if p.val = (false, vertices_457) then 17 else
  if p.val = (false, vertices_849) then 19 else
  if p.val = (true, vertices_650) then 12 else
  if p.val = (true, vertices_140) then 2 else
  if p.val = (true, vertices_164) then 3 else
  if p.val = (true, vertices_644) then 4 else
  if p.val = (true, vertices_176) then 5 else
  if p.val = (true, vertices_400) then 6 else
  if p.val = (true, vertices_656) then 7 else
  if p.val = (true, vertices_224) then 8 else
  if p.val = (true, vertices_896) then 9 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_267), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_533), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_140), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_164), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_644), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_176), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_400), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_656), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_224), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_896), by decide +kernel⟩
  | 10 => Sum.inl 0
  | 11 => Sum.inr ⟨(false, vertices_775), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_650), by decide +kernel⟩
  | 13 => Sum.inl 1
  | 14 => Sum.inl 2
  | 15 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 16 => Sum.inr ⟨(false, vertices_121), by decide +kernel⟩
  | 17 => Sum.inr ⟨(false, vertices_457), by decide +kernel⟩
  | 18 => Sum.inl 3
  | 19 => Sum.inr ⟨(false, vertices_849), by decide +kernel⟩
  | 20 => Sum.inl 4
  | 21 => Sum.inl 5
  | 22 => Sum.inl 6
  | 23 => Sum.inl 7
  | 24 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 2 6 8 650
cert_row_4 1 1 2 4 5 6 236 44 3
cert_row_4 2 1 3 4 6 8 692 52 3
cert_row_4 3 3 4 5 6 7 496 112 3
cert_rows
cert_pivot_2 0 2 1 3
cert_heightProof 4
cert_coverFacet 0 654
cert_cover_5 0 0 0 1 2 6 14 654 3
cert_coverFacet 1 906
cert_cover_5 1 0 0 2 6 7 650 906 3
cert_coverFacet 2 236
cert_cover_5 2 1 1 2 4 5 44 236 3
cert_coverFacet 3 692
cert_cover_5 3 2 1 3 4 6 52 692 3
cert_coverFacet 4 496
cert_cover_5 4 3 3 4 5 6 112 496 3
cert_coverFacet 5 912
cert_cover_2 5 6 3 7 8 400 912 3
cert_coveringFacets
cert_coveringProof_6
cert_certificate 4 6
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0957

end
end BundlePart16

section BundlePart17
/- Source: ProjectionCertificates/R_one_six_0961.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0961

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 519, 779, 533, 121, 457, 849, 398, 646, 962, 236, 692, 752, 7, 11, 515, 21, 517, 57, 73, 265, 81, 529, 321, 769, 14, 134, 518, 266, 386, 642, 770, 44, 140, 52, 532, 164, 644, 104, 200, 392, 112, 688, 592, 224, 448, 704, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_519, vertices_779, vertices_533, vertices_121, vertices_457, vertices_849, vertices_398, vertices_646, vertices_962, vertices_236, vertices_692, vertices_752] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_515, vertices_21, vertices_517, vertices_57, vertices_73, vertices_265, vertices_81, vertices_529, vertices_321, vertices_769, vertices_14, vertices_134, vertices_518, vertices_266, vertices_386, vertices_642, vertices_770, vertices_44, vertices_140, vertices_52, vertices_532, vertices_164, vertices_644, vertices_104, vertices_200, vertices_392, vertices_112, vertices_688, vertices_592, vertices_224, vertices_448, vertices_704, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_519), (false, vertices_779), (false, vertices_533), (false, vertices_121), (false, vertices_457), (false, vertices_849), (true, vertices_134), (true, vertices_386), (true, vertices_642), (true, vertices_140), (true, vertices_164), (true, vertices_644), (true, vertices_688), (true, vertices_224), (true, vertices_704)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 10 12 13 17 20 21 22 23 24
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 14 else
  if p.val = (false, vertices_519) then 0 else
  if p.val = (false, vertices_779) then 11 else
  if p.val = (false, vertices_533) then 1 else
  if p.val = (false, vertices_121) then 15 else
  if p.val = (false, vertices_457) then 16 else
  if p.val = (false, vertices_849) then 18 else
  if p.val = (true, vertices_134) then 2 else
  if p.val = (true, vertices_386) then 3 else
  if p.val = (true, vertices_642) then 4 else
  if p.val = (true, vertices_140) then 5 else
  if p.val = (true, vertices_164) then 6 else
  if p.val = (true, vertices_644) then 7 else
  if p.val = (true, vertices_688) then 19 else
  if p.val = (true, vertices_224) then 8 else
  if p.val = (true, vertices_704) then 9 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_519), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_533), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_134), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_386), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_642), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_140), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_164), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_644), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_224), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_704), by decide +kernel⟩
  | 10 => Sum.inl 0
  | 11 => Sum.inr ⟨(false, vertices_779), by decide +kernel⟩
  | 12 => Sum.inl 1
  | 13 => Sum.inl 2
  | 14 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 15 => Sum.inr ⟨(false, vertices_121), by decide +kernel⟩
  | 16 => Sum.inr ⟨(false, vertices_457), by decide +kernel⟩
  | 17 => Sum.inl 3
  | 18 => Sum.inr ⟨(false, vertices_849), by decide +kernel⟩
  | 19 => Sum.inr ⟨(true, vertices_688), by decide +kernel⟩
  | 20 => Sum.inl 4
  | 21 => Sum.inl 5
  | 22 => Sum.inl 6
  | 23 => Sum.inl 7
  | 24 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 3 4 6 8 688
cert_row_4 1 0 5 6 7 8 962 386 1
cert_row_4 2 0 1 2 6 7 398 14 3
cert_row_4 3 1 2 4 5 6 236 44 3
cert_rows
cert_pivot_2 3 8 0 1
cert_heightProof 4
cert_coverFacet 0 398
cert_cover_5 0 2 0 1 2 6 14 398 3
cert_coverFacet 1 646
cert_cover_2 1 1 0 6 8 134 646 3
cert_coverFacet 2 962
cert_cover_5 2 1 0 5 6 7 386 962 1
cert_coverFacet 3 236
cert_cover_5 3 3 1 2 4 5 44 236 3
cert_coverFacet 4 692
cert_cover_5 4 0 1 3 4 6 52 692 3
cert_coverFacet 5 752
cert_cover_5 5 0 3 4 5 6 112 752 3
cert_coveringFacets
cert_coveringProof_6
cert_certificate 4 6
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0961

end
end BundlePart17

section BundlePart18
/- Source: ProjectionCertificates/R_one_six_0962.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0962

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 519, 779, 533, 121, 457, 849, 398, 902, 236, 692, 624, 992, 7, 11, 515, 21, 517, 57, 73, 265, 81, 529, 321, 769, 14, 390, 518, 266, 770, 44, 140, 52, 532, 164, 644, 104, 200, 392, 112, 560, 592, 224, 608, 672, 448, 832, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_519, vertices_779, vertices_533, vertices_121, vertices_457, vertices_849, vertices_398, vertices_902, vertices_236, vertices_692, vertices_624, vertices_992] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_515, vertices_21, vertices_517, vertices_57, vertices_73, vertices_265, vertices_81, vertices_529, vertices_321, vertices_769, vertices_14, vertices_390, vertices_518, vertices_266, vertices_770, vertices_44, vertices_140, vertices_52, vertices_532, vertices_164, vertices_644, vertices_104, vertices_200, vertices_392, vertices_112, vertices_560, vertices_592, vertices_224, vertices_608, vertices_672, vertices_448, vertices_832, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_519), (false, vertices_779), (false, vertices_533), (false, vertices_121), (false, vertices_457), (false, vertices_849), (true, vertices_390), (true, vertices_140), (true, vertices_164), (true, vertices_644), (true, vertices_560), (true, vertices_224), (true, vertices_608), (true, vertices_672), (true, vertices_896)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 10 13 14 18 20 21 22 23 24
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 15 else
  if p.val = (false, vertices_519) then 0 else
  if p.val = (false, vertices_779) then 11 else
  if p.val = (false, vertices_533) then 1 else
  if p.val = (false, vertices_121) then 16 else
  if p.val = (false, vertices_457) then 17 else
  if p.val = (false, vertices_849) then 19 else
  if p.val = (true, vertices_390) then 12 else
  if p.val = (true, vertices_140) then 2 else
  if p.val = (true, vertices_164) then 3 else
  if p.val = (true, vertices_644) then 4 else
  if p.val = (true, vertices_560) then 5 else
  if p.val = (true, vertices_224) then 6 else
  if p.val = (true, vertices_608) then 7 else
  if p.val = (true, vertices_672) then 8 else
  if p.val = (true, vertices_896) then 9 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_519), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_533), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_140), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_164), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_644), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_560), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_224), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_608), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_672), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_896), by decide +kernel⟩
  | 10 => Sum.inl 0
  | 11 => Sum.inr ⟨(false, vertices_779), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_390), by decide +kernel⟩
  | 13 => Sum.inl 1
  | 14 => Sum.inl 2
  | 15 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 16 => Sum.inr ⟨(false, vertices_121), by decide +kernel⟩
  | 17 => Sum.inr ⟨(false, vertices_457), by decide +kernel⟩
  | 18 => Sum.inl 3
  | 19 => Sum.inr ⟨(false, vertices_849), by decide +kernel⟩
  | 20 => Sum.inl 4
  | 21 => Sum.inl 5
  | 22 => Sum.inl 6
  | 23 => Sum.inl 7
  | 24 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 1 6 7 390
cert_row_4 1 1 2 4 5 6 236 44 3
cert_row_4 2 1 3 4 6 8 692 52 3
cert_row_4 3 4 5 6 7 8 992 224 3
cert_rows
cert_pivot_2 0 2 1 4
cert_heightProof 4
cert_coverFacet 0 398
cert_cover_5 0 0 0 1 2 6 14 398 3
cert_coverFacet 1 902
cert_cover_5 1 0 0 1 6 8 390 902 3
cert_coverFacet 2 236
cert_cover_5 2 1 1 2 4 5 44 236 3
cert_coverFacet 3 692
cert_cover_5 3 2 1 3 4 6 52 692 3
cert_coverFacet 4 624
cert_cover_2 4 4 3 5 8 112 624 3
cert_coverFacet 5 992
cert_cover_5 5 3 4 5 6 7 224 992 3
cert_coveringFacets
cert_coveringProof_6
cert_certificate 4 6
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0962

end
end BundlePart18

section BundlePart19
/- Source: ProjectionCertificates/R_one_six_0963.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0963

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 519, 779, 533, 121, 457, 849, 398, 902, 236, 692, 496, 912, 7, 11, 515, 21, 517, 57, 73, 265, 81, 529, 321, 769, 14, 390, 518, 266, 770, 44, 140, 52, 532, 164, 644, 104, 200, 392, 112, 176, 336, 400, 656, 784, 224, 448, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_519, vertices_779, vertices_533, vertices_121, vertices_457, vertices_849, vertices_398, vertices_902, vertices_236, vertices_692, vertices_496, vertices_912] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_515, vertices_21, vertices_517, vertices_57, vertices_73, vertices_265, vertices_81, vertices_529, vertices_321, vertices_769, vertices_14, vertices_390, vertices_518, vertices_266, vertices_770, vertices_44, vertices_140, vertices_52, vertices_532, vertices_164, vertices_644, vertices_104, vertices_200, vertices_392, vertices_112, vertices_176, vertices_336, vertices_400, vertices_656, vertices_784, vertices_224, vertices_448, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_519), (false, vertices_779), (false, vertices_533), (false, vertices_121), (false, vertices_457), (false, vertices_849), (true, vertices_390), (true, vertices_140), (true, vertices_164), (true, vertices_644), (true, vertices_176), (true, vertices_400), (true, vertices_656), (true, vertices_224), (true, vertices_896)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 10 13 14 18 20 21 22 23 24
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 15 else
  if p.val = (false, vertices_519) then 0 else
  if p.val = (false, vertices_779) then 11 else
  if p.val = (false, vertices_533) then 1 else
  if p.val = (false, vertices_121) then 16 else
  if p.val = (false, vertices_457) then 17 else
  if p.val = (false, vertices_849) then 19 else
  if p.val = (true, vertices_390) then 12 else
  if p.val = (true, vertices_140) then 2 else
  if p.val = (true, vertices_164) then 3 else
  if p.val = (true, vertices_644) then 4 else
  if p.val = (true, vertices_176) then 5 else
  if p.val = (true, vertices_400) then 6 else
  if p.val = (true, vertices_656) then 7 else
  if p.val = (true, vertices_224) then 8 else
  if p.val = (true, vertices_896) then 9 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_519), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_533), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_140), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_164), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_644), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_176), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_400), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_656), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_224), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_896), by decide +kernel⟩
  | 10 => Sum.inl 0
  | 11 => Sum.inr ⟨(false, vertices_779), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_390), by decide +kernel⟩
  | 13 => Sum.inl 1
  | 14 => Sum.inl 2
  | 15 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 16 => Sum.inr ⟨(false, vertices_121), by decide +kernel⟩
  | 17 => Sum.inr ⟨(false, vertices_457), by decide +kernel⟩
  | 18 => Sum.inl 3
  | 19 => Sum.inr ⟨(false, vertices_849), by decide +kernel⟩
  | 20 => Sum.inl 4
  | 21 => Sum.inl 5
  | 22 => Sum.inl 6
  | 23 => Sum.inl 7
  | 24 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 1 6 7 390
cert_row_4 1 1 2 4 5 6 236 44 3
cert_row_4 2 1 3 4 6 8 692 52 3
cert_row_4 3 3 4 5 6 7 496 112 3
cert_rows
cert_pivot_2 0 2 1 3
cert_heightProof 4
cert_coverFacet 0 398
cert_cover_5 0 0 0 1 2 6 14 398 3
cert_coverFacet 1 902
cert_cover_5 1 0 0 1 6 8 390 902 3
cert_coverFacet 2 236
cert_cover_5 2 1 1 2 4 5 44 236 3
cert_coverFacet 3 692
cert_cover_5 3 2 1 3 4 6 52 692 3
cert_coverFacet 4 496
cert_cover_5 4 3 3 4 5 6 112 496 3
cert_coverFacet 5 912
cert_cover_2 5 6 3 7 8 400 912 3
cert_coveringFacets
cert_coveringProof_6
cert_certificate 4 6
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0963

end
end BundlePart19

section BundlePart20
/- Source: ProjectionCertificates/R_one_six_0965.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0965

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 775, 395, 341, 121, 457, 654, 898, 556, 820, 744, 496, 928, 7, 11, 259, 21, 261, 57, 73, 393, 81, 321, 14, 518, 138, 386, 642, 770, 44, 524, 52, 276, 548, 772, 104, 552, 200, 648, 112, 304, 336, 224, 416, 672, 800, 448, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_775, vertices_395, vertices_341, vertices_121, vertices_457, vertices_654, vertices_898, vertices_556, vertices_820, vertices_744, vertices_496, vertices_928] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_259, vertices_21, vertices_261, vertices_57, vertices_73, vertices_393, vertices_81, vertices_321, vertices_14, vertices_518, vertices_138, vertices_386, vertices_642, vertices_770, vertices_44, vertices_524, vertices_52, vertices_276, vertices_548, vertices_772, vertices_104, vertices_552, vertices_200, vertices_648, vertices_112, vertices_304, vertices_336, vertices_224, vertices_416, vertices_672, vertices_800, vertices_448, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_775), (false, vertices_395), (false, vertices_341), (false, vertices_121), (false, vertices_457), (true, vertices_642), (true, vertices_524), (true, vertices_548), (true, vertices_552), (true, vertices_648), (true, vertices_304), (true, vertices_224), (true, vertices_416), (true, vertices_672), (true, vertices_800), (true, vertices_896)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 11 13 18 15 21 22 23 24 25
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 16 else
  if p.val = (false, vertices_775) then 12 else
  if p.val = (false, vertices_395) then 19 else
  if p.val = (false, vertices_341) then 14 else
  if p.val = (false, vertices_121) then 17 else
  if p.val = (false, vertices_457) then 20 else
  if p.val = (true, vertices_642) then 0 else
  if p.val = (true, vertices_524) then 1 else
  if p.val = (true, vertices_548) then 2 else
  if p.val = (true, vertices_552) then 3 else
  if p.val = (true, vertices_648) then 4 else
  if p.val = (true, vertices_304) then 5 else
  if p.val = (true, vertices_224) then 6 else
  if p.val = (true, vertices_416) then 7 else
  if p.val = (true, vertices_672) then 8 else
  if p.val = (true, vertices_800) then 9 else
  if p.val = (true, vertices_896) then 10 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_642), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_524), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_548), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_552), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_648), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_304), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_224), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_416), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_672), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_800), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_896), by decide +kernel⟩
  | 11 => Sum.inl 0
  | 12 => Sum.inr ⟨(false, vertices_775), by decide +kernel⟩
  | 13 => Sum.inl 1
  | 14 => Sum.inr ⟨(false, vertices_341), by decide +kernel⟩
  | 15 => Sum.inl 3
  | 16 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 17 => Sum.inr ⟨(false, vertices_121), by decide +kernel⟩
  | 18 => Sum.inl 2
  | 19 => Sum.inr ⟨(false, vertices_395), by decide +kernel⟩
  | 20 => Sum.inr ⟨(false, vertices_457), by decide +kernel⟩
  | 21 => Sum.inl 4
  | 22 => Sum.inl 5
  | 23 => Sum.inl 6
  | 24 => Sum.inl 7
  | 25 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 2 6 8 654 14 3
cert_row_4 1 1 3 4 7 8 820 52 3
cert_row_4 2 2 4 5 6 8 744 104 3
cert_row_4 3 3 4 5 6 7 496 112 3
cert_rows
cert_pivot_2 0 1 2 3
cert_heightProof 4
cert_coverFacet 0 654
cert_cover_5 0 0 0 1 2 6 14 654 3
cert_coverFacet 1 898
cert_cover_2 1 6 0 7 8 386 898 3
cert_coverFacet 2 556
cert_cover_2 2 2 1 4 8 44 556 3
cert_coverFacet 3 820
cert_cover_5 3 1 1 3 4 7 52 820 3
cert_coverFacet 4 744
cert_cover_5 4 2 2 4 5 6 104 744 3
cert_coverFacet 5 496
cert_cover_5 5 3 3 4 5 6 112 496 3
cert_coverFacet 6 928
cert_cover_2 6 6 4 7 8 416 928 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0965

end
end BundlePart20

section BundlePart21
/- Source: ProjectionCertificates/R_one_six_0966.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0966

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 775, 395, 341, 121, 457, 654, 898, 556, 820, 744, 624, 976, 7, 11, 259, 21, 261, 57, 73, 393, 81, 321, 14, 518, 138, 386, 642, 770, 44, 524, 52, 276, 548, 772, 104, 552, 200, 648, 112, 560, 336, 592, 784, 608, 448, 704, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_775, vertices_395, vertices_341, vertices_121, vertices_457, vertices_654, vertices_898, vertices_556, vertices_820, vertices_744, vertices_624, vertices_976] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_259, vertices_21, vertices_261, vertices_57, vertices_73, vertices_393, vertices_81, vertices_321, vertices_14, vertices_518, vertices_138, vertices_386, vertices_642, vertices_770, vertices_44, vertices_524, vertices_52, vertices_276, vertices_548, vertices_772, vertices_104, vertices_552, vertices_200, vertices_648, vertices_112, vertices_560, vertices_336, vertices_592, vertices_784, vertices_608, vertices_448, vertices_704, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_775), (false, vertices_395), (false, vertices_341), (false, vertices_121), (false, vertices_457), (true, vertices_642), (true, vertices_524), (true, vertices_548), (true, vertices_552), (true, vertices_648), (true, vertices_560), (true, vertices_592), (true, vertices_784), (true, vertices_608), (true, vertices_704), (true, vertices_896)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 11 13 18 15 21 22 23 24 25
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 16 else
  if p.val = (false, vertices_775) then 12 else
  if p.val = (false, vertices_395) then 19 else
  if p.val = (false, vertices_341) then 14 else
  if p.val = (false, vertices_121) then 17 else
  if p.val = (false, vertices_457) then 20 else
  if p.val = (true, vertices_642) then 0 else
  if p.val = (true, vertices_524) then 1 else
  if p.val = (true, vertices_548) then 2 else
  if p.val = (true, vertices_552) then 3 else
  if p.val = (true, vertices_648) then 4 else
  if p.val = (true, vertices_560) then 5 else
  if p.val = (true, vertices_592) then 6 else
  if p.val = (true, vertices_784) then 7 else
  if p.val = (true, vertices_608) then 8 else
  if p.val = (true, vertices_704) then 9 else
  if p.val = (true, vertices_896) then 10 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_642), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_524), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_548), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_552), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_648), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_560), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_592), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_784), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_608), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_704), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_896), by decide +kernel⟩
  | 11 => Sum.inl 0
  | 12 => Sum.inr ⟨(false, vertices_775), by decide +kernel⟩
  | 13 => Sum.inl 1
  | 14 => Sum.inr ⟨(false, vertices_341), by decide +kernel⟩
  | 15 => Sum.inl 3
  | 16 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 17 => Sum.inr ⟨(false, vertices_121), by decide +kernel⟩
  | 18 => Sum.inl 2
  | 19 => Sum.inr ⟨(false, vertices_395), by decide +kernel⟩
  | 20 => Sum.inr ⟨(false, vertices_457), by decide +kernel⟩
  | 21 => Sum.inl 4
  | 22 => Sum.inl 5
  | 23 => Sum.inl 6
  | 24 => Sum.inl 7
  | 25 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 2 6 8 654 14 3
cert_row_4 1 1 3 4 7 8 820 52 3
cert_row_4 2 2 4 5 6 8 744 104 3
cert_row_4 3 3 5 6 7 8 976 336 2
cert_rows
cert_pivot_2 0 1 2 3
cert_heightProof 4
cert_coverFacet 0 654
cert_cover_5 0 0 0 1 2 6 14 654 3
cert_coverFacet 1 898
cert_cover_2 1 6 0 7 8 386 898 3
cert_coverFacet 2 556
cert_cover_2 2 2 1 4 8 44 556 3
cert_coverFacet 3 820
cert_cover_5 3 1 1 3 4 7 52 820 3
cert_coverFacet 4 744
cert_cover_5 4 2 2 4 5 6 104 744 3
cert_coverFacet 5 624
cert_cover_2 5 4 3 5 8 112 624 3
cert_coverFacet 6 976
cert_cover_5 6 3 3 5 6 7 336 976 2
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0966

end
end BundlePart21

section BundlePart22
/- Source: ProjectionCertificates/R_one_six_0967.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0967

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 775, 395, 341, 121, 457, 654, 962, 556, 820, 744, 624, 848, 7, 11, 259, 21, 261, 57, 73, 393, 81, 321, 14, 518, 138, 386, 642, 770, 44, 524, 52, 276, 548, 772, 104, 552, 200, 648, 112, 560, 336, 592, 784, 608, 448, 704, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_775, vertices_395, vertices_341, vertices_121, vertices_457, vertices_654, vertices_962, vertices_556, vertices_820, vertices_744, vertices_624, vertices_848] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_259, vertices_21, vertices_261, vertices_57, vertices_73, vertices_393, vertices_81, vertices_321, vertices_14, vertices_518, vertices_138, vertices_386, vertices_642, vertices_770, vertices_44, vertices_524, vertices_52, vertices_276, vertices_548, vertices_772, vertices_104, vertices_552, vertices_200, vertices_648, vertices_112, vertices_560, vertices_336, vertices_592, vertices_784, vertices_608, vertices_448, vertices_704, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_775), (false, vertices_395), (false, vertices_341), (false, vertices_121), (false, vertices_457), (true, vertices_642), (true, vertices_524), (true, vertices_548), (true, vertices_552), (true, vertices_648), (true, vertices_560), (true, vertices_592), (true, vertices_784), (true, vertices_608), (true, vertices_704), (true, vertices_832)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 11 13 18 15 21 22 23 24 25
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 16 else
  if p.val = (false, vertices_775) then 12 else
  if p.val = (false, vertices_395) then 19 else
  if p.val = (false, vertices_341) then 14 else
  if p.val = (false, vertices_121) then 17 else
  if p.val = (false, vertices_457) then 20 else
  if p.val = (true, vertices_642) then 0 else
  if p.val = (true, vertices_524) then 1 else
  if p.val = (true, vertices_548) then 2 else
  if p.val = (true, vertices_552) then 3 else
  if p.val = (true, vertices_648) then 4 else
  if p.val = (true, vertices_560) then 5 else
  if p.val = (true, vertices_592) then 6 else
  if p.val = (true, vertices_784) then 7 else
  if p.val = (true, vertices_608) then 8 else
  if p.val = (true, vertices_704) then 9 else
  if p.val = (true, vertices_832) then 10 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_642), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_524), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_548), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_552), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_648), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_560), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_592), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_784), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_608), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_704), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_832), by decide +kernel⟩
  | 11 => Sum.inl 0
  | 12 => Sum.inr ⟨(false, vertices_775), by decide +kernel⟩
  | 13 => Sum.inl 1
  | 14 => Sum.inr ⟨(false, vertices_341), by decide +kernel⟩
  | 15 => Sum.inl 3
  | 16 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 17 => Sum.inr ⟨(false, vertices_121), by decide +kernel⟩
  | 18 => Sum.inl 2
  | 19 => Sum.inr ⟨(false, vertices_395), by decide +kernel⟩
  | 20 => Sum.inr ⟨(false, vertices_457), by decide +kernel⟩
  | 21 => Sum.inl 4
  | 22 => Sum.inl 5
  | 23 => Sum.inl 6
  | 24 => Sum.inl 7
  | 25 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 1 3 4 7 8 820 52 3
cert_row_4 1 0 1 2 6 8 654 14 3
cert_row_4 2 0 5 6 7 8 962 386 1
cert_row_4 3 2 4 5 6 8 744 104 3
cert_rows
cert_pivot_2 3 1 0 2
cert_heightProof 4
cert_coverFacet 0 654
cert_cover_5 0 1 0 1 2 6 14 654 3
cert_coverFacet 1 962
cert_cover_5 1 2 0 5 6 7 386 962 1
cert_coverFacet 2 556
cert_cover_2 2 2 1 4 8 44 556 3
cert_coverFacet 3 820
cert_cover_5 3 0 1 3 4 7 52 820 3
cert_coverFacet 4 744
cert_cover_5 4 3 2 4 5 6 104 744 3
cert_coverFacet 5 624
cert_cover_2 5 4 3 5 8 112 624 3
cert_coverFacet 6 848
cert_cover_2 6 5 3 7 8 336 848 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0967

end
end BundlePart22

section BundlePart23
/- Source: ProjectionCertificates/R_one_six_0968.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0968

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 775, 395, 341, 121, 457, 654, 962, 556, 820, 744, 368, 864, 7, 11, 259, 21, 261, 57, 73, 393, 81, 321, 14, 518, 138, 386, 642, 770, 44, 524, 52, 276, 548, 772, 104, 552, 200, 648, 112, 304, 336, 352, 608, 800, 448, 704, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_775, vertices_395, vertices_341, vertices_121, vertices_457, vertices_654, vertices_962, vertices_556, vertices_820, vertices_744, vertices_368, vertices_864] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_259, vertices_21, vertices_261, vertices_57, vertices_73, vertices_393, vertices_81, vertices_321, vertices_14, vertices_518, vertices_138, vertices_386, vertices_642, vertices_770, vertices_44, vertices_524, vertices_52, vertices_276, vertices_548, vertices_772, vertices_104, vertices_552, vertices_200, vertices_648, vertices_112, vertices_304, vertices_336, vertices_352, vertices_608, vertices_800, vertices_448, vertices_704, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_775), (false, vertices_395), (false, vertices_341), (false, vertices_121), (false, vertices_457), (true, vertices_642), (true, vertices_524), (true, vertices_548), (true, vertices_552), (true, vertices_648), (true, vertices_304), (true, vertices_352), (true, vertices_608), (true, vertices_800), (true, vertices_704), (true, vertices_832)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 11 13 18 15 21 22 23 24 25
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 16 else
  if p.val = (false, vertices_775) then 12 else
  if p.val = (false, vertices_395) then 19 else
  if p.val = (false, vertices_341) then 14 else
  if p.val = (false, vertices_121) then 17 else
  if p.val = (false, vertices_457) then 20 else
  if p.val = (true, vertices_642) then 0 else
  if p.val = (true, vertices_524) then 1 else
  if p.val = (true, vertices_548) then 2 else
  if p.val = (true, vertices_552) then 3 else
  if p.val = (true, vertices_648) then 4 else
  if p.val = (true, vertices_304) then 5 else
  if p.val = (true, vertices_352) then 6 else
  if p.val = (true, vertices_608) then 7 else
  if p.val = (true, vertices_800) then 8 else
  if p.val = (true, vertices_704) then 9 else
  if p.val = (true, vertices_832) then 10 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_642), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_524), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_548), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_552), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_648), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_304), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_352), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_608), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_800), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_704), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_832), by decide +kernel⟩
  | 11 => Sum.inl 0
  | 12 => Sum.inr ⟨(false, vertices_775), by decide +kernel⟩
  | 13 => Sum.inl 1
  | 14 => Sum.inr ⟨(false, vertices_341), by decide +kernel⟩
  | 15 => Sum.inl 3
  | 16 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 17 => Sum.inr ⟨(false, vertices_121), by decide +kernel⟩
  | 18 => Sum.inl 2
  | 19 => Sum.inr ⟨(false, vertices_395), by decide +kernel⟩
  | 20 => Sum.inr ⟨(false, vertices_457), by decide +kernel⟩
  | 21 => Sum.inl 4
  | 22 => Sum.inl 5
  | 23 => Sum.inl 6
  | 24 => Sum.inl 7
  | 25 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 1 3 4 7 8 820 52 3
cert_row_4 1 0 1 2 6 8 654 14 3
cert_row_4 2 0 5 6 7 8 962 386 1
cert_row_4 3 2 4 5 6 8 744 104 3
cert_rows
cert_pivot_2 3 1 0 2
cert_heightProof 4
cert_coverFacet 0 654
cert_cover_5 0 1 0 1 2 6 14 654 3
cert_coverFacet 1 962
cert_cover_5 1 2 0 5 6 7 386 962 1
cert_coverFacet 2 556
cert_cover_2 2 2 1 4 8 44 556 3
cert_coverFacet 3 820
cert_cover_5 3 0 1 3 4 7 52 820 3
cert_coverFacet 4 744
cert_cover_5 4 3 2 4 5 6 104 744 3
cert_coverFacet 5 368
cert_cover_2 5 4 3 5 7 112 368 3
cert_coverFacet 6 864
cert_cover_2 6 5 4 7 8 352 864 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0968

end
end BundlePart23

section BundlePart24
/- Source: ProjectionCertificates/R_one_six_0969.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0969

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 775, 395, 341, 121, 457, 654, 962, 556, 308, 804, 744, 880, 7, 11, 259, 21, 261, 57, 73, 393, 81, 321, 14, 518, 138, 386, 642, 770, 44, 524, 52, 276, 292, 548, 772, 104, 552, 200, 648, 112, 304, 336, 608, 800, 448, 704, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_775, vertices_395, vertices_341, vertices_121, vertices_457, vertices_654, vertices_962, vertices_556, vertices_308, vertices_804, vertices_744, vertices_880] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_259, vertices_21, vertices_261, vertices_57, vertices_73, vertices_393, vertices_81, vertices_321, vertices_14, vertices_518, vertices_138, vertices_386, vertices_642, vertices_770, vertices_44, vertices_524, vertices_52, vertices_276, vertices_292, vertices_548, vertices_772, vertices_104, vertices_552, vertices_200, vertices_648, vertices_112, vertices_304, vertices_336, vertices_608, vertices_800, vertices_448, vertices_704, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_775), (false, vertices_395), (false, vertices_341), (false, vertices_121), (false, vertices_457), (true, vertices_642), (true, vertices_524), (true, vertices_292), (true, vertices_548), (true, vertices_552), (true, vertices_648), (true, vertices_304), (true, vertices_608), (true, vertices_800), (true, vertices_704), (true, vertices_832)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 11 13 18 15 21 22 23 24 25
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 16 else
  if p.val = (false, vertices_775) then 12 else
  if p.val = (false, vertices_395) then 19 else
  if p.val = (false, vertices_341) then 14 else
  if p.val = (false, vertices_121) then 17 else
  if p.val = (false, vertices_457) then 20 else
  if p.val = (true, vertices_642) then 0 else
  if p.val = (true, vertices_524) then 1 else
  if p.val = (true, vertices_292) then 2 else
  if p.val = (true, vertices_548) then 3 else
  if p.val = (true, vertices_552) then 4 else
  if p.val = (true, vertices_648) then 5 else
  if p.val = (true, vertices_304) then 6 else
  if p.val = (true, vertices_608) then 7 else
  if p.val = (true, vertices_800) then 8 else
  if p.val = (true, vertices_704) then 9 else
  if p.val = (true, vertices_832) then 10 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_642), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_524), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_292), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_548), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_552), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_648), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_304), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_608), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_800), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_704), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_832), by decide +kernel⟩
  | 11 => Sum.inl 0
  | 12 => Sum.inr ⟨(false, vertices_775), by decide +kernel⟩
  | 13 => Sum.inl 1
  | 14 => Sum.inr ⟨(false, vertices_341), by decide +kernel⟩
  | 15 => Sum.inl 3
  | 16 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 17 => Sum.inr ⟨(false, vertices_121), by decide +kernel⟩
  | 18 => Sum.inl 2
  | 19 => Sum.inr ⟨(false, vertices_395), by decide +kernel⟩
  | 20 => Sum.inr ⟨(false, vertices_457), by decide +kernel⟩
  | 21 => Sum.inl 4
  | 22 => Sum.inl 5
  | 23 => Sum.inl 6
  | 24 => Sum.inl 7
  | 25 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 2 6 8 654 14 3
cert_row_4 1 0 5 6 7 8 962 386 1
cert_row_4 2 2 4 5 6 8 744 104 3
cert_row_4 3 3 4 5 7 8 880 112 3
cert_rows
cert_pivot_2 1 0 2 3
cert_heightProof 4
cert_coverFacet 0 654
cert_cover_5 0 0 0 1 2 6 14 654 3
cert_coverFacet 1 962
cert_cover_5 1 1 0 5 6 7 386 962 1
cert_coverFacet 2 556
cert_cover_2 2 2 1 4 8 44 556 3
cert_coverFacet 3 308
cert_cover_2 3 3 1 4 7 52 308 3
cert_coverFacet 4 804
cert_cover_2 4 4 1 7 8 292 804 3
cert_coverFacet 5 744
cert_cover_5 5 2 2 4 5 6 104 744 3
cert_coverFacet 6 880
cert_cover_5 6 3 3 4 5 7 112 880 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0969

end
end BundlePart24

section BundlePart25
/- Source: ProjectionCertificates/R_one_six_0970.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0970

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 775, 395, 341, 121, 457, 654, 962, 556, 564, 788, 744, 880, 7, 11, 259, 21, 261, 57, 73, 393, 81, 321, 14, 518, 138, 386, 642, 770, 44, 524, 52, 276, 532, 548, 772, 104, 552, 200, 648, 112, 560, 336, 784, 608, 448, 704, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_775, vertices_395, vertices_341, vertices_121, vertices_457, vertices_654, vertices_962, vertices_556, vertices_564, vertices_788, vertices_744, vertices_880] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_259, vertices_21, vertices_261, vertices_57, vertices_73, vertices_393, vertices_81, vertices_321, vertices_14, vertices_518, vertices_138, vertices_386, vertices_642, vertices_770, vertices_44, vertices_524, vertices_52, vertices_276, vertices_532, vertices_548, vertices_772, vertices_104, vertices_552, vertices_200, vertices_648, vertices_112, vertices_560, vertices_336, vertices_784, vertices_608, vertices_448, vertices_704, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_775), (false, vertices_395), (false, vertices_341), (false, vertices_121), (false, vertices_457), (true, vertices_642), (true, vertices_524), (true, vertices_532), (true, vertices_548), (true, vertices_552), (true, vertices_648), (true, vertices_560), (true, vertices_784), (true, vertices_608), (true, vertices_704), (true, vertices_832)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 11 13 18 15 21 22 23 24 25
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 16 else
  if p.val = (false, vertices_775) then 12 else
  if p.val = (false, vertices_395) then 19 else
  if p.val = (false, vertices_341) then 14 else
  if p.val = (false, vertices_121) then 17 else
  if p.val = (false, vertices_457) then 20 else
  if p.val = (true, vertices_642) then 0 else
  if p.val = (true, vertices_524) then 1 else
  if p.val = (true, vertices_532) then 2 else
  if p.val = (true, vertices_548) then 3 else
  if p.val = (true, vertices_552) then 4 else
  if p.val = (true, vertices_648) then 5 else
  if p.val = (true, vertices_560) then 6 else
  if p.val = (true, vertices_784) then 7 else
  if p.val = (true, vertices_608) then 8 else
  if p.val = (true, vertices_704) then 9 else
  if p.val = (true, vertices_832) then 10 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_642), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_524), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_532), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_548), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_552), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_648), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_560), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_784), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_608), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_704), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_832), by decide +kernel⟩
  | 11 => Sum.inl 0
  | 12 => Sum.inr ⟨(false, vertices_775), by decide +kernel⟩
  | 13 => Sum.inl 1
  | 14 => Sum.inr ⟨(false, vertices_341), by decide +kernel⟩
  | 15 => Sum.inl 3
  | 16 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 17 => Sum.inr ⟨(false, vertices_121), by decide +kernel⟩
  | 18 => Sum.inl 2
  | 19 => Sum.inr ⟨(false, vertices_395), by decide +kernel⟩
  | 20 => Sum.inr ⟨(false, vertices_457), by decide +kernel⟩
  | 21 => Sum.inl 4
  | 22 => Sum.inl 5
  | 23 => Sum.inl 6
  | 24 => Sum.inl 7
  | 25 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 2 6 8 654 14 3
cert_row_4 1 0 5 6 7 8 962 386 1
cert_row_4 2 2 4 5 6 8 744 104 3
cert_row_4 3 3 4 5 7 8 880 112 3
cert_rows
cert_pivot_2 1 0 2 3
cert_heightProof 4
cert_coverFacet 0 654
cert_cover_5 0 0 0 1 2 6 14 654 3
cert_coverFacet 1 962
cert_cover_5 1 1 0 5 6 7 386 962 1
cert_coverFacet 2 556
cert_cover_2 2 2 1 4 8 44 556 3
cert_coverFacet 3 564
cert_cover_2 3 3 1 4 8 52 564 3
cert_coverFacet 4 788
cert_cover_2 4 3 1 7 8 276 788 3
cert_coverFacet 5 744
cert_cover_5 5 2 2 4 5 6 104 744 3
cert_coverFacet 6 880
cert_cover_5 6 3 3 4 5 7 112 880 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0970

end
end BundlePart25

section BundlePart26
/- Source: ProjectionCertificates/R_one_six_0971.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0971

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 391, 779, 117, 197, 809, 481, 654, 962, 220, 568, 728, 880, 7, 11, 259, 53, 69, 133, 41, 777, 97, 289, 193, 385, 14, 134, 522, 386, 642, 770, 28, 140, 84, 196, 56, 216, 536, 552, 648, 112, 560, 592, 352, 800, 448, 704, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_391, vertices_779, vertices_117, vertices_197, vertices_809, vertices_481, vertices_654, vertices_962, vertices_220, vertices_568, vertices_728, vertices_880] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_259, vertices_53, vertices_69, vertices_133, vertices_41, vertices_777, vertices_97, vertices_289, vertices_193, vertices_385, vertices_14, vertices_134, vertices_522, vertices_386, vertices_642, vertices_770, vertices_28, vertices_140, vertices_84, vertices_196, vertices_56, vertices_216, vertices_536, vertices_552, vertices_648, vertices_112, vertices_560, vertices_592, vertices_352, vertices_800, vertices_448, vertices_704, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_391), (false, vertices_779), (false, vertices_117), (false, vertices_197), (false, vertices_809), (false, vertices_481), (true, vertices_642), (true, vertices_140), (true, vertices_216), (true, vertices_536), (true, vertices_648), (true, vertices_560), (true, vertices_592), (true, vertices_704), (true, vertices_832)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 9 11 16 14 19 21 22 23 24
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 12 else
  if p.val = (false, vertices_391) then 10 else
  if p.val = (false, vertices_779) then 17 else
  if p.val = (false, vertices_117) then 13 else
  if p.val = (false, vertices_197) then 0 else
  if p.val = (false, vertices_809) then 18 else
  if p.val = (false, vertices_481) then 20 else
  if p.val = (true, vertices_642) then 1 else
  if p.val = (true, vertices_140) then 2 else
  if p.val = (true, vertices_216) then 15 else
  if p.val = (true, vertices_536) then 3 else
  if p.val = (true, vertices_648) then 4 else
  if p.val = (true, vertices_560) then 5 else
  if p.val = (true, vertices_592) then 6 else
  if p.val = (true, vertices_704) then 7 else
  if p.val = (true, vertices_832) then 8 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_197), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_642), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_140), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_536), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_648), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_560), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_592), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_704), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_832), by decide +kernel⟩
  | 9 => Sum.inl 0
  | 10 => Sum.inr ⟨(false, vertices_391), by decide +kernel⟩
  | 11 => Sum.inl 1
  | 12 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 13 => Sum.inr ⟨(false, vertices_117), by decide +kernel⟩
  | 14 => Sum.inl 3
  | 15 => Sum.inr ⟨(true, vertices_216), by decide +kernel⟩
  | 16 => Sum.inl 2
  | 17 => Sum.inr ⟨(false, vertices_779), by decide +kernel⟩
  | 18 => Sum.inr ⟨(false, vertices_809), by decide +kernel⟩
  | 19 => Sum.inl 4
  | 20 => Sum.inr ⟨(false, vertices_481), by decide +kernel⟩
  | 21 => Sum.inl 5
  | 22 => Sum.inl 6
  | 23 => Sum.inl 7
  | 24 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 2 6 8 654 14 3
cert_row_2 1 2 3 5 6 216
cert_row_4 2 0 5 6 7 8 962 386 1
cert_row_4 3 3 4 5 7 8 880 112 3
cert_rows
cert_pivot_2 1 2 0 3
cert_heightProof 4
cert_coverFacet 0 654
cert_cover_5 0 0 0 1 2 6 14 654 3
cert_coverFacet 1 962
cert_cover_5 1 2 0 5 6 7 386 962 1
cert_coverFacet 2 220
cert_cover_5 2 1 1 2 3 5 28 220 3
cert_coverFacet 3 568
cert_cover_2 3 3 2 4 8 56 568 3
cert_coverFacet 4 728
cert_cover_5 4 1 2 3 5 8 216 728 3
cert_coverFacet 5 880
cert_cover_5 5 3 3 4 5 7 112 880 3
cert_coveringFacets
cert_coveringProof_6
cert_certificate 4 6
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0971

end
end BundlePart26

section BundlePart27
/- Source: ProjectionCertificates/R_one_six_0972.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0972

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 647, 395, 781, 961, 214, 122, 202, 300, 820, 724, 488, 880, 7, 11, 131, 13, 517, 265, 385, 641, 769, 22, 134, 58, 74, 138, 82, 194, 44, 268, 52, 212, 532, 292, 644, 772, 104, 296, 200, 392, 112, 816, 592, 352, 448, 704, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_647, vertices_395, vertices_781, vertices_961, vertices_214, vertices_122, vertices_202, vertices_300, vertices_820, vertices_724, vertices_488, vertices_880] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_131, vertices_13, vertices_517, vertices_265, vertices_385, vertices_641, vertices_769, vertices_22, vertices_134, vertices_58, vertices_74, vertices_138, vertices_82, vertices_194, vertices_44, vertices_268, vertices_52, vertices_212, vertices_532, vertices_292, vertices_644, vertices_772, vertices_104, vertices_296, vertices_200, vertices_392, vertices_112, vertices_816, vertices_592, vertices_352, vertices_448, vertices_704, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_647), (false, vertices_395), (false, vertices_781), (false, vertices_961), (true, vertices_74), (true, vertices_82), (true, vertices_194), (true, vertices_212), (true, vertices_532), (true, vertices_292), (true, vertices_104), (true, vertices_296), (true, vertices_200), (true, vertices_112), (true, vertices_816), (true, vertices_592), (true, vertices_352)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 11 14 18 19 21 22 24 25 26
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 15 else
  if p.val = (false, vertices_647) then 12 else
  if p.val = (false, vertices_395) then 13 else
  if p.val = (false, vertices_781) then 16 else
  if p.val = (false, vertices_961) then 23 else
  if p.val = (true, vertices_74) then 0 else
  if p.val = (true, vertices_82) then 1 else
  if p.val = (true, vertices_194) then 2 else
  if p.val = (true, vertices_212) then 17 else
  if p.val = (true, vertices_532) then 3 else
  if p.val = (true, vertices_292) then 4 else
  if p.val = (true, vertices_104) then 5 else
  if p.val = (true, vertices_296) then 6 else
  if p.val = (true, vertices_200) then 7 else
  if p.val = (true, vertices_112) then 8 else
  if p.val = (true, vertices_816) then 20 else
  if p.val = (true, vertices_592) then 9 else
  if p.val = (true, vertices_352) then 10 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_74), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_82), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_194), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_532), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_292), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_104), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_296), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_200), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_112), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_592), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_352), by decide +kernel⟩
  | 11 => Sum.inl 0
  | 12 => Sum.inr ⟨(false, vertices_647), by decide +kernel⟩
  | 13 => Sum.inr ⟨(false, vertices_395), by decide +kernel⟩
  | 14 => Sum.inl 1
  | 15 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 16 => Sum.inr ⟨(false, vertices_781), by decide +kernel⟩
  | 17 => Sum.inr ⟨(true, vertices_212), by decide +kernel⟩
  | 18 => Sum.inl 2
  | 19 => Sum.inl 3
  | 20 => Sum.inr ⟨(true, vertices_816), by decide +kernel⟩
  | 21 => Sum.inl 4
  | 22 => Sum.inl 5
  | 23 => Sum.inr ⟨(false, vertices_961), by decide +kernel⟩
  | 24 => Sum.inl 6
  | 25 => Sum.inl 7
  | 26 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 3 4 7 8 816
cert_row_2 1 0 2 3 4 58
cert_row_2 2 1 3 5 6 212
cert_row_4 3 2 4 5 6 7 488 104 3
cert_rows
cert_pivot_2 8 0 1 2
cert_heightProof 4
cert_coverFacet 0 214
cert_cover_5 0 2 0 1 3 5 22 214 3
cert_coverFacet 1 122
cert_cover_5 1 1 0 2 3 5 58 122 3
cert_coverFacet 2 202
cert_cover_2 2 2 0 5 6 74 202 3
cert_coverFacet 3 300
cert_cover_2 3 2 1 4 7 44 300 3
cert_coverFacet 4 820
cert_cover_5 4 0 1 3 4 7 52 820 3
cert_coverFacet 5 724
cert_cover_5 5 2 1 3 5 8 212 724 3
cert_coverFacet 6 488
cert_cover_5 6 3 2 4 5 6 104 488 3
cert_coverFacet 7 880
cert_cover_5 7 0 3 4 5 7 112 880 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0972

end
end BundlePart27

section BundlePart28
/- Source: ProjectionCertificates/R_one_six_0974.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0974

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 519, 779, 661, 361, 817, 206, 902, 458, 124, 212, 752, 992, 7, 11, 515, 21, 517, 41, 265, 49, 529, 289, 769, 14, 134, 518, 202, 266, 386, 770, 60, 76, 84, 148, 196, 644, 104, 328, 112, 560, 208, 656, 736, 352, 800, 448, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_519, vertices_779, vertices_661, vertices_361, vertices_817, vertices_206, vertices_902, vertices_458, vertices_124, vertices_212, vertices_752, vertices_992] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_515, vertices_21, vertices_517, vertices_41, vertices_265, vertices_49, vertices_529, vertices_289, vertices_769, vertices_14, vertices_134, vertices_518, vertices_202, vertices_266, vertices_386, vertices_770, vertices_60, vertices_76, vertices_84, vertices_148, vertices_196, vertices_644, vertices_104, vertices_328, vertices_112, vertices_560, vertices_208, vertices_656, vertices_736, vertices_352, vertices_800, vertices_448, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_519), (false, vertices_779), (false, vertices_661), (false, vertices_361), (false, vertices_817), (true, vertices_134), (true, vertices_202), (true, vertices_386), (true, vertices_76), (true, vertices_84), (true, vertices_196), (true, vertices_112), (true, vertices_208), (true, vertices_736), (true, vertices_448), (true, vertices_896)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 10 18 12 20 22 23 24 25
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 13 else
  if p.val = (false, vertices_519) then 0 else
  if p.val = (false, vertices_779) then 16 else
  if p.val = (false, vertices_661) then 11 else
  if p.val = (false, vertices_361) then 19 else
  if p.val = (false, vertices_817) then 14 else
  if p.val = (true, vertices_134) then 1 else
  if p.val = (true, vertices_202) then 17 else
  if p.val = (true, vertices_386) then 2 else
  if p.val = (true, vertices_76) then 3 else
  if p.val = (true, vertices_84) then 4 else
  if p.val = (true, vertices_196) then 5 else
  if p.val = (true, vertices_112) then 6 else
  if p.val = (true, vertices_208) then 7 else
  if p.val = (true, vertices_736) then 21 else
  if p.val = (true, vertices_448) then 8 else
  if p.val = (true, vertices_896) then 9 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_519), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_134), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_386), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_76), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_84), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_196), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_112), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_208), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_448), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_896), by decide +kernel⟩
  | 10 => Sum.inl 1
  | 11 => Sum.inr ⟨(false, vertices_661), by decide +kernel⟩
  | 12 => Sum.inl 3
  | 13 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 14 => Sum.inr ⟨(false, vertices_817), by decide +kernel⟩
  | 15 => Sum.inl 0
  | 16 => Sum.inr ⟨(false, vertices_779), by decide +kernel⟩
  | 17 => Sum.inr ⟨(true, vertices_202), by decide +kernel⟩
  | 18 => Sum.inl 2
  | 19 => Sum.inr ⟨(false, vertices_361), by decide +kernel⟩
  | 20 => Sum.inl 4
  | 21 => Sum.inr ⟨(true, vertices_736), by decide +kernel⟩
  | 22 => Sum.inl 5
  | 23 => Sum.inl 6
  | 24 => Sum.inl 7
  | 25 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 1 2 3 4 60
cert_row_2 1 0 2 5 6 202
cert_row_2 2 4 5 6 8 736
cert_row_4 3 0 1 6 7 8 902 134 3
cert_rows
cert_pivot_2 3 2 4 0
cert_heightProof 4
cert_coverFacet 0 206
cert_cover_5 0 1 0 1 2 5 14 206 3
cert_coverFacet 1 902
cert_cover_5 1 3 0 1 6 7 134 902 3
cert_coverFacet 2 458
cert_cover_5 2 1 0 2 5 7 202 458 3
cert_coverFacet 3 124
cert_cover_5 3 0 1 2 3 5 60 124 3
cert_coverFacet 4 212
cert_cover_2 4 3 1 5 6 84 212 3
cert_coverFacet 5 752
cert_cover_5 5 2 3 4 5 6 112 752 3
cert_coverFacet 6 992
cert_cover_5 6 2 4 5 6 7 736 992 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0974

end
end BundlePart28

section BundlePart29
/- Source: ProjectionCertificates/R_one_six_0975.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0975

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 199, 779, 451, 117, 361, 526, 902, 540, 724, 696, 936, 496, 7, 11, 195, 259, 53, 69, 41, 265, 97, 321, 14, 134, 518, 522, 386, 770, 28, 524, 84, 532, 196, 644, 56, 536, 680, 296, 776, 112, 176, 208, 656, 352, 416, 448, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_199, vertices_779, vertices_451, vertices_117, vertices_361, vertices_526, vertices_902, vertices_540, vertices_724, vertices_696, vertices_936, vertices_496] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_195, vertices_259, vertices_53, vertices_69, vertices_41, vertices_265, vertices_97, vertices_321, vertices_14, vertices_134, vertices_518, vertices_522, vertices_386, vertices_770, vertices_28, vertices_524, vertices_84, vertices_532, vertices_196, vertices_644, vertices_56, vertices_536, vertices_680, vertices_296, vertices_776, vertices_112, vertices_176, vertices_208, vertices_656, vertices_352, vertices_416, vertices_448, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_199), (false, vertices_779), (false, vertices_451), (false, vertices_117), (false, vertices_361), (true, vertices_518), (true, vertices_524), (true, vertices_532), (true, vertices_644), (true, vertices_536), (true, vertices_680), (true, vertices_176), (true, vertices_208), (true, vertices_656), (true, vertices_416), (true, vertices_896)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 14 10 18 12 21 22 23 24 25
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 13 else
  if p.val = (false, vertices_199) then 15 else
  if p.val = (false, vertices_779) then 16 else
  if p.val = (false, vertices_451) then 17 else
  if p.val = (false, vertices_117) then 11 else
  if p.val = (false, vertices_361) then 19 else
  if p.val = (true, vertices_518) then 0 else
  if p.val = (true, vertices_524) then 1 else
  if p.val = (true, vertices_532) then 2 else
  if p.val = (true, vertices_644) then 3 else
  if p.val = (true, vertices_536) then 4 else
  if p.val = (true, vertices_680) then 20 else
  if p.val = (true, vertices_176) then 5 else
  if p.val = (true, vertices_208) then 6 else
  if p.val = (true, vertices_656) then 7 else
  if p.val = (true, vertices_416) then 8 else
  if p.val = (true, vertices_896) then 9 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_518), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_524), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_532), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_644), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_536), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_176), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_208), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_656), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_416), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_896), by decide +kernel⟩
  | 10 => Sum.inl 1
  | 11 => Sum.inr ⟨(false, vertices_117), by decide +kernel⟩
  | 12 => Sum.inl 3
  | 13 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 14 => Sum.inl 0
  | 15 => Sum.inr ⟨(false, vertices_199), by decide +kernel⟩
  | 16 => Sum.inr ⟨(false, vertices_779), by decide +kernel⟩
  | 17 => Sum.inr ⟨(false, vertices_451), by decide +kernel⟩
  | 18 => Sum.inl 2
  | 19 => Sum.inr ⟨(false, vertices_361), by decide +kernel⟩
  | 20 => Sum.inr ⟨(true, vertices_680), by decide +kernel⟩
  | 21 => Sum.inl 4
  | 22 => Sum.inl 5
  | 23 => Sum.inl 6
  | 24 => Sum.inl 7
  | 25 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 2 4 6 8 680
cert_row_4 1 0 1 6 7 8 902 134 3
cert_row_4 2 1 3 5 6 8 724 84 3
cert_row_4 3 3 4 5 6 7 496 112 3
cert_rows
cert_pivot_2 2 0 1 3
cert_heightProof 4
cert_coverFacet 0 526
cert_cover_2 0 1 0 2 8 14 526 3
cert_coverFacet 1 902
cert_cover_5 1 1 0 1 6 7 134 902 3
cert_coverFacet 2 540
cert_cover_2 2 2 1 3 8 28 540 3
cert_coverFacet 3 724
cert_cover_5 3 2 1 3 5 6 84 724 3
cert_coverFacet 4 696
cert_cover_5 4 0 2 3 4 6 56 696 3
cert_coverFacet 5 936
cert_cover_5 5 0 2 4 6 7 680 936 3
cert_coverFacet 6 496
cert_cover_5 6 3 3 4 5 6 112 496 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0975

end
end BundlePart29

-- Public target certificates; internal witness data stays private.
namespace Nonrational.TerminalVerification
open Papers.RationalityTen.ChirotopeDensity.FiniteProjection
open Nonrational.TerminalData
set_option maxRecDepth 100000
set_option maxHeartbeats 0

public theorem projection_1260 : Certifies 1260 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0939.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1261 : Certifies 1261 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0940.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1262 : Certifies 1262 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0941.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1263 : Certifies 1263 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0942.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1264 : Certifies 1264 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0943.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1265 : Certifies 1265 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0944.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1266 : Certifies 1266 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0945.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1267 : Certifies 1267 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0946.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1268 : Certifies 1268 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0947.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1269 : Certifies 1269 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0948.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1270 : Certifies 1270 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0949.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1271 : Certifies 1271 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0952.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1272 : Certifies 1272 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0953.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1273 : Certifies 1273 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0954.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1274 : Certifies 1274 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0955.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1275 : Certifies 1275 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0956.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1276 : Certifies 1276 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0957.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1277 : Certifies 1277 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0961.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1278 : Certifies 1278 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0962.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1279 : Certifies 1279 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0963.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1280 : Certifies 1280 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0965.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1281 : Certifies 1281 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0966.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1282 : Certifies 1282 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0967.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1283 : Certifies 1283 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0968.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1284 : Certifies 1284 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0969.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1285 : Certifies 1285 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0970.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1286 : Certifies 1286 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0971.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1287 : Certifies 1287 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0972.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1288 : Certifies 1288 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0974.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1289 : Certifies 1289 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0975.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem certified_B042 (j : Fin 30) :
    Certifies (1260 + j.val) := by
  fin_cases j
  · exact projection_1260
  · exact projection_1261
  · exact projection_1262
  · exact projection_1263
  · exact projection_1264
  · exact projection_1265
  · exact projection_1266
  · exact projection_1267
  · exact projection_1268
  · exact projection_1269
  · exact projection_1270
  · exact projection_1271
  · exact projection_1272
  · exact projection_1273
  · exact projection_1274
  · exact projection_1275
  · exact projection_1276
  · exact projection_1277
  · exact projection_1278
  · exact projection_1279
  · exact projection_1280
  · exact projection_1281
  · exact projection_1282
  · exact projection_1283
  · exact projection_1284
  · exact projection_1285
  · exact projection_1286
  · exact projection_1287
  · exact projection_1288
  · exact projection_1289

end Nonrational.TerminalVerification
-- Explicit facial frame witnesses, with lexical vector tracking.
