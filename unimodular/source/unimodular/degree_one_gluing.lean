module

public import Unimodular.StarNeighborhoods

@[expose] public section

open scoped Pointwise Topology BigOperators
open Filter Set

namespace Unimodular.CycleDegree.FullCones

attribute [local instance] Classical.propDecidable

variable {I V : Type*} [Fintype I] [NormedAddCommGroup V] [NormedSpace ℝ V]
  [FiniteDimensional ℝ V] (S : FullCones I V)

theorem weightedDegree_eq_two (c : I → ℤ) (hc : S.IsCycle c)
    {w : V} (hw : S.Generic w) (hdegree : S.multiplicity c w = 1)
    {x : V} (hx : S.Regular x) : S.weightedDegree c x = 2 := by
  rw [S.weightedDegree_eq c hc hx (S.generic_regular hw),
    S.weightedDegree_eq_two_mul hw c, hdegree]
  norm_num

/-- Integrality and nonnegativity force every coefficient of a degree-one cycle to be
an actual indicator. No coefficient bound is assumed. -/
theorem coeff_zero_or_one (c : I → ℤ) (hc0 : ∀ i, 0 ≤ c i) (hc : S.IsCycle c)
    {w : V} (hw : S.Generic w) (hdegree : S.multiplicity c w = 1) (i : I) :
    c i = 0 ∨ c i = 1 := by
  obtain ⟨x, hxint, hxgen⟩ := S.generic_dense.inter_open_nonempty
    (interior (S.cone i : Set V)) isOpen_interior ⟨S.center i, S.center_mem_interior i⟩
  have ht := S.term_le_weightedDegree c hc0 i x
  rw [FacetLine.weight_of_interior hxint,
    S.weightedDegree_eq_two c hc hw hdegree (S.generic_regular hxgen)] at ht
  have hn := hc0 i
  omega

theorem positive_coeff_eq_one (c : I → ℤ) (hc0 : ∀ i, 0 ≤ c i) (hc : S.IsCycle c)
    {w : V} (hw : S.Generic w) (hdegree : S.multiplicity c w = 1)
    {i : I} (hi : 0 < c i) : c i = 1 := by
  rcases S.coeff_zero_or_one c hc0 hc hw hdegree i with h | h
  · omega
  · exact h

theorem pair_le_weightedDegree (c : I → ℤ) (hc0 : ∀ i, 0 ≤ c i)
    {i j : I} (hij : i ≠ j) (x : V) :
    c i * FacetLine.weight (S.cone i) x + c j * FacetLine.weight (S.cone j) x ≤
      S.weightedDegree c x := by
  classical
  rw [← Finset.sum_pair (f := fun k => c k * FacetLine.weight (S.cone k) x) hij]
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
    (fun k _ _ => mul_nonneg (hc0 k) (S.weight_nonneg k x))

theorem selected_index_unique_at_generic (c : I → ℤ) (hc0 : ∀ i, 0 ≤ c i)
    (hc : S.IsCycle c) {w : V} (hw : S.Generic w) (hdegree : S.multiplicity c w = 1)
    {x : V} (hx : S.Generic x) {i j : I} (hi : 0 < c i) (hj : 0 < c j)
    (hxi : x ∈ S.cone i) (hxj : x ∈ S.cone j) : i = j := by
  by_contra hij
  have ht := S.pair_le_weightedDegree c hc0 hij x
  rw [FacetLine.weight_of_interior (S.generic_interior hx i hxi),
    FacetLine.weight_of_interior (S.generic_interior hx j hxj),
    S.weightedDegree_eq_two c hc hw hdegree (S.generic_regular hx)] at ht
  omega

/-- The selected maximal cones cover the entire ambient space, including every boundary
point; this follows from generic degree one and closedness. -/
theorem selected_eq_univ (c : I → ℤ) (hc0 : ∀ i, 0 ≤ c i) (hc : S.IsCycle c)
    {w : V} (hw : S.Generic w) (hdegree : S.multiplicity c w = 1) :
    S.Selected c = Set.univ := by
  have hs : {x | S.Generic x} ⊆ S.Selected c := by
    intro x hx
    apply S.mem_selected_of_weightedDegree_pos c hc0
    rw [S.weightedDegree_eq_two c hc hw hdegree (S.generic_regular hx)]
    norm_num
  have hd := S.generic_dense.mono hs
  exact (S.selected_isClosed c).closure_eq.symm.trans hd.closure_eq

/-- The difficult boundary conclusion: the actual smallest faces of any two selected
cones through a common point agree. -/
theorem selected_minimalFace_eq (c : I → ℤ) (hc0 : ∀ i, 0 ≤ c i) (hc : S.IsCycle c)
    {w : V} (hw : S.Generic w) (hdegree : S.multiplicity c w = 1)
    {i j : I} (hi : 0 < c i) (hj : 0 < c j) {x : V}
    (hxi : x ∈ S.cone i) (hxj : x ∈ S.cone j) :
    MinimalFaces.dominatedCone (S.cone i) x = MinimalFaces.dominatedCone (S.cone j) x := by
  let F := MinimalFaces.dominatedCone (S.cone i) x
  let G := MinimalFaces.dominatedCone (S.cone j) x
  have hFi : F.IsFaceOf (S.cone i) := MinimalFaces.dominatedCone_isFaceOf _ _
  have hGj : G.IsFaceOf (S.cone j) := MinimalFaces.dominatedCone_isFaceOf _ _
  have hxF : Active F x := (S.active_iff hFi).2 ⟨hxi, rfl⟩
  have hxG : Active G x := (S.active_iff hGj).2 ⟨hxj, rfl⟩
  have hFnb := S.star_selected_mem_nhds c hc0 hc hxF hFi hi
  have hGnb := S.star_selected_mem_nhds c hc0 hc hxG hGj hj
  obtain ⟨y, hygen, hyF, hyG⟩ :=
    S.generic_dense.inter_nhds_nonempty (Filter.inter_mem hFnb hGnb)
  obtain ⟨k, hk, hyk⟩ := hyF
  obtain ⟨l, hl, hyl⟩ := hyG
  obtain ⟨hFk, hck⟩ := (S.starCoeff_pos_iff c F k).1 hk
  obtain ⟨hGl, hcl⟩ := (S.starCoeff_pos_iff c G l).1 hl
  have hkl := S.selected_index_unique_at_generic c hc0 hc hw hdegree hygen hck hcl hyk hyl
  subst l
  exact MinimalFaces.equal_of_common_supercone hxi hxj hFk hGl

/-- Every subcone of a finitely generated cone has a point which detects every containing
face of the ambient cone. No finite-generation hypothesis on the subcone is required. -/
theorem exists_face_detecting_point_in_subcone {C T : PointedCone ℝ V}
    (hC : C.FG) (hTC : T ≤ C) :
    ∃ x ∈ T, ∀ F : PointedCone ℝ V, F.IsFaceOf C → x ∈ F → T ≤ F := by
  classical
  letI : Finite C.Face := PointedCone.FG.finite_face hC
  letI : Fintype C.Face := Fintype.ofFinite _
  have hex : ∀ F : C.Face, ∃ y ∈ T, (¬ T ≤ F.toPointedCone → y ∉ F.toPointedCone) := by
    intro F
    by_cases h : T ≤ F.toPointedCone
    · exact ⟨0, T.zero_mem, fun hn => (hn h).elim⟩
    · obtain ⟨y, hyT, hyF⟩ := Set.not_subset.1
        (show ¬ (T : Set V) ⊆ (F.toPointedCone : Set V) from h)
      exact ⟨y, hyT, fun _ => hyF⟩
  choose y hyT hyF using hex
  refine ⟨∑ F, y F, T.sum_mem (fun F _ => hyT F), ?_⟩
  intro F hF hx
  by_contra hn
  exact hyF ⟨F, hF⟩ hn
    (hF.mem_of_sum_mem (fun G => hTC (hyT G)) hx ⟨F, hF⟩)

/-- Exact face-to-face intersection for every pair of selected cones. The intersection
condition is proved from the cycle equations, not required in the input. -/
theorem selected_intersection_isFaceOf (c : I → ℤ) (hc0 : ∀ i, 0 ≤ c i)
    (hc : S.IsCycle c) {w : V} (hw : S.Generic w) (hdegree : S.multiplicity c w = 1)
    {i j : I} (hi : 0 < c i) (hj : 0 < c j) :
    (S.cone i ⊓ S.cone j).IsFaceOf (S.cone i) := by
  obtain ⟨x, hx, hdetect⟩ := exists_face_detecting_point_in_subcone (S.fg i)
    (show S.cone i ⊓ S.cone j ≤ S.cone i from inf_le_left)
  have he := S.selected_minimalFace_eq c hc0 hc hw hdegree hi hj hx.1 hx.2
  have hFi := MinimalFaces.dominatedCone_isFaceOf (S.cone i) x
  have hFj : (MinimalFaces.dominatedCone (S.cone i) x).IsFaceOf (S.cone j) := by
    rw [he]
    exact MinimalFaces.dominatedCone_isFaceOf _ _
  have hEq : S.cone i ⊓ S.cone j = MinimalFaces.dominatedCone (S.cone i) x :=
    le_antisymm (hdetect _ hFi (MinimalFaces.self_mem_dominatedCone hx.1))
      (le_inf hFi.le hFj.le)
  rw [hEq]
  exact hFi

/-- The full geometric content of positive degree-one gluing in every finite dimension. -/
theorem positive_degree_one_geometric (c : I → ℤ) (hc0 : ∀ i, 0 ≤ c i)
    (hc : S.IsCycle c) {w : V} (hw : S.Generic w) (hdegree : S.multiplicity c w = 1) :
    (∀ i, c i = 0 ∨ c i = 1) ∧
    (∀ x : V, ∃ i, c i = 1 ∧ x ∈ S.cone i) ∧
    (∀ i j, c i = 1 → c j = 1 → (S.cone i ⊓ S.cone j).IsFaceOf (S.cone i)) := by
  refine ⟨S.coeff_zero_or_one c hc0 hc hw hdegree, ?_, ?_⟩
  · intro x
    have hx : x ∈ S.Selected c := by rw [S.selected_eq_univ c hc0 hc hw hdegree]; trivial
    obtain ⟨i, hi, hxi⟩ := hx
    exact ⟨i, S.positive_coeff_eq_one c hc0 hc hw hdegree hi, hxi⟩
  · intro i j hi hj
    apply S.selected_intersection_isFaceOf c hc0 hc hw hdegree <;> omega

end Unimodular.CycleDegree.FullCones
