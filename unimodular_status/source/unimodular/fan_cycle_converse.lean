module

public import Unimodular.DegreeOneGluing

@[expose] public section

open scoped Pointwise Topology BigOperators
open Filter Set

namespace Unimodular.CycleDegree.FullCones

attribute [local instance] Classical.propDecidable

variable {I V : Type*} [Fintype I] [NormedAddCommGroup V] [NormedSpace ℝ V]
  [FiniteDimensional ℝ V] (S : FullCones I V)

/-- The usual geometric conditions for the maximal cones of a complete fan, written on
their indicator vector. The complete fan itself is constructed separately from these data. -/
structure CompleteDecomposition (c : I → ℤ) : Prop where
  indicator : ∀ i, c i = 0 ∨ c i = 1
  cover : ∀ x : V, ∃ i, c i = 1 ∧ x ∈ S.cone i
  faces : ∀ i j, c i = 1 → c j = 1 → (S.cone i ⊓ S.cone j).IsFaceOf (S.cone i)

theorem completeDecomposition_of_cycle (c : I → ℤ) (hc0 : ∀ i, 0 ≤ c i)
    (hc : S.IsCycle c) {w : V} (hw : S.Generic w) (hdegree : S.multiplicity c w = 1) :
    S.CompleteDecomposition c := by
  obtain ⟨h1, h2, h3⟩ := S.positive_degree_one_geometric c hc0 hc hw hdegree
  exact ⟨h1, h2, h3⟩

theorem selected_unique_of_interior (hinj : Function.Injective S.cone)
    {c : I → ℤ} (hd : S.CompleteDecomposition c) {i j : I}
    (hi : c i = 1) (hj : c j = 1) {x : V}
    (hxi : x ∈ interior (S.cone i : Set V)) (hxj : x ∈ interior (S.cone j : Set V)) : i = j := by
  have he1 := ConeInterior.face_eq_of_mem_interior (hd.faces i j hi hj)
    (show x ∈ S.cone i ⊓ S.cone j from ⟨interior_subset hxi, interior_subset hxj⟩) hxi
  have he2 := ConeInterior.face_eq_of_mem_interior (hd.faces j i hj hi)
    (show x ∈ S.cone j ⊓ S.cone i from ⟨interior_subset hxj, interior_subset hxi⟩) hxj
  apply hinj
  exact he1.symm.trans ((inf_comm _ _).trans he2)

theorem weightedDegree_eq_two_of_no_selected_boundary (hinj : Function.Injective S.cone)
    {c : I → ℤ} (hd : S.CompleteDecomposition c) {x : V}
    (hx : ∀ i, c i = 1 → x ∈ S.cone i → x ∈ interior (S.cone i : Set V)) :
    S.weightedDegree c x = 2 := by
  classical
  obtain ⟨i, hi, hxi⟩ := hd.cover x
  unfold weightedDegree
  rw [Finset.sum_eq_single i]
  · rw [hi, FacetLine.weight_of_interior (hx i hi hxi)]; norm_num
  · intro j _ hji
    rcases hd.indicator j with hj | hj
    · rw [hj, zero_mul]
    · have hn : x ∉ S.cone j := by
        intro hxj
        exact hji (S.selected_unique_of_interior hinj hd hj hi (hx j hj hxj) (hx i hi hxi))
      rw [FacetLine.weight_of_outside hn, mul_zero]
  · simp

theorem multiplicity_eq_one_of_completeDecomposition (hinj : Function.Injective S.cone)
    {c : I → ℤ} (hd : S.CompleteDecomposition c) {x : V} (hx : S.Generic x) :
    S.multiplicity c x = 1 := by
  have he := S.weightedDegree_eq_two_of_no_selected_boundary hinj hd
    (fun i _ hi => S.generic_interior hx i hi)
  rw [S.weightedDegree_eq_two_mul hx c] at he
  omega

theorem face_fg {F : PointedCone ℝ V} (hF : S.IsFace F) : F.FG := by
  classical
  obtain ⟨i, hFi⟩ := hF
  obtain ⟨s, hs⟩ := S.fg i
  have he := PointedCone.Face.eq_hull_inter_of_eq_hull ⟨F, hFi⟩ (s : Set V) hs.symm
  change F = PointedCone.hull ℝ ((s : Set V) ∩ (F : Set V)) at he
  refine ⟨s.filter (fun x => x ∈ F), ?_⟩
  simpa [Finset.coe_filter, Set.inter_def] using he.symm

theorem exists_active_point {F : PointedCone ℝ V} (hF : S.IsFace F) : ∃ x, Active F x := by
  obtain ⟨x, hx, hdetect⟩ := FanProducts.exists_face_detecting_point F (S.face_fg hF)
  refine ⟨x, hx, ?_⟩
  exact le_antisymm (MinimalFaces.dominatedCone_isFaceOf F x).le
    (hdetect _ (MinimalFaces.dominatedCone_isFaceOf F x) (MinimalFaces.self_mem_dominatedCone hx))

/-- In an actual complete face-to-face decomposition, every cone containing a relative
interior point of a selected face contains that entire face. -/
theorem face_of_mem_at_active {c : I → ℤ} (hd : S.CompleteDecomposition c)
    {F : PointedCone ℝ V} {x : V} (hx : Active F x)
    {i j : I} (hi : c i = 1) (hj : c j = 1)
    (hFi : F.IsFaceOf (S.cone i)) (hxj : x ∈ S.cone j) : F.IsFaceOf (S.cone j) := by
  have hm := ((S.active_iff hFi).1 hx).2
  have hle : F ≤ S.cone i ⊓ S.cone j := by
    rw [← hm]
    exact MinimalFaces.dominatedCone_le (hd.faces i j hi hj) ⟨hFi.le hx.1, hxj⟩
  have hFint := (PointedCone.IsFaceOf.isFaceOf_iff_le hFi (hd.faces i j hi hj)).2 hle
  have hIntj : (S.cone i ⊓ S.cone j).IsFaceOf (S.cone j) := by
    rw [inf_comm]
    exact hd.faces j i hj hi
  exact hFint.trans hIntj

theorem eventually_selected_containing_face {c : I → ℤ} (hd : S.CompleteDecomposition c)
    {F : PointedCone ℝ V} {x : V} (hx : Active F x)
    {i : I} (hi : c i = 1) (hFi : F.IsFaceOf (S.cone i)) :
    ∀ᶠ y in 𝓝 x, ∀ j, c j = 1 → y ∈ S.cone j → F.IsFaceOf (S.cone j) := by
  apply Filter.eventually_all.2
  intro j
  by_cases hj : c j = 1
  · by_cases hFj : F.IsFaceOf (S.cone j)
    · exact Filter.Eventually.of_forall (fun _ _ _ => hFj)
    · have hnx : x ∉ S.cone j := fun h => hFj (S.face_of_mem_at_active hd hx hi hj hFi h)
      filter_upwards [(ConeInterior.isClosed_of_fg (S.fg j)).isOpen_compl.mem_nhds hnx]
        with y hy
      exact fun _ hym => (hy hym).elim
  · exact Filter.Eventually.of_forall (fun _ hj' => (hj hj').elim)

theorem signZ_ne_zero {a : ℝ} (ha : a ≠ 0) : FacetLine.signZ a ≠ 0 := by
  rcases lt_or_gt_of_ne ha with h | h
  · rw [FacetLine.signZ_of_neg h]; norm_num
  · rw [FacetLine.signZ_of_pos h]; norm_num

theorem eventually_not_boundary_at_active {F : S.Facet} {x : V} (hx : Active F.1 x)
    (v : V) (hv : S.normal F v ≠ 0) (i : I) (hFi : F.1.IsFaceOf (S.cone i)) :
    ∀ᶠ t : ℝ in 𝓝 0, t ≠ 0 → x + t • v ∈ S.cone i →
      x + t • v ∈ interior (S.cone i : Set V) := by
  have hm := ((S.active_iff hFi).1 hx).2
  have hxi := hFi.le hx.1
  have hne : MinimalFaces.dominatedCone (S.cone i) x ≠ S.cone i := by
    rw [hm]; exact S.facet_ne_cone F i
  have hker : LinearMap.ker (S.normal F) =
      Submodule.span ℝ (MinimalFaces.dominatedCone (S.cone i) x : Set V) := by
    rw [hm]; exact S.normal_ker F
  have he := FacetLine.eventually_weight_at_facet hxi hne (S.normal F) hker
    (S.center_mem_interior i) v
  have hcy := ConeInterior.normal_ne_zero_at_interior hFi (S.facet_ne_cone F i)
    (S.normal F) (S.normal_ker F) (S.center_mem_interior i)
  filter_upwards [he] with t ht ht0 hti
  by_contra hni
  rw [FacetLine.weight_of_boundary hti hni] at ht
  have hn := mul_ne_zero (signZ_ne_zero (mul_ne_zero ht0 hv)) (signZ_ne_zero hcy)
  omega

theorem eventually_star_degree_at_facet (c : I → ℤ) (F : S.Facet) {x : V}
    (hx : Active F.1 x) (v : V) :
    ∀ᶠ t : ℝ in 𝓝 0,
      S.weightedDegree (S.starCoeff c F.1) (x + t • v) =
        S.weightedDegree (S.starCoeff c F.1) x +
        FacetLine.signZ (t * S.normal F v) * ∑ i, c i * S.boundary F i := by
  have he : ∀ i, ∀ᶠ t : ℝ in 𝓝 0,
      S.starCoeff c F.1 i * FacetLine.weight (S.cone i) (x + t • v) =
        S.starCoeff c F.1 i * FacetLine.weight (S.cone i) x +
        FacetLine.signZ (t * S.normal F v) * (c i * S.boundary F i) := by
    intro i
    by_cases hFi : F.1.IsFaceOf (S.cone i)
    · have hm := ((S.active_iff hFi).1 hx).2
      have hxi := hFi.le hx.1
      have hne : MinimalFaces.dominatedCone (S.cone i) x ≠ S.cone i := by
        rw [hm]; exact S.facet_ne_cone F i
      have hker : LinearMap.ker (S.normal F) =
          Submodule.span ℝ (MinimalFaces.dominatedCone (S.cone i) x : Set V) := by
        rw [hm]; exact S.normal_ker F
      have ht := FacetLine.eventually_weight_at_facet hxi hne (S.normal F) hker
        (S.center_mem_interior i) v
      have hni : x ∉ interior (S.cone i : Set V) := fun h =>
        S.facet_ne_cone F i (ConeInterior.face_eq_of_mem_interior hFi hx.1 h)
      filter_upwards [ht] with t ht
      rw [ht, FacetLine.weight_of_boundary hxi hni]
      simp only [starCoeff, boundary, if_pos hFi]
      ring
    · exact Filter.Eventually.of_forall (fun _ => by simp [starCoeff, boundary, hFi])
  filter_upwards [Filter.eventually_all.2 he] with t ht
  unfold weightedDegree
  simp_rw [ht, Finset.sum_add_distrib, ← Finset.mul_sum]

/-- Every oriented facet row cancels for a genuine complete face-to-face decomposition. -/
theorem boundary_eq_zero_of_completeDecomposition (hinj : Function.Injective S.cone)
    {c : I → ℤ} (hd : S.CompleteDecomposition c) (F : S.Facet) :
    ∑ i, c i * S.boundary F i = 0 := by
  classical
  by_cases hex : ∃ i, c i = 1 ∧ F.1.IsFaceOf (S.cone i)
  · obtain ⟨i, hi, hFi⟩ := hex
    obtain ⟨x, hx⟩ := S.exists_active_point F.2.1
    have hvex : ∃ v : V, 0 < S.normal F v := by
      have hex : ∃ v : V, S.normal F v ≠ 0 := by
        by_contra hn
        push_neg at hn
        apply S.normal_ne_zero F
        ext v
        exact hn v
      obtain ⟨v, hv⟩ := hex
      rcases lt_or_gt_of_ne hv with hn | hp
      · exact ⟨-v, by simpa using neg_pos.2 hn⟩
      · exact ⟨v, hp⟩
    obtain ⟨v, hv⟩ := hvex
    have hcont : Continuous (fun t : ℝ => x + t • v) :=
      continuous_const.add (continuous_id.smul continuous_const)
    have hlim : Tendsto (fun t : ℝ => x + t • v) (𝓝 0) (𝓝 x) := by
      simpa using hcont.tendsto (0 : ℝ)
    have hnear := hlim.eventually (S.eventually_selected_containing_face hd hx hi hFi)
    have hb : ∀ᶠ t : ℝ in 𝓝 0, ∀ j, F.1.IsFaceOf (S.cone j) →
        t ≠ 0 → x + t • v ∈ S.cone j → x + t • v ∈ interior (S.cone j : Set V) := by
      apply Filter.eventually_all.2
      intro j
      by_cases hFj : F.1.IsFaceOf (S.cone j)
      · filter_upwards [S.eventually_not_boundary_at_active hx v hv.ne' j hFj]
          with t ht
        exact fun _ => ht
      · exact Filter.Eventually.of_forall (fun _ h => (hFj h).elim)
    have hjump := S.eventually_star_degree_at_facet c F hx v
    have he : ∀ᶠ t : ℝ in 𝓝 0, t ≠ 0 →
        (2 : ℤ) = S.weightedDegree (S.starCoeff c F.1) x +
          FacetLine.signZ (t * S.normal F v) * ∑ j, c j * S.boundary F j := by
      filter_upwards [hnear, hb, hjump] with t hnear hb hjump ht
      have hd2 : S.weightedDegree c (x + t • v) = 2 :=
        S.weightedDegree_eq_two_of_no_selected_boundary hinj hd
          (fun j hj hmem => hb j (hnear j hj hmem) ht hmem)
      have heq : S.weightedDegree (S.starCoeff c F.1) (x + t • v) =
          S.weightedDegree c (x + t • v) := by
        apply Finset.sum_congr rfl
        intro j _
        by_cases hFj : F.1.IsFaceOf (S.cone j)
        · simp [starCoeff, hFj]
        · rcases hd.indicator j with hj | hj
          · simp [starCoeff, hFj, hj]
          · have hn : x + t • v ∉ S.cone j := fun h => hFj (hnear j hj h)
            rw [FacetLine.weight_of_outside hn]
            simp
      rw [heq, hd2] at hjump
      exact hjump
    have hneg : Tendsto (fun t : ℝ => -t) (𝓝 0) (𝓝 0) := by
      simpa using (continuous_neg : Continuous (fun t : ℝ => -t)).tendsto (0 : ℝ)
    have hboth := (he.and (hneg.eventually he)).filter_mono
      (show 𝓝[>] (0 : ℝ) ≤ 𝓝 (0 : ℝ) from nhdsWithin_le_nhds)
    have hpos : ∀ᶠ t : ℝ in 𝓝[>] 0, 0 < t := self_mem_nhdsWithin
    obtain ⟨t, htpos, hplus, hminus⟩ := (hpos.and hboth).exists
    specialize hplus htpos.ne'
    specialize hminus (neg_ne_zero.2 htpos.ne')
    rw [FacetLine.signZ_of_pos (mul_pos htpos hv), one_mul] at hplus
    rw [FacetLine.signZ_of_neg (mul_neg_of_neg_of_pos (neg_neg_of_pos htpos) hv),
      neg_one_mul] at hminus
    omega
  · apply Finset.sum_eq_zero
    intro i _
    rcases hd.indicator i with hi | hi
    · rw [hi, zero_mul]
    · have hF : ¬ F.1.IsFaceOf (S.cone i) := fun h => hex ⟨i, hi, h⟩
      simp [boundary, hF]

/-- Exact geometric equivalence, in arbitrary finite dimension and allowing all
nonsimplicial polyhedral cones. The boundary matrix is built from their actual facets. -/
theorem positive_degree_one_iff_completeDecomposition (hinj : Function.Injective S.cone)
    (c : I → ℤ) {w : V} (hw : S.Generic w) :
    ((∀ i, 0 ≤ c i) ∧ S.IsCycle c ∧ S.multiplicity c w = 1) ↔
      S.CompleteDecomposition c := by
  constructor
  · rintro ⟨hc0, hc, hd⟩
    exact S.completeDecomposition_of_cycle c hc0 hc hw hd
  · intro hd
    refine ⟨?_, ?_, S.multiplicity_eq_one_of_completeDecomposition hinj hd hw⟩
    · intro i
      rcases hd.indicator i with h | h <;> omega
    · exact S.boundary_eq_zero_of_completeDecomposition hinj hd

end Unimodular.CycleDegree.FullCones
