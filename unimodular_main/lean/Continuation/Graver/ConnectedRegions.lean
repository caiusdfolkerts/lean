module

public import Continuation.Graver.PrimitiveRegions
public import Continuation.Graver.ConeBridges

/-!
# Connected interiors of primitive replacement regions

The coefficients are a primitive element of the literal integer kernel:
every original facet equation and the actual generic degree equation
are retained. If the replacement region had an open separation, restrict
the coefficients to the cones on one side. Cones contributing to a
common facet row lie on the same side by `common_facet_bridge`; cones
contributing to the degree row meet at the prescribed generic point.
The restriction is therefore another conformal kernel vector, which
primitivity forces to be the whole vector.
-/

@[expose] public noncomputable section
set_option autoImplicit false

open scoped Topology BigOperators
open Set

namespace Unimodular.PrimitiveRegions

attribute [local instance] Classical.propDecidable

variable {I : Type*} [Fintype I]

/-- A row equation survives restriction when all its nonzero terms
belong to the same side of the restriction. -/
theorem restrict_pairing_eq_zero (c a : I → ℤ) (s : Set I)
    (hzero : ∑ i, c i * a i = 0)
    (hside : ∀ i j, c i * a i ≠ 0 → c j * a j ≠ 0 →
      (i ∈ s ↔ j ∈ s)) :
    ∑ i, restrictCoeffs c s i * a i = 0 := by
  by_cases hactive : ∃ i ∈ s, c i * a i ≠ 0
  · obtain ⟨i, hi, hia⟩ := hactive
    calc
      ∑ j, restrictCoeffs c s j * a j = ∑ j, c j * a j := by
        apply Finset.sum_congr rfl
        intro j _
        by_cases hja : c j * a j = 0
        · by_cases hj : j ∈ s <;> simp [restrictCoeffs, hj, hja]
        · have hj := (hside i j hia hja).mp hi
          simp only [restrictCoeffs, if_pos hj]
      _ = 0 := hzero
  · apply Finset.sum_eq_zero
    intro i _
    by_cases hi : i ∈ s
    · have hia : c i * a i = 0 := by
        by_contra hia
        exact hactive ⟨i, hi, hia⟩
      simpa only [restrictCoeffs, if_pos hi] using hia
    · simp [restrictCoeffs, hi]

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [FiniteDimensional ℝ V]

/-- Membership in either side of a disjoint open cover is constant on
a preconnected set. -/
theorem open_side_constant {K u v : Set V} (hK : IsPreconnected K)
    (hu : IsOpen u) (hv : IsOpen v) (huv : Disjoint u v)
    (hcover : K ⊆ u ∪ v) {x y : V} (hx : x ∈ K) (hy : y ∈ K) :
    (x ∈ u ↔ y ∈ u) := by
  rcases hK.subset_or_subset hu hv huv hcover with h | h
  · exact ⟨fun _ => h hy, fun _ => h hx⟩
  · constructor
    · intro hxu
      exact False.elim (Set.disjoint_left.1 huv hxu (h hx))
    · intro hyu
      exact False.elim (Set.disjoint_left.1 huv hyu (h hy))

variable (S : CycleDegree.FullCones I V)

/-- Every cone with a nonzero coefficient lies in the common closed
region, regardless of the sign of its coefficient. -/
theorem cone_subset_selected_of_ne_zero (c : I → ℤ)
    (heq : S.Selected c = S.Selected (-c)) {i : I} (hi : c i ≠ 0) :
    (S.cone i : Set V) ⊆ S.Selected c := by
  intro x hx
  rcases lt_or_gt_of_ne hi with hneg | hpos
  · rw [heq]
    exact ⟨i, neg_pos.2 hneg, hx⟩
  · exact ⟨i, hpos, hx⟩

/-- An open set meeting the interior of the replacement region meets
the interior of an actual positive cone. -/
theorem exists_positive_cone_meeting_open (c : I → ℤ) {u : Set V}
    (hu : IsOpen u) (hne : (interior (S.Selected c) ∩ u).Nonempty) :
    ∃ i, 0 < c i ∧ (interior (S.cone i : Set V) ∩ u).Nonempty := by
  obtain ⟨x, hx, hxu⟩ := hne
  obtain ⟨i, hi, hxi⟩ := interior_subset hx
  obtain ⟨y, hyu, hyi⟩ :=
    (mem_closure_iff.1 (S.cone_subset_closure_interior i hxi)) u hu hxu
  exact ⟨i, hi, y, hyi, hyu⟩

/-- A primitive replacement region has no nontrivial disjoint open
partition of its interior. -/
theorem primitive_no_open_partition {c : I → ℤ} {w : V}
    (hw : S.Generic w) (hc : Graver.Primitive (zeroCycles S w) c)
    {u v : Set V} (hu : IsOpen u) (hv : IsOpen v) (huv : Disjoint u v)
    (hcover : interior (S.Selected c) ⊆ u ∪ v)
    (hune : (interior (S.Selected c) ∩ u).Nonempty)
    (hvne : (interior (S.Selected c) ∩ v).Nonempty) : False := by
  have heq := selected_eq_neg S c hc.1.1 hw hc.1.2
  have hcone (i : I) (hi : c i ≠ 0) :
      (S.cone i : Set V) ⊆ S.Selected c :=
    cone_subset_selected_of_ne_zero S c heq hi
  have hint (i : I) (hi : c i ≠ 0) :
      interior (S.cone i : Set V) ⊆ interior (S.Selected c) :=
    interior_mono (hcone i hi)
  have hside (i : I) (hi : c i ≠ 0) {x : V}
      (hx : x ∈ interior (S.cone i : Set V)) :
      (S.center i ∈ u ↔ x ∈ u) :=
    open_side_constant
      (S.cone i : ConvexCone ℝ V).convex.interior.isPreconnected
      hu hv huv ((hint i hi).trans hcover) (S.center_mem_interior i) hx
  let s : Set I := {i | S.center i ∈ u}
  have hboundary : S.IsCycle (restrictCoeffs c s) := by
    intro F
    apply restrict_pairing_eq_zero c (S.boundary F) s (hc.1.1 F)
    intro i j hi hj
    have hci : c i ≠ 0 := left_ne_zero_of_mul hi
    have hcj : c j ≠ 0 := left_ne_zero_of_mul hj
    have hFi : F.1.IsFaceOf (S.cone i) := by
      by_contra hn
      exact hi (by simp [CycleDegree.FullCones.boundary, hn])
    have hFj : F.1.IsFaceOf (S.cone j) := by
      by_contra hn
      exact hj (by simp [CycleDegree.FullCones.boundary, hn])
    obtain ⟨K, hK, hiK, hjK, hKunion⟩ := common_facet_bridge S F hFi hFj
    have hKT : K ⊆ interior (S.Selected c) :=
      hKunion.trans (interior_mono (union_subset (hcone i hci) (hcone j hcj)))
    exact open_side_constant hK hu hv huv (hKT.trans hcover)
      (hiK (S.center_mem_interior i)) (hjK (S.center_mem_interior j))
  let a : I → ℤ := fun i => if w ∈ interior (S.cone i : Set V) then 1 else 0
  have hdegree_eq (d : I → ℤ) :
      S.multiplicity d w = ∑ i, d i * a i := by
    apply Finset.sum_congr rfl
    intro i _
    dsimp [a]
    split_ifs <;> simp
  have hdegree : S.multiplicity (restrictCoeffs c s) w = 0 := by
    rw [hdegree_eq]
    apply restrict_pairing_eq_zero c a s
    · rw [← hdegree_eq]
      exact hc.1.2
    · intro i j hi hj
      have hci : c i ≠ 0 := left_ne_zero_of_mul hi
      have hcj : c j ≠ 0 := left_ne_zero_of_mul hj
      have hwi : w ∈ interior (S.cone i : Set V) := by
        by_contra hn
        exact hi (by simp [a, hn])
      have hwj : w ∈ interior (S.cone j : Set V) := by
        by_contra hn
        exact hj (by simp [a, hn])
      exact (hside i hci hwi).trans (hside j hcj hwj).symm
  obtain ⟨i, hi, y, hyi, hyu⟩ := exists_positive_cone_meeting_open S c hu hune
  have his : i ∈ s := (hside i hi.ne' hyi).mpr hyu
  have hrestrict : restrictCoeffs c s = c :=
    primitive_restriction_eq hc s ⟨hboundary, hdegree⟩ ⟨i, his, hi.ne'⟩
  obtain ⟨j, hj, z, hzj, hzv⟩ := exists_positive_cone_meeting_open S c hv hvne
  have hjs : j ∈ s := by
    by_contra hn
    have he := congrFun hrestrict j
    simp only [restrictCoeffs, if_neg hn] at he
    exact hj.ne' he.symm
  have hzu : z ∈ u := (hside j hj.ne' hzj).mp hjs
  exact Set.disjoint_left.1 huv hzu hzv

/-- The common closed region of a primitive signed replacement has a
nonempty connected interior, as asserted in Section 3.3. -/
theorem primitive_region_connected {c : I → ℤ} {w : V}
    (hw : S.Generic w) (hc : Graver.Primitive (zeroCycles S w) c) :
    IsConnected (interior (S.Selected c)) := by
  have heq := selected_eq_neg S c hc.1.1 hw hc.1.2
  have hne : ∃ i, c i ≠ 0 := by
    by_contra hn
    push_neg at hn
    exact hc.2.1 (funext hn)
  obtain ⟨i, hi⟩ := hne
  refine ⟨⟨S.center i, ?_⟩, ?_⟩
  · exact interior_mono (cone_subset_selected_of_ne_zero S c heq hi)
      (S.center_mem_interior i)
  · intro u v hu hv hcover hune hvne
    by_contra hn
    let U := interior (S.Selected c) ∩ u
    let W := interior (S.Selected c) ∩ v
    have hU : IsOpen U := isOpen_interior.inter hu
    have hW : IsOpen W := isOpen_interior.inter hv
    have hUW : Disjoint U W := by
      apply Set.disjoint_left.2
      intro x hxU hxW
      exact hn ⟨x, hxU.1, hxU.2, hxW.2⟩
    have hcvr : interior (S.Selected c) ⊆ U ∪ W := by
      intro x hx
      rcases hcover hx with hxu | hxv
      · exact Or.inl ⟨hx, hxu⟩
      · exact Or.inr ⟨hx, hxv⟩
    have hUne : (interior (S.Selected c) ∩ U).Nonempty := by
      obtain ⟨x, hx, hxu⟩ := hune
      exact ⟨x, hx, hx, hxu⟩
    have hWne : (interior (S.Selected c) ∩ W).Nonempty := by
      obtain ⟨x, hx, hxv⟩ := hvne
      exact ⟨x, hx, hx, hxv⟩
    exact primitive_no_open_partition S hw hc hU hW hUW hcvr hUne hWne

end Unimodular.PrimitiveRegions

#print axioms Unimodular.PrimitiveRegions.primitive_region_connected

