module

public import PaperVerification.ToricStarPositivePullback
public import PaperVerification.ToricSimultaneousParents
public import PaperVerification.ToricSelectedNoPositive

@[expose] public section

/-!
# Actual old edge bounds for positive selected divisors

A positive new sum ray is an endpoint of a genuine invariant wall. The
two old parent cones give an actual old lattice edge with precisely the
pullback degree. If no new ray is positive, the proved primitive pushdown
gives an old contractible relation. Unblown codimension-one selected
divisors are included in the latter case.
-/

noncomputable section

namespace PaperVerification.ToricGeometry

open scoped BigOperators Classical

namespace SmoothCompleteFan

variable {n : ℕ} («Σ» : SmoothCompleteFan n)
variable {ι : Type*} [Fintype ι] (T : ι → Finset (Lattice n))
variable (hT : ∀ i, T i ∈ «Σ».cones) (hne : ∀ i, (T i).Nonempty)
variable (hdisj : «Σ».PairwiseDisjointFoci T) (hcard : ∀ i, 2 ≤ (T i).card)

include hcard in
/-- A positive exceptional endpoint has exactly the length of a genuine
old edge as its pullback degree. Both endpoints may be new sum rays. -/
theorem simultaneous_positive_pullback_degree_eq_edge_length
    (hpure : «Σ».IsPure) (P : LatticePolytope n) (hP : P.Smooth)
    (hfan : «Σ».realCones = P.normalFan)
    (S : («Σ».simultaneousSubdivision T hT hne hdisj).PrimitiveRelation)
    (hS : S.IsCombinatoriallyContractible) (i : ι)
    (hi : (∑ v ∈ T i, v) ∈ S.positive) :
    ∃ v w : Lattice n, P.IsEdge (embed n v) (embed n w) ∧
      S.degree (simultaneousSupport T (fun u => (P.integralSupport u : ℝ)) 0) =
        (LatticePolytope.latticeLength v w : ℝ) := by
  let Γ := «Σ».simultaneousSubdivision T hT hne hdisj
  let e := ∑ v ∈ T i, v
  let a : Lattice n → ℝ := fun u => (P.integralSupport u : ℝ)
  let B := simultaneousSupport T a 0
  have hΓpure := «Σ».isPure_simultaneousSubdivision T hpure hT hne hdisj
  have hex : ∃ x ∈ S.positive, x ≠ e := by
    by_contra hn
    push_neg at hn
    have hsub : S.positive ⊆ {e} := by
      intro x hx
      exact Finset.mem_singleton.mpr (hn x hx)
    exact S.primitive.2.1 (Γ.downward {e}
      (Γ.singleton_mem_of_mem_rays (S.primitive.1 hi)) S.positive hsub)
  obtain ⟨z, hzP, hze⟩ := hex
  have hcore := S.contractible_core_cone hS hzP
  obtain ⟨U, hU, hcoreU, hUcard⟩ := hΓpure _ hcore
  have heU : e ∈ U := hcoreU
    (Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨hze.symm, hi⟩))
  have hNU : S.negative ⊆ U := fun u hu => hcoreU (Finset.mem_union_right _ hu)
  obtain ⟨b, hb⟩ := Γ.full_cone_basis hU hUcard
  obtain ⟨j, hj, hbj⟩ := Finset.mem_image.mp (hb ▸ heU)
  obtain ⟨x, hxP, hxU, hPdiff, hxcone, hxcoords⟩ :=
    S.replacement_across_full_wall hS U hU b hb hNU j (hbj.symm ▸ hi)
  let W := U.erase e
  have heW : e ∉ W := by simp [W]
  have hUinsert : insert e W = U := Finset.insert_erase heU
  have hN : S.negative ⊆ W := by
    intro u hu
    refine Finset.mem_erase.mpr ⟨?_, hNU hu⟩
    intro hue
    have heN : e ∈ S.negative := hue ▸ hu
    exact Finset.disjoint_left.mp S.disjoint hi heN
  have hxcone' : insert x W ∈ Γ.cones := by simpa only [hbj] using hxcone
  have hxW : x ∉ W := fun hh => hxU (Finset.mem_of_mem_erase hh)
  have hWcard : W.card + 1 = n := by
    dsimp only [W]
    rw [Finset.card_erase_of_mem heU]
    have hUpos := Finset.card_pos.mpr ⟨e, heU⟩
    omega
  have hxcard : (insert x W).card = n := by
    rw [Finset.card_insert_of_notMem hxW]
    exact hWcard
  obtain ⟨hWold, hWrays, hWnone⟩ :=
    «Σ».simultaneous_wall_below_sum_old T hT hne hdisj hcard i W
      (hUinsert.symm ▸ hU) heW
  obtain ⟨p, hpT, hpW, hpcone, hpcard, hTp, hC, he⟩ :=
    «Σ».full_simultaneous_sum_endpoint_parent T hT hne hdisj hcard i W
      (hUinsert.symm ▸ hU) (hUinsert.symm ▸ hUcard) heW
  obtain ⟨q, D, hqcone, hqcard, hD, hx, hqkind⟩ :=
    «Σ».full_simultaneous_endpoint_parent T hT hne hdisj hcard W x hWnone hxcone' hxcard
  obtain ⟨d, hd⟩ := «Σ».full_cone_basis hpcone hpcard
  obtain ⟨k, hk, hdk⟩ := Finset.mem_image.mp (hd ▸ Finset.mem_insert_self p W)
  have hWbasis : W = (Finset.univ.erase k).image d := by
    rw [Finset.image_erase d.injective, ← hd, hdk,
      Finset.erase_insert_eq_erase, Finset.erase_eq_of_notMem hpW]
  have hBwall (u : Lattice n) (hu : u ∈ W) : B u = a u :=
    «Σ».simultaneousSupport_old T hT hcard a 0 u (hWrays hu)
  have hinj := «Σ».simultaneous_sum_rays_injective T hT hdisj
  have hBe : B e = a p + ∑ u ∈ (T i).erase p, a u := by
    change simultaneousSupport T a 0 (∑ v ∈ T i, v) = _
    rw [simultaneousSupport_at_sum T hinj, Pi.zero_apply, sub_zero,
      ← Finset.add_sum_erase (T i) a hpT]
  have hBx : B x = a q + ∑ u ∈ D, a u := by
    rcases hqkind with ⟨hxold, hqx, hDempty⟩ | ⟨l, hxsum, hql, rfl⟩
    · change simultaneousSupport T a 0 x = _
      rw [«Σ».simultaneousSupport_old T hT hcard a 0 x hxold,
        hqx, hDempty, Finset.sum_empty, add_zero]
    · change simultaneousSupport T a 0 x = _
      rw [hxsum, simultaneousSupport_at_sum T hinj, Pi.zero_apply, sub_zero,
        ← Finset.add_sum_erase (T l) a hql]
  apply P.positive_sum_pullback_degree_eq_edge_length hP «Σ» hfan d
    (hd ▸ hpcone) k ((T i).erase p) D q e x
    (hWbasis ▸ hC) (hWbasis ▸ hD)
    (by simpa only [hdk] using he) hx (hWbasis ▸ hqcone) Γ S hi
    (hWbasis ▸ hN)
    (by simpa only [← hWbasis, hUinsert] using hPdiff) B
  · intro u hu
    exact hBwall u (hWbasis.symm ▸ hu)
  · simpa only [hdk] using hBe
  · exact hBx

end SmoothCompleteFan

namespace SmoothCompleteFan

variable {n : ℕ} («Σ» : SmoothCompleteFan n)
variable {ι : Type*} [Fintype ι] (R : ι → «Σ».PrimitiveRelation)
variable (hne : ∀ i, (R i).negative.Nonempty)
variable (hdisj : «Σ».PairwiseDisjointFoci (fun i => (R i).negative))

/-- Whenever some selected divisor is positive, the original literal
edge threshold is inherited by the full pullback degree. This includes
selected old divisor rays of codimension one. -/
theorem selected_positive_pullback_degree_lower_bound
    (hpure : «Σ».IsPure) (P : LatticePolytope n) (hP : P.Smooth)
    (hfan : «Σ».realCones = P.normalFan) {bound : ℕ} (hbound : P.EdgesAtLeast bound)
    (S : («Σ».selectedFan R hne hdisj).PrimitiveRelation)
    (hS : S.IsCombinatoriallyContractible)
    (hpositive : ∃ i : ι, «Σ».selectedRay R i ∈ S.positive) :
    (bound : ℝ) ≤ S.degree («Σ».selectedPullback R (fun u => (P.integralSupport u : ℝ))) := by
  let T := «Σ».selectedStarFocus R
  have hT (i : «Σ».BlowupIndices R) : T i ∈ «Σ».cones := (R i).negative_cone
  have hTne (i : «Σ».BlowupIndices R) : (T i).Nonempty := hne i
  have hTd := «Σ».selectedStarFocus_disjoint R hdisj
  have hTc (i : «Σ».BlowupIndices R) : 2 ≤ (T i).card := i.property
  by_cases hex : ∃ i : «Σ».BlowupIndices R, «Σ».selectedRay R i ∈ S.positive
  · obtain ⟨i, hi⟩ := hex
    apply P.degree_lower_bound_of_edge_length S
      («Σ».selectedPullback R (fun u => (P.integralSupport u : ℝ))) hbound
    exact «Σ».simultaneous_positive_pullback_degree_eq_edge_length T hT hTne hTd hTc
      hpure P hP hfan S hS i hi
  · have hnone (i : «Σ».BlowupIndices R) : (∑ v ∈ T i, v) ∉ S.positive := by
      intro hh
      exact hex ⟨i, hh⟩
    have hnotfocus (i : «Σ».BlowupIndices R) : S.positive ≠ T i := by
      intro hfocus
      obtain ⟨j, hj⟩ := hpositive
      have hjN : «Σ».selectedRay R j ∈ (R i).negative := by
        change «Σ».selectedRay R j ∈ T i
        exact hfocus ▸ hj
      by_cases hji : j = (i : ι)
      · subst j
        have hOld := «Σ».ray_mem_of_mem_cone (R i).negative_cone hjN
        exact «Σ».sum_rays_not_mem_rays (R i).negative_cone i.property hOld
      · exact «Σ».selected_ray_not_negative_of_ne R hdisj j i hji hjN
    obtain ⟨Q, hQP, hQ, hdeg⟩ :=
      «Σ».simultaneous_contractible_pushdown T hT hTne hTd hTc S hS hnone hnotfocus
    have hdegree : S.degree («Σ».selectedPullback R (fun u => (P.integralSupport u : ℝ))) =
        Q.degree (fun u => (P.integralSupport u : ℝ)) := by
      change S.degree (simultaneousSupport T (fun u => (P.integralSupport u : ℝ)) 0) = _
      rcases hdeg with h | ⟨i, hi, h⟩
      · exact h _ 0
      · have hh := h (fun u => (P.integralSupport u : ℝ))
          (0 : «Σ».BlowupIndices R → ℝ)
        rw [Pi.zero_apply, mul_zero, add_zero] at hh
        exact hh
    rw [hdegree]
    exact P.contractible_degree_lower_bound hP «Σ» hpure hfan hbound Q hQ

end SmoothCompleteFan

end PaperVerification.ToricGeometry
