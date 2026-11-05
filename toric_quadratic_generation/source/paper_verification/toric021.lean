module

public import Lean.Elab.BuiltinEvalCommand
public meta import Lean.Elab.BuiltinEvalCommand
public import Lean.Util.CollectAxioms
public meta import Lean.Util.CollectAxioms
public import Lean.Util.FoldConsts
public meta import Lean.Util.FoldConsts
public import Mathlib.Algebra.Order.Archimedean.Basic
public import Mathlib.GroupTheory.QuotientGroup.Defs
public import paper_verification.toric002
public import paper_verification.toric005
public import paper_verification.toric017
public import paper_verification.toric018
public import paper_verification.toric019
public import paper_verification.toric020

@[expose] public section


-- BEGIN ORIGINAL PaperVerification.ToricSelectedPositiveDegrees
section Source_ToricSelectedPositiveDegrees

-- original header: module

-- original header: public import PaperVerification.ToricStarPositivePullback
-- original header: public import PaperVerification.ToricSimultaneousParents
-- original header: public import PaperVerification.ToricSelectedNoPositive

-- original header: @[expose] public section

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
end
end Source_ToricSelectedPositiveDegrees
-- END ORIGINAL PaperVerification.ToricSelectedPositiveDegrees


-- BEGIN ORIGINAL PaperVerification.ToricSelectedDegreeEstimates
section Source_ToricSelectedDegreeEstimates

-- original header: module

-- original header: public import PaperVerification.ToricSelectedPositiveDegrees
-- original header: public import PaperVerification.ToricCorrectionBounds

-- original header: @[expose] public section

/-!
# Exact degree estimates for corrected support functions

The degree is evaluated on the actual primitive relation of the selected
fan.  Constants, old-ray selections, and selected-ray corrections are kept
separate.  In particular, the lower bounds below do not assume nefness or
the containment of any of the boxes they will be used to construct.
-/

noncomputable section

namespace PaperVerification.ToricGeometry

open scoped BigOperators Classical

namespace SmoothCompleteFan.PrimitiveRelation

variable {n : ℕ} {Γ : SmoothCompleteFan n} (S : Γ.PrimitiveRelation)

def negativeCoefficientSum : ℝ := ∑ v ∈ S.negative, (S.coefficient v : ℝ)

def negativeWeightOn (D : Finset (Lattice n)) : ℝ :=
  ∑ v ∈ S.negative, if v ∈ D then (S.coefficient v : ℝ) else 0

theorem negativeCoefficientSum_nonneg : 0 ≤ S.negativeCoefficientSum :=
  Finset.sum_nonneg (fun _ _ => Nat.cast_nonneg _)

theorem card_negative_le_coefficientSum :
    (S.negative.card : ℝ) ≤ S.negativeCoefficientSum := by
  have hh : (∑ v ∈ S.negative, (1 : ℝ)) ≤
      ∑ v ∈ S.negative, (S.coefficient v : ℝ) := by
    apply Finset.sum_le_sum
    intro v hv
    exact_mod_cast S.coefficient_pos v hv
  simpa only [negativeCoefficientSum, Finset.sum_const, nsmul_eq_mul, mul_one] using hh

theorem minimumCoefficient_mul_card_le_sum (hne : S.negative.Nonempty) :
    (S.minimumCoefficient hne : ℝ) * S.negative.card ≤ S.negativeCoefficientSum := by
  have hh : (∑ v ∈ S.negative, (S.minimumCoefficient hne : ℝ)) ≤
      ∑ v ∈ S.negative, (S.coefficient v : ℝ) := by
    apply Finset.sum_le_sum
    intro v hv
    exact_mod_cast (S.minimumCoefficient_spec hne).2.2 v hv
  simpa only [negativeCoefficientSum, Finset.sum_const, nsmul_eq_mul, mul_comm] using hh

theorem negativeWeightOn_nonneg (D : Finset (Lattice n)) :
    0 ≤ S.negativeWeightOn D := by
  apply Finset.sum_nonneg
  intro v hv
  split_ifs <;> positivity

theorem card_negative_inter_le_weight (D : Finset (Lattice n)) :
    ((S.negative ∩ D).card : ℝ) ≤ S.negativeWeightOn D := by
  have hh : (∑ v ∈ S.negative, if v ∈ D then (1 : ℝ) else 0) ≤
      S.negativeWeightOn D := by
    apply Finset.sum_le_sum
    intro v hv
    split_ifs
    · exact_mod_cast S.coefficient_pos v hv
    · exact le_rfl
  simpa only [Finset.sum_boole, Finset.filter_mem_eq_inter] using hh

theorem degree_constant (c : ℝ) :
    S.degree (fun _ => c) = c * ((S.positive.card : ℝ) - S.negativeCoefficientSum) := by
  simp only [degree, negativeCoefficientSum, Finset.sum_const, nsmul_eq_mul]
  rw [← Finset.sum_mul]
  ring

theorem positive_card_eq_fiberDimension_add_one :
    S.positive.card = S.fiberDimension + 1 := by
  have hh := (Γ.primitiveCollection_card_bounds S.primitive).1
  unfold fiberDimension
  omega

theorem degree_constant_subtraction (a : Lattice n → ℝ) (c : ℝ) :
    S.degree (fun v => a v - c) = S.degree a -
      c * ((S.fiberDimension : ℝ) + 1 - S.negativeCoefficientSum) := by
  change S.degree (a - (fun _ => c)) = _
  rw [S.degree_sub, S.degree_constant,
    S.positive_card_eq_fiberDimension_add_one, Nat.cast_add, Nat.cast_one]

theorem degree_indicator (D : Finset (Lattice n)) :
    S.degree (fun v => if v ∈ D then 1 else 0) =
      ((S.positive ∩ D).card : ℝ) - S.negativeWeightOn D := by
  simp only [degree, negativeWeightOn, mul_ite, mul_one, mul_zero,
    Finset.sum_boole, Finset.filter_mem_eq_inter]

/-- The full coefficient calculation used in all three correction
arguments, before discarding any helpful negative coefficient. -/
theorem degree_corrected_support {ι : Type*} [Fintype ι]
    (e : ι → Lattice n) (B : Lattice n → ℝ)
    (c side : ℝ) (D : Finset (Lattice n)) (u : ι → ℝ) :
    S.degree (fun v => B v - c - side * (if v ∈ D then 1 else 0) -
      ∑ i, if v = e i then u i else 0) =
      S.degree B - c * ((S.positive.card : ℝ) - S.negativeCoefficientSum) -
        side * (((S.positive ∩ D).card : ℝ) - S.negativeWeightOn D) -
        (∑ i, if e i ∈ S.positive then u i else 0) +
        ∑ i, if e i ∈ S.negative then (S.coefficient (e i) : ℝ) * u i else 0 := by
  rw [S.degree_sub_finite_ray_corrections]
  have hbase : S.degree (fun v => B v - c - side * (if v ∈ D then 1 else 0)) =
      S.degree B - c * ((S.positive.card : ℝ) - S.negativeCoefficientSum) -
        side * (((S.positive ∩ D).card : ℝ) - S.negativeWeightOn D) := by
    change S.degree ((B - (fun _ => c)) -
      side • (fun v => if v ∈ D then 1 else 0)) = _
    rw [S.degree_sub, S.degree_sub, S.degree_smul,
      S.degree_constant, S.degree_indicator]
  rw [hbase]

end SmoothCompleteFan.PrimitiveRelation

namespace SmoothCompleteFan

variable {n : ℕ} («Σ» : SmoothCompleteFan n)
variable {ι : Type*} [Fintype ι] (R : ι → «Σ».PrimitiveRelation)
variable (hR : ∀ i, (R i).IsCombinatoriallyContractible)
variable (hne : ∀ i, (R i).negative.Nonempty)
variable (hdisj : «Σ».PairwiseDisjointFoci (fun i => (R i).negative))

/-- A contractible relation with a positive selected ray has no negative
selected ray.  This is forced by actual cone incidence, not by a sign
convention on the relation. -/
theorem selected_negative_empty_if_positive
    (S : («Σ».selectedFan R hne hdisj).PrimitiveRelation)
    (hS : S.IsCombinatoriallyContractible) (i : ι)
    (hi : «Σ».selectedRay R i ∈ S.positive) :
    ∀ j, «Σ».selectedRay R j ∉ S.negative := by
  have hex : ∃ x ∈ S.positive, x ≠ «Σ».selectedRay R i := by
    by_contra hn
    push_neg at hn
    have hsub : S.positive ⊆ {«Σ».selectedRay R i} := by
      intro x hx
      exact Finset.mem_singleton.mpr (hn x hx)
    have hcard := Finset.card_le_card hsub
    have htwo := ((«Σ».selectedFan R hne hdisj).primitiveCollection_card_bounds S.primitive).1
    simp only [Finset.card_singleton] at hcard
    omega
  obtain ⟨x, hx, hxi⟩ := hex
  have hcone := S.contractible_core_cone hS hx
  have hie : «Σ».selectedRay R i ∈ S.positive.erase x ∪ S.negative :=
    Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨hxi.symm, hi⟩)
  intro j hj
  by_cases hji : j = i
  · subst j
    exact Finset.disjoint_left.mp S.disjoint hi hj
  · exact «Σ».selected_no_common_rays R hne hdisj i j (Ne.symm hji) hcone hie
      (Finset.mem_union_right _ hj)

theorem selected_correction_sum_one
    (S : («Σ».selectedFan R hne hdisj).PrimitiveRelation)
    (i : ι) (hi : «Σ».selectedRay R i ∈ S.positive)
    (hother : ∀ j, j ≠ i → «Σ».selectedRay R j ∉ S.positive) (u : ι → ℝ) :
    (∑ j, if «Σ».selectedRay R j ∈ S.positive then u j else 0) = u i := by
  rw [Finset.sum_eq_single i]
  · simp only [hi, if_true]
  · intro j hj hji
    simp only [hother j hji, if_false]
  · simp

theorem selected_correction_sum_two
    (S : («Σ».selectedFan R hne hdisj).PrimitiveRelation)
    (i j : ι) (hij : i ≠ j)
    (hi : «Σ».selectedRay R i ∈ S.positive)
    (hj : «Σ».selectedRay R j ∈ S.positive) (u : ι → ℝ) :
    (∑ k, if «Σ».selectedRay R k ∈ S.positive then u k else 0) = u i + u j := by
  have hP := «Σ».primitive_selected_pair_eq R hne hdisj S.primitive i j hij hi hj
  have hinj := «Σ».selectedRay_injective R hdisj
  have hterm (k : ι) :
      (if «Σ».selectedRay R k ∈ S.positive then u k else 0) =
        (if k = i then u i else 0) + (if k = j then u j else 0) := by
    by_cases hki : k = i
    · subst k
      simp only [hP, Finset.mem_insert, Finset.mem_singleton, hinj.eq_iff,
        true_or, if_true, hij, if_false, add_zero]
    · by_cases hkj : k = j
      · subst k
        simp only [hP, Finset.mem_insert, Finset.mem_singleton, hinj.eq_iff,
          or_true, if_true, hij.symm, if_false, zero_add]
      · simp only [hP, Finset.mem_insert, Finset.mem_singleton, hinj.eq_iff,
          hki, hkj, false_or, if_false, add_zero]
  rw [Finset.sum_congr rfl (fun k _ => hterm k), Finset.sum_add_distrib]
  simp

include hR in
/-- The one-positive-selected-ray lower bound, retaining an arbitrary
constant and an arbitrary nonnegative box side. -/
theorem selected_one_positive_degree_bound
    (S : («Σ».selectedFan R hne hdisj).PrimitiveRelation)
    (hS : S.IsCombinatoriallyContractible) (i : ι)
    (hi : «Σ».selectedRay R i ∈ S.positive)
    (hother : ∀ j, j ≠ i → «Σ».selectedRay R j ∉ S.positive)
    (B : Lattice n → ℝ) (bound c side : ℝ) (hc : 0 ≤ c) (hside : 0 ≤ side)
    (hB : bound ≤ S.degree B) (D : Finset (Lattice n))
    (hD : ∀ j, «Σ».selectedRay R j ∉ D) (u : ι → ℝ) :
    bound - c * ((«Σ».selectedBaseDimension R i : ℝ) + 2) -
      side * ((«Σ».selectedBaseDimension R i : ℝ) + 1) - u i ≤
    S.degree (fun v => B v - c - side * (if v ∈ D then 1 else 0) -
      ∑ j, if v = «Σ».selectedRay R j then u j else 0) := by
  have hneg := «Σ».selected_negative_empty_if_positive R hne hdisj S hS i hi
  rw [S.degree_corrected_support,
    «Σ».selected_correction_sum_one R hne hdisj S i hi hother u]
  simp only [hneg, if_false, Finset.sum_const_zero, add_zero]
  have hproper : S.positive ∩ D ⊂ S.positive := by
    refine Finset.ssubset_iff_subset_ne.mpr ⟨Finset.inter_subset_left, ?_⟩
    intro hh
    exact hD i (Finset.mem_inter.mp (hh.symm ▸ hi)).2
  have hcard := Finset.card_lt_card hproper
  have hcardR : ((S.positive ∩ D).card : ℝ) + 1 ≤ (S.positive.card : ℝ) := by
    have hh : (S.positive ∩ D).card + 1 ≤ S.positive.card := by omega
    exact_mod_cast hh
  have hs := «Σ».selected_one_positive_card_bound R hR hne hdisj S i hi hother
  have hsR : (S.positive.card : ℝ) ≤ («Σ».selectedBaseDimension R i : ℝ) + 2 := by
    exact_mod_cast hs
  have hC := S.negativeCoefficientSum_nonneg
  have hNS := S.negativeWeightOn_nonneg D
  nlinarith [mul_nonneg hc hC, mul_nonneg hside hNS,
    mul_nonneg hc (sub_nonneg.mpr hsR),
    mul_nonneg hside (sub_nonneg.mpr (le_trans hcardR hsR))]

/-- The two-positive estimate retains the weighted negative selection.
This term is essential in the second estimate of Proposition 5.2. -/
theorem selected_two_positive_degree_bound
    (S : («Σ».selectedFan R hne hdisj).PrimitiveRelation)
    (hS : S.IsCombinatoriallyContractible) (i j : ι) (hij : i ≠ j)
    (hi : «Σ».selectedRay R i ∈ S.positive)
    (hj : «Σ».selectedRay R j ∈ S.positive)
    (B : Lattice n → ℝ) (bound c side : ℝ) (hc : 0 ≤ c)
    (hB : bound ≤ S.degree B) (D : Finset (Lattice n))
    (hD : ∀ k, «Σ».selectedRay R k ∉ D) (u : ι → ℝ) :
    bound - 2 * c + c * (S.negative.card : ℝ) + side * S.negativeWeightOn D -
      u i - u j ≤
    S.degree (fun v => B v - c - side * (if v ∈ D then 1 else 0) -
      ∑ k, if v = «Σ».selectedRay R k then u k else 0) := by
  have hP := «Σ».primitive_selected_pair_eq R hne hdisj S.primitive i j hij hi hj
  have hef := («Σ».selectedRay_injective R hdisj).ne hij
  have hneg := «Σ».selected_negative_empty_if_positive R hne hdisj S hS i hi
  have hPD : S.positive ∩ D = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro v hv
    obtain ⟨hvP, hvD⟩ := Finset.mem_inter.mp hv
    rcases (by simpa only [hP, Finset.mem_insert, Finset.mem_singleton] using hvP :
      v = «Σ».selectedRay R i ∨ v = «Σ».selectedRay R j) with h | h
    · exact hD i (h ▸ hvD)
    · exact hD j (h ▸ hvD)
  rw [S.degree_corrected_support,
    «Σ».selected_correction_sum_two R hne hdisj S i j hij hi hj u, hPD]
  simp only [hneg, if_false, Finset.sum_const_zero, add_zero,
    Finset.card_empty, Nat.cast_zero, hP, Finset.card_pair hef, Nat.cast_ofNat,
    zero_sub, mul_neg, sub_neg_eq_add]
  have hC := S.card_negative_le_coefficientSum
  nlinarith [mul_nonneg hc (sub_nonneg.mpr hC)]

end SmoothCompleteFan

end PaperVerification.ToricGeometry
end
end Source_ToricSelectedDegreeEstimates
-- END ORIGINAL PaperVerification.ToricSelectedDegreeEstimates


-- BEGIN ORIGINAL PaperVerification.ToricSelectedSupportFormula
section Source_ToricSelectedSupportFormula

-- original header: module

-- original header: public import PaperVerification.ToricSelectedDegreeEstimates

-- original header: @[expose] public section

/-!
# Rewriting a pulled-back correction in actual ray coefficients

This identity includes the discrepancy `q-1` of each inserted ray and
the number of chosen old rays in its focus.  Singleton foci obey the same
formula and introduce no extra discrepancy.
-/

noncomputable section

namespace PaperVerification.ToricGeometry

open scoped BigOperators Classical

namespace SmoothCompleteFan

variable {n : ℕ} («Σ» : SmoothCompleteFan n)
variable {ι : Type*} [Fintype ι] (R : ι → «Σ».PrimitiveRelation)
variable (hne : ∀ i, (R i).negative.Nonempty)
variable (hdisj : «Σ».PairwiseDisjointFoci (fun i => (R i).negative))

def selectedCorrectionWeight (c side : ℝ) (D : Finset (Lattice n))
    (t : ι → ℝ) (i : ι) : ℝ :=
  c * ((R i).negative.card - 1 : ℝ) +
    side * (((R i).negative ∩ D).card : ℝ) + t i

include hne hdisj in
theorem selected_support_coefficient_formula (a : Lattice n → ℝ)
    (c side : ℝ) (D : Finset (Lattice n))
    (hD : ∀ i, «Σ».selectedRay R i ∉ D) (t : ι → ℝ) :
    simultaneousSupport (fun i => (R i).negative)
      (fun v => a v - c - side * (if v ∈ D then 1 else 0)) t =
    fun v => «Σ».selectedPullback R a v - c - side * (if v ∈ D then 1 else 0) -
      ∑ i, if v = «Σ».selectedRay R i then «Σ».selectedCorrectionWeight R c side D t i else 0 := by
  funext v
  by_cases hex : ∃ i, v = «Σ».selectedRay R i
  · obtain ⟨i, rfl⟩ := hex
    rw [«Σ».selectedSupport_at_selected_ray R hdisj,
      «Σ».selectedPullback_at_selected_ray R hne hdisj]
    have hsum : (∑ j, if «Σ».selectedRay R i = «Σ».selectedRay R j then
        «Σ».selectedCorrectionWeight R c side D t j else 0) =
        «Σ».selectedCorrectionWeight R c side D t i := by
      simp only [(«Σ».selectedRay_injective R hdisj).eq_iff]
      simp
    rw [hsum]
    simp only [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul,
      ← Finset.mul_sum, Finset.sum_boole, Finset.filter_mem_eq_inter,
      hD i, if_false, mul_zero, sub_zero, selectedCorrectionWeight]
    ring
  · have hv : ∀ i, v ≠ «Σ».selectedRay R i := by simpa only [not_exists] using hex
    rw [simultaneousSupport_of_not_sum _ _ t v hv]
    have hv' : ∀ i : «Σ».BlowupIndices R,
        v ≠ ∑ w ∈ «Σ».selectedStarFocus R i, w := fun i => hv i
    rw [selectedPullback, simultaneousSupport_of_not_sum _ a 0 v hv']
    simp only [hv, if_false, Finset.sum_const_zero, sub_zero]

include hne hdisj in
/-- A canonical-shift center written in the old fan and in the selected
fan has exactly the same coefficient function, including codimension one. -/
theorem selected_center_coefficient_formula (a : Lattice n → ℝ)
    (c : ℝ) (u : ι → ℝ) :
    simultaneousSupport (fun i => (R i).negative) (fun v => a v - c)
      (fun i => u i - c * ((R i).negative.card - 1 : ℝ)) =
      fun v => «Σ».selectedPullback R a v - c -
        ∑ i, if v = «Σ».selectedRay R i then u i else 0 := by
  have hh := «Σ».selected_support_coefficient_formula R hne hdisj a c 0 ∅
    (by simp) (fun i => u i - c * ((R i).negative.card - 1 : ℝ))
  have hu : «Σ».selectedCorrectionWeight R c 0 ∅
      (fun i => u i - c * ((R i).negative.card - 1 : ℝ)) = u := by
    funext i
    dsimp only [selectedCorrectionWeight]
    ring
  simpa only [zero_mul, sub_zero, hu] using hh

end SmoothCompleteFan

end PaperVerification.ToricGeometry
end
end Source_ToricSelectedSupportFormula
-- END ORIGINAL PaperVerification.ToricSelectedSupportFormula


-- BEGIN ORIGINAL PaperVerification.ToricSimultaneousIntegralSupport
section Source_ToricSimultaneousIntegralSupport

-- original header: module

-- original header: public import PaperVerification.ToricSimultaneousSupport
-- original header: public import Mathlib.Algebra.Order.Archimedean.Basic

-- original header: @[expose] public section

/-!
# Integral strict support after all disjoint star subdivisions

A single sufficiently small reciprocal integer parameter works at every
selected center. Scaling by that integer makes every actual support
coefficient integral, so the terminating primitive reduction applies to the
constructed simultaneous fan without a projectivity assumption.
-/

noncomputable section

namespace PaperVerification.ToricGeometry.SmoothCompleteFan

open scoped BigOperators Classical

variable {n : ℕ} («Σ» : SmoothCompleteFan n)

theorem exists_integral_strictSupport_simultaneousSubdivision
    {ι : Type*} [Fintype ι]
    (T : ι → Finset (Lattice n)) (hT : ∀ i, T i ∈ «Σ».cones)
    (hne : ∀ i, (T i).Nonempty) (hdisj : «Σ».PairwiseDisjointFoci T)
    (hcard : ∀ i, 2 ≤ (T i).card)
    (H : Lattice n → ℤ) (hH : «Σ».IsStrictSupport (fun v => (H v : ℝ))) :
    ∃ K : Lattice n → ℤ,
      («Σ».simultaneousSubdivision T hT hne hdisj).IsStrictSupport
        (fun v => (K v : ℝ)) := by
  obtain ⟨δ, hδ, hsmall⟩ :=
    «Σ».strictSupport_simultaneousSubdivision_all_small T hT hne hdisj hcard
      (fun v => (H v : ℝ)) hH
  obtain ⟨N, hNlarge⟩ := exists_nat_gt (max (1 : ℝ) δ⁻¹)
  have hNR : (0 : ℝ) < N := lt_trans zero_lt_one ((le_max_left _ _).trans_lt hNlarge)
  have hNne : (N : ℝ) ≠ 0 := ne_of_gt hNR
  have hε : (0 : ℝ) < (N : ℝ)⁻¹ := inv_pos.mpr hNR
  have hεle : (N : ℝ)⁻¹ ≤ δ := by
    have hlarge : δ⁻¹ < (N : ℝ) := (le_max_right _ _).trans_lt hNlarge
    have hmul := mul_lt_mul_of_pos_left hlarge hδ
    rw [mul_inv_cancel₀ (ne_of_gt hδ)] at hmul
    simpa only [one_div] using (div_le_iff₀ hNR).mpr hmul.le
  have hs := hsmall (N : ℝ)⁻¹ hε hεle
  have hscaled := IsStrictSupport.smul («Σ».simultaneousSubdivision T hT hne hdisj) hs hNR
  let K : Lattice n → ℤ :=
    simultaneousSupport T (fun v => (N : ℤ) * H v) (fun _ => 1)
  have hcoeff : (fun v => (K v : ℝ)) = (N : ℝ) •
      simultaneousSupport T (fun v => (H v : ℝ)) (fun _ => (N : ℝ)⁻¹) := by
    funext v
    simp only [K, simultaneousSupport, Pi.smul_apply, smul_eq_mul,
      Int.cast_add, Int.cast_sum, Int.cast_mul, Int.cast_natCast,
      mul_add, Finset.mul_sum]
    congr 1
    apply Finset.sum_congr rfl
    intro i hi
    by_cases hv : v = ∑ w ∈ T i, w
    · simp only [if_pos hv, Int.cast_sub, Int.cast_sum, Int.cast_mul,
        Int.cast_natCast, Int.cast_one, mul_sub, Finset.mul_sum,
        mul_inv_cancel₀ hNne]
    · simp only [if_neg hv, Int.cast_zero, mul_zero]
  exact ⟨K, hcoeff.symm ▸ hscaled⟩

end PaperVerification.ToricGeometry.SmoothCompleteFan
end
end Source_ToricSimultaneousIntegralSupport
-- END ORIGINAL PaperVerification.ToricSimultaneousIntegralSupport


-- BEGIN ORIGINAL PaperVerification.ToricSelectedCenterCriterion
section Source_ToricSelectedCenterCriterion

-- original header: module

-- original header: public import PaperVerification.ToricSelectedSupportFormula
-- original header: public import PaperVerification.ToricSimultaneousIntegralSupport
-- original header: public import PaperVerification.ToricExtremalCriterion

-- original header: @[expose] public section

/-!
# A scalar criterion for the genuine selected-fan centers

The selected fan is constructed from the old fan. Its integral strictly
convex support function is proved to exist. The nef conclusion follows
from the actual effective-cone extremal criterion and the three exhaustive
selected-ray cases.
-/

noncomputable section

namespace PaperVerification.ToricGeometry

open scoped BigOperators Classical

namespace SmoothCompleteFan

variable {n : ℕ} («Σ» : SmoothCompleteFan n)
variable {ι : Type*} [Fintype ι] (R : ι → «Σ».PrimitiveRelation)
variable (hR : ∀ i, (R i).IsCombinatoriallyContractible)
variable (hne : ∀ i, (R i).negative.Nonempty)
variable (hdisj : «Σ».PairwiseDisjointFoci (fun i => (R i).negative))

include hR in
theorem selected_center_isNef_of_scalar_bounds
    (hpure : «Σ».IsPure) (P : LatticePolytope n) (hP : P.Smooth)
    (hfan : «Σ».realCones = P.normalFan) {bound : ℕ} (hbound : P.EdgesAtLeast bound)
    (c : ℝ) (hc : 0 ≤ c) (u : ι → ℝ)
    (ht : ∀ i, 0 ≤ u i - c * ((R i).negative.card - 1 : ℝ))
    (hrepair : ∀ i, 0 ≤
      (R i).degree (fun v => (P.integralSupport v : ℝ) - c) +
      ((R i).minimumCoefficient (hne i) : ℝ) *
        (u i - c * ((R i).negative.card - 1 : ℝ)))
    (hinactive : ∀ Q : «Σ».PrimitiveRelation, Q.IsCombinatoriallyContractible →
      (∀ i, «Σ».selectedRay R i ∉ Q.positive) →
      (∀ i, Q.positive ≠ (R i).positive) →
        0 ≤ Q.degree (fun v => (P.integralSupport v : ℝ) - c))
    (hone : ∀ i, 0 ≤ (bound : ℝ) -
      c * ((«Σ».selectedBaseDimension R i : ℝ) + 2) - u i)
    (htwo : ∀ i j, i ≠ j → 0 ≤ (bound : ℝ) - 2 * c +
      c * ((n : ℝ) - 1 - «Σ».selectedBaseDimension R i -
        «Σ».selectedBaseDimension R j) - u i - u j) :
    («Σ».selectedFan R hne hdisj).IsNef
      (fun v => «Σ».selectedPullback R (fun w => (P.integralSupport w : ℝ)) v - c -
        ∑ i, if v = «Σ».selectedRay R i then u i else 0) := by
  let Γ := «Σ».selectedFan R hne hdisj
  let a : Lattice n → ℝ := fun v => (P.integralSupport v : ℝ)
  let t : ι → ℝ := fun i => u i - c * ((R i).negative.card - 1 : ℝ)
  let F : Lattice n → ℝ := fun v => «Σ».selectedPullback R a v - c -
    ∑ i, if v = «Σ».selectedRay R i then u i else 0
  have hF : simultaneousSupport (fun i => (R i).negative) (fun v => a v - c) t = F :=
    «Σ».selected_center_coefficient_formula R hne hdisj a c u
  have hΓpure : Γ.IsPure := «Σ».isPure_simultaneousSubdivision
    («Σ».selectedStarFocus R) hpure (fun i => (R i).negative_cone)
    (fun i => hne i) («Σ».selectedStarFocus_disjoint R hdisj)
  obtain ⟨H, hH⟩ := «Σ».exists_integral_strictSupport_simultaneousSubdivision
    («Σ».selectedStarFocus R) (fun i => (R i).negative_cone)
    (fun i => hne i) («Σ».selectedStarFocus_disjoint R hdisj)
    (fun i => i.property) P.integralSupport
    (P.integralSupport_isStrictSupport «Σ» hfan)
  apply (Γ.isNef_iff_extremal_primitive_nonneg hΓpure H hH F).mpr
  intro S hSext
  have hS := S.combinatoriallyContractible_of_extremal hSext
  by_cases hex : ∃ i, «Σ».selectedRay R i ∈ S.positive
  · obtain ⟨i, hi⟩ := hex
    have hB := «Σ».selected_positive_pullback_degree_lower_bound R hne hdisj
      hpure P hP hfan hbound S hS ⟨i, hi⟩
    by_cases hexj : ∃ j, j ≠ i ∧ «Σ».selectedRay R j ∈ S.positive
    · obtain ⟨j, hji, hj⟩ := hexj
      have hij := hji.symm
      have hcard := («Σ».selected_two_positive_card_bound R hR hne hdisj
        hpure S hS i j hij hi hj).2
      have hcardR : (n : ℝ) ≤ (S.negative.card : ℝ) +
          «Σ».selectedBaseDimension R i + «Σ».selectedBaseDimension R j + 1 := by
        exact_mod_cast hcard
      have hnum : 0 ≤ (bound : ℝ) - 2 * c + c * (S.negative.card : ℝ) - u i - u j := by
        have hh := htwo i j hij
        nlinarith [mul_nonneg hc (sub_nonneg.mpr hcardR)]
      have hdeg := «Σ».selected_two_positive_degree_bound R hne hdisj S hS i j hij hi hj
        («Σ».selectedPullback R a) (bound : ℝ) c 0 hc hB ∅ (by simp) u
      have hdeg' : (bound : ℝ) - 2 * c + c * (S.negative.card : ℝ) - u i - u j ≤
          S.degree F := by
        simpa only [F, zero_mul, sub_zero, add_zero] using hdeg
      exact hnum.trans hdeg'
    · have hother : ∀ j, j ≠ i → «Σ».selectedRay R j ∉ S.positive := by
        intro j hji hj
        exact hexj ⟨j, hji, hj⟩
      have hdeg := «Σ».selected_one_positive_degree_bound R hR hne hdisj S hS i hi hother
        («Σ».selectedPullback R a) (bound : ℝ) c 0 hc le_rfl hB ∅ (by simp) u
      have hdeg' : (bound : ℝ) - c * ((«Σ».selectedBaseDimension R i : ℝ) + 2) - u i ≤
          S.degree F := by
        simpa only [F, zero_mul, sub_zero] using hdeg
      exact (hone i).trans hdeg'
  · have hnone : ∀ i, «Σ».selectedRay R i ∉ S.positive := by
      simpa only [not_exists] using hex
    rw [← hF]
    exact «Σ».selected_no_positive_degree_nonneg R hR hne hdisj
      (fun v => a v - c) t ht hrepair hinactive S hS hnone

end SmoothCompleteFan

end PaperVerification.ToricGeometry
end
end Source_ToricSelectedCenterCriterion
-- END ORIGINAL PaperVerification.ToricSelectedCenterCriterion


-- BEGIN ORIGINAL PaperVerification.ToricCentersNef
section Source_ToricCentersNef

-- original header: module

-- original header: public import PaperVerification.ToricSelectedCenterCriterion

-- original header: @[expose] public section

/-!
# Nefness of the parity and adjoint centers

All three center support functions have their literal coefficients on the
constructed selected fan. The input edge bounds concern actual lattice
edges of the original polytope. Inactive-class bounds and displacement
inequalities are the explicit scalar data supplied by the finite
obstruction selection and the integer ceiling construction.
-/

noncomputable section

namespace PaperVerification.ToricGeometry

open scoped BigOperators Classical

namespace SmoothCompleteFan

variable {n : ℕ} («Σ» : SmoothCompleteFan n)
variable {ι : Type*} [Fintype ι] (R : ι → «Σ».PrimitiveRelation)
variable (hR : ∀ i, (R i).IsCombinatoriallyContractible)
variable (hne : ∀ i, (R i).negative.Nonempty)
variable (hdisj : «Σ».PairwiseDisjointFoci (fun i => (R i).negative))

include hR in
/-- The real center divisor of Section 6.2 is nef on the actual common
subdivision. The selected family may be the union of both factors' full
obstruction families. -/
theorem parity_center_isNef
    (hpure : «Σ».IsPure) (P : LatticePolytope n) (hP : P.Smooth)
    (hfan : «Σ».realCones = P.normalFan) (hbound : P.EdgesAtLeast n)
    (t : ι → ℝ)
    (htlower : ∀ i, ((R i).negative.card : ℝ) - 1 ≤ t i)
    (htupper : ∀ i, t i ≤ (R i).fiberDimension + (R i).negative.card - 2)
    (hinactive : ∀ Q : «Σ».PrimitiveRelation, Q.IsCombinatoriallyContractible →
      (∀ i, Q.positive ≠ (R i).positive) →
      2 * (Q.fiberDimension : ℝ) ≤ Q.degree (fun v => (P.integralSupport v : ℝ))) :
    («Σ».selectedFan R hne hdisj).IsNef
      (fun v => «Σ».selectedPullback R (fun w => (P.integralSupport w : ℝ)) v - 1 -
        ∑ i, if v = «Σ».selectedRay R i then t i else 0) := by
  apply «Σ».selected_center_isNef_of_scalar_bounds R hR hne hdisj
    hpure P hP hfan hbound 1 zero_le_one t
  · intro i
    simpa only [one_mul] using sub_nonneg.mpr (htlower i)
  · intro i
    rw [(R i).degree_constant_subtraction]
    have hd := P.contractible_degree_lower_bound hP «Σ» hpure hfan hbound (R i) (hR i)
    have hdim := (R i).contractible_dimension_bound (hR i)
    have hq : 1 ≤ (R i).negative.card := Finset.card_pos.mpr (hne i)
    have hs : (R i).fiberDimension + 1 ≤ n := by omega
    have hsR : (R i).fiberDimension + (1 : ℝ) ≤ n := by exact_mod_cast hs
    have hC := (R i).negativeCoefficientSum_nonneg
    have ht := htlower i
    have hm : (0 : ℝ) ≤ (R i).minimumCoefficient (hne i) := Nat.cast_nonneg _
    simp only [one_mul]
    nlinarith [mul_nonneg hm (sub_nonneg.mpr ht)]
  · intro Q hQ hpos hother
    rw [Q.degree_constant_subtraction]
    have hd := hinactive Q hQ hother
    have hr : (1 : ℝ) ≤ Q.fiberDimension := by exact_mod_cast Q.fiberDimension_pos
    have hC := Q.negativeCoefficientSum_nonneg
    linarith
  · intro i
    have hdim : (n : ℝ) = (R i).fiberDimension + (R i).negative.card +
        «Σ».selectedBaseDimension R i := by exact_mod_cast «Σ».selected_dimension_eq R hR i
    have ht := htupper i
    linarith
  · intro i j hij
    have hdi : (n : ℝ) = (R i).fiberDimension + (R i).negative.card +
        «Σ».selectedBaseDimension R i := by exact_mod_cast «Σ».selected_dimension_eq R hR i
    have hdj : (n : ℝ) = (R j).fiberDimension + (R j).negative.card +
        «Σ».selectedBaseDimension R j := by exact_mod_cast «Σ».selected_dimension_eq R hR j
    have hti := htupper i
    have htj := htupper j
    linarith

include hR in
/-- The first unit-box center in Section 7.4. -/
theorem first_adjoint_center_isNef
    (hpure : «Σ».IsPure) (P : LatticePolytope n) (hP : P.Smooth)
    (hfan : «Σ».realCones = P.normalFan) (hbound : P.EdgesAtLeast (n + 1))
    (hlarge : ∀ i, n < 2 * (R i).fiberDimension) :
    («Σ».selectedFan R hne hdisj).IsNef
      (fun v => «Σ».selectedPullback R (fun w => (P.integralSupport w : ℝ)) v - 1 / 2 -
        ∑ i, if v = «Σ».selectedRay R i then ((R i).negative.card : ℝ) - 1 else 0) := by
  apply «Σ».selected_center_isNef_of_scalar_bounds R hR hne hdisj
    hpure P hP hfan hbound (1 / 2) (by norm_num)
    (fun i => ((R i).negative.card : ℝ) - 1)
  · intro i
    have hq : (1 : ℝ) ≤ (R i).negative.card := by
      exact_mod_cast Finset.card_pos.mpr (hne i)
    linarith
  · intro i
    rw [(R i).degree_constant_subtraction]
    have hd := P.contractible_degree_lower_bound hP «Σ» hpure hfan hbound (R i) (hR i)
    have hcard := ((«Σ».primitiveCollection_card_bounds (R i).primitive).2)
    rw [(R i).positive_card_eq_fiberDimension_add_one] at hcard
    have hr : (R i).fiberDimension ≤ n := by omega
    have hrR : ((R i).fiberDimension : ℝ) ≤ n := by exact_mod_cast hr
    have hq : (1 : ℝ) ≤ (R i).negative.card := by
      exact_mod_cast Finset.card_pos.mpr (hne i)
    have hC := (R i).negativeCoefficientSum_nonneg
    have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg _
    have hm : (0 : ℝ) ≤ (R i).minimumCoefficient (hne i) := Nat.cast_nonneg _
    norm_num only [Nat.cast_add, Nat.cast_one] at hd
    nlinarith [mul_nonneg hm (sub_nonneg.mpr hq)]
  · intro Q hQ hpos hother
    rw [Q.degree_constant_subtraction]
    have hd := P.contractible_degree_lower_bound hP «Σ» hpure hfan hbound Q hQ
    have hcard := («Σ».primitiveCollection_card_bounds Q.primitive).2
    rw [Q.positive_card_eq_fiberDimension_add_one] at hcard
    have hr : Q.fiberDimension ≤ n := by omega
    have hrR : (Q.fiberDimension : ℝ) ≤ n := by exact_mod_cast hr
    have hC := Q.negativeCoefficientSum_nonneg
    have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg _
    norm_num only [Nat.cast_add, Nat.cast_one] at hd
    linarith
  · intro i
    have hdim : (n : ℝ) = (R i).fiberDimension + (R i).negative.card +
        «Σ».selectedBaseDimension R i := by exact_mod_cast «Σ».selected_dimension_eq R hR i
    have hr : (0 : ℝ) ≤ (R i).fiberDimension := Nat.cast_nonneg _
    have hb : (0 : ℝ) ≤ «Σ».selectedBaseDimension R i := Nat.cast_nonneg _
    norm_num only [Nat.cast_add, Nat.cast_one]
    linarith
  · intro i j hij
    have hdi : (n : ℝ) = (R i).fiberDimension + (R i).negative.card +
        «Σ».selectedBaseDimension R i := by exact_mod_cast «Σ».selected_dimension_eq R hR i
    have hdj : (n : ℝ) = (R j).fiberDimension + (R j).negative.card +
        «Σ».selectedBaseDimension R j := by exact_mod_cast «Σ».selected_dimension_eq R hR j
    have hli : (n : ℝ) < 2 * (R i).fiberDimension := by exact_mod_cast hlarge i
    have hlj : (n : ℝ) < 2 * (R j).fiberDimension := by exact_mod_cast hlarge j
    have hbi : (0 : ℝ) ≤ «Σ».selectedBaseDimension R i := Nat.cast_nonneg _
    have hbj : (0 : ℝ) ≤ «Σ».selectedBaseDimension R j := Nat.cast_nonneg _
    have hqi : (0 : ℝ) ≤ (R i).negative.card := Nat.cast_nonneg _
    have hqj : (0 : ℝ) ≤ (R j).negative.card := Nat.cast_nonneg _
    norm_num only [Nat.cast_add, Nat.cast_one]
    linarith

include hR in
/-- The second, inner unit-box center in Section 7.4.  The repair is the
actual fiber inequality of the chosen displacement, with the minimum
coefficient taken from the genuine primitive relation. -/
theorem second_adjoint_center_isNef
    (hpure : «Σ».IsPure) (P : LatticePolytope n) (hP : P.Smooth)
    (hfan : «Σ».realCones = P.normalFan) (hbound : P.EdgesAtLeast (n + 1))
    (t : ι → ℝ)
    (htlower : ∀ i, 2 * (((R i).negative.card : ℝ) - 1) ≤ t i)
    (htupper : ∀ i, t i ≤ (n : ℝ) - 2 * «Σ».selectedBaseDimension R i - 2)
    (hfiber : ∀ i, 2 * ((R i).fiberDimension : ℝ) + 1 ≤
      (R i).degree (fun v => (P.integralSupport v : ℝ)) +
      (R i).negativeCoefficientSum + ((R i).minimumCoefficient (hne i) : ℝ) *
        (t i + 1 - (R i).negative.card))
    (hinactive : ∀ Q : «Σ».PrimitiveRelation, Q.IsCombinatoriallyContractible →
      (∀ i, Q.positive ≠ (R i).positive) →
      2 * (Q.fiberDimension : ℝ) + 1 ≤
        Q.degree (fun v => (P.integralSupport v : ℝ)) + Q.negativeCoefficientSum) :
    («Σ».selectedFan R hne hdisj).IsNef
      (fun v => «Σ».selectedPullback R (fun w => (P.integralSupport w : ℝ)) v - 3 / 2 -
        ∑ i, if v = «Σ».selectedRay R i then t i else 0) := by
  apply «Σ».selected_center_isNef_of_scalar_bounds R hR hne hdisj
    hpure P hP hfan hbound (3 / 2) (by norm_num) t
  · intro i
    have hq : (1 : ℝ) ≤ (R i).negative.card := by
      exact_mod_cast Finset.card_pos.mpr (hne i)
    have ht := htlower i
    linarith
  · intro i
    rw [(R i).degree_constant_subtraction]
    have hfix := hfiber i
    have hmcard := (R i).minimumCoefficient_mul_card_le_sum (hne i)
    have hr : (1 : ℝ) ≤ (R i).fiberDimension := by exact_mod_cast (R i).fiberDimension_pos
    have hm : (0 : ℝ) ≤ (R i).minimumCoefficient (hne i) := Nat.cast_nonneg _
    nlinarith
  · intro Q hQ hpos hother
    rw [Q.degree_constant_subtraction]
    have hd := hinactive Q hQ hother
    have hr : (1 : ℝ) ≤ Q.fiberDimension := by exact_mod_cast Q.fiberDimension_pos
    have hC := Q.negativeCoefficientSum_nonneg
    linarith
  · intro i
    have ht := htupper i
    have hb : (0 : ℝ) ≤ «Σ».selectedBaseDimension R i := Nat.cast_nonneg _
    norm_num only [Nat.cast_add, Nat.cast_one]
    linarith
  · intro i j hij
    have hti := htupper i
    have htj := htupper j
    have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg _
    have hbi : (0 : ℝ) ≤ «Σ».selectedBaseDimension R i := Nat.cast_nonneg _
    have hbj : (0 : ℝ) ≤ «Σ».selectedBaseDimension R j := Nat.cast_nonneg _
    norm_num only [Nat.cast_add, Nat.cast_one]
    linarith

end SmoothCompleteFan

end PaperVerification.ToricGeometry
end
end Source_ToricCentersNef
-- END ORIGINAL PaperVerification.ToricCentersNef


-- BEGIN ORIGINAL PaperVerification.ToricObstructionSelection
section Source_ToricObstructionSelection

-- original header: module

-- original header: public import PaperVerification.ToricPrimitiveFinite
-- original header: public import PaperVerification.ToricLargeLoci
-- original header: public import PaperVerification.ToricSimultaneousStars
-- original header: public import PaperVerification.ToricContractibleEdgeDegrees

-- original header: @[expose] public section

/-!
# The complete finite collection of obstructing contractible classes

The index set is cut out from all primitive collections of the actual fan.
No coefficient bound or extremality restriction is imposed. Uniqueness of
the primitive relation transfers every unrestricted contractible class to
this finite collection. Large-fiber disjointness and the fiber-type
alternative are consequences of the actual degree bounds.
-/

noncomputable section

namespace PaperVerification.ToricGeometry

open scoped BigOperators Classical

namespace SmoothCompleteFan.PrimitiveRelation

variable {n : ℕ} {«Σ» : SmoothCompleteFan n} (R S : «Σ».PrimitiveRelation)

theorem contractible_iff_of_positive_eq (hpos : R.positive = S.positive) :
    R.IsCombinatoriallyContractible ↔ S.IsCombinatoriallyContractible := by
  have hneg := R.negative_unique S hpos
  simp only [IsCombinatoriallyContractible, hpos, hneg]

theorem fiberDimension_eq_of_positive_eq (hpos : R.positive = S.positive) :
    R.fiberDimension = S.fiberDimension := by simp only [fiberDimension, hpos]

/-- The integer-valued degree of an integral support function. -/
def integerDegree (a : Lattice n → ℤ) : ℤ :=
  (∑ v ∈ R.positive, a v) - ∑ v ∈ R.negative, (R.coefficient v : ℤ) * a v

theorem integerDegree_cast (a : Lattice n → ℤ) :
    (R.integerDegree a : ℝ) = R.degree (fun v => (a v : ℝ)) := by
  simp only [integerDegree, degree, Int.cast_sub, Int.cast_sum, Int.cast_mul,
    Int.cast_natCast]

def coefficientSum : ℕ := ∑ v ∈ R.negative, R.coefficient v

theorem negative_card_le_coefficientSum : R.negative.card ≤ R.coefficientSum := by
  calc
    R.negative.card = ∑ _ ∈ R.negative, 1 := by simp
    _ ≤ R.coefficientSum := Finset.sum_le_sum (fun v hv => R.coefficient_pos v hv)

theorem coefficientSum_eq_of_positive_eq (hpos : R.positive = S.positive) :
    R.coefficientSum = S.coefficientSum := by
  have hneg := R.negative_unique S hpos
  unfold coefficientSum
  calc
    (∑ v ∈ R.negative, R.coefficient v) = ∑ v ∈ R.negative, S.coefficient v :=
      Finset.sum_congr rfl (fun v hv => R.coefficient_unique_on_negative S hpos hv)
    _ = _ := by rw [hneg]

end SmoothCompleteFan.PrimitiveRelation

namespace SmoothCompleteFan

variable {n : ℕ} («Σ» : SmoothCompleteFan n)

/-- Finite selection from every primitive collection of the actual fan. -/
def selectedPrimitiveCollections (test : «Σ».PrimitiveRelation → Prop) :
    Finset «Σ».primitiveCollections :=
  Finset.univ.filter (fun Q => («Σ».canonicalPrimitive Q).IsCombinatoriallyContractible ∧
    test («Σ».canonicalPrimitive Q))

def selectionRelation (test : «Σ».PrimitiveRelation → Prop)
    (i : «Σ».selectedPrimitiveCollections test) : «Σ».PrimitiveRelation :=
  «Σ».canonicalPrimitive i

theorem selectionRelation_contractible (test : «Σ».PrimitiveRelation → Prop)
    (i : «Σ».selectedPrimitiveCollections test) :
    («Σ».selectionRelation test i).IsCombinatoriallyContractible :=
  (Finset.mem_filter.mp i.property).2.1

theorem selectionRelation_test (test : «Σ».PrimitiveRelation → Prop)
    (i : «Σ».selectedPrimitiveCollections test) : test («Σ».selectionRelation test i) :=
  (Finset.mem_filter.mp i.property).2.2

theorem selectionRelation_positive_injective (test : «Σ».PrimitiveRelation → Prop) :
    Function.Injective (fun i : «Σ».selectedPrimitiveCollections test =>
      («Σ».selectionRelation test i).positive) := by
  intro i j hij
  apply Subtype.ext
  apply Subtype.ext
  simpa only [selectionRelation, «Σ».canonicalPrimitive_positive] using hij

/-- Exact exhaustiveness up to the proved primitive-class equality. -/
theorem selectionRelation_exhaustive
    (test : «Σ».PrimitiveRelation → Prop)
    (hcongr : ∀ R S : «Σ».PrimitiveRelation, R.positive = S.positive → (test R ↔ test S))
    (R : «Σ».PrimitiveRelation) :
    (∃ i : «Σ».selectedPrimitiveCollections test,
      R.positive = («Σ».selectionRelation test i).positive) ↔
      R.IsCombinatoriallyContractible ∧ test R := by
  constructor
  · rintro ⟨i, hi⟩
    exact ⟨(R.contractible_iff_of_positive_eq _ hi).mpr
      («Σ».selectionRelation_contractible test i),
      (hcongr R _ hi).mpr («Σ».selectionRelation_test test i)⟩
  · rintro ⟨hR, htest⟩
    let Q : «Σ».primitiveCollections :=
      ⟨R.positive, («Σ».mem_primitiveCollections R.positive).mpr R.primitive⟩
    have hpos : R.positive = («Σ».canonicalPrimitive Q).positive :=
      («Σ».canonicalPrimitive_positive Q).symm
    have hQ : Q ∈ «Σ».selectedPrimitiveCollections test := by
      apply Finset.mem_filter.mpr
      exact ⟨Finset.mem_univ Q, (R.contractible_iff_of_positive_eq _ hpos).mp hR,
        (hcongr R _ hpos).mp htest⟩
    exact ⟨⟨Q, hQ⟩, hpos⟩

/-- Pairwise disjointness is derived for the complete selected family. -/
theorem selectionRelation_disjoint_of_large (hpure : «Σ».IsPure)
    (test : «Σ».PrimitiveRelation → Prop)
    (hlarge : ∀ i : «Σ».selectedPrimitiveCollections test,
      n < 2 * («Σ».selectionRelation test i).fiberDimension) :
    «Σ».PairwiseDisjointFoci (fun i => («Σ».selectionRelation test i).negative) := by
  intro i j hij
  apply «Σ».no_common_cone_of_two_large_relations hpure
    («Σ».selectionRelation test i) («Σ».selectionRelation test j)
    («Σ».selectionRelation_contractible test i) («Σ».selectionRelation_contractible test j)
    (hlarge i) (hlarge j)
  exact fun h => hij («Σ».selectionRelation_positive_injective test h)

/-- A selected fiber-type class is the only selected class. Otherwise all
selected focus cones are nonempty, exactly as needed by the common blowup. -/
theorem selectionRelation_focus_cases (test : «Σ».PrimitiveRelation → Prop)
    (hdisj : «Σ».PairwiseDisjointFoci (fun i => («Σ».selectionRelation test i).negative)) :
    (∃ i : «Σ».selectedPrimitiveCollections test,
      («Σ».selectionRelation test i).negative = ∅ ∧ ∀ j, j = i) ∨
      (∀ i : «Σ».selectedPrimitiveCollections test,
        («Σ».selectionRelation test i).negative.Nonempty) := by
  by_cases hex : ∃ i : «Σ».selectedPrimitiveCollections test,
      («Σ».selectionRelation test i).negative = ∅
  · obtain ⟨i, hi⟩ := hex
    left
    refine ⟨i, hi, ?_⟩
    intro j
    by_contra hji
    apply hdisj i j (Ne.symm hji)
    refine ⟨(«Σ».selectionRelation test j).negative,
      («Σ».selectionRelation test j).negative_cone, ?_⟩
    change («Σ».selectionRelation test i).negative ∪
      («Σ».selectionRelation test j).negative ⊆ («Σ».selectionRelation test j).negative
    intro v hv
    simpa only [hi, Finset.empty_union] using hv
  · right
    intro i
    exact Finset.nonempty_iff_ne_empty.mpr (fun hi => hex ⟨i, hi⟩)

/-- Failure of either of the two side-two corner thresholds. -/
def parityObstruction (a b : Lattice n → ℝ) (R : «Σ».PrimitiveRelation) : Prop :=
  R.degree a < 2 * (R.fiberDimension : ℝ) ∨
    R.degree b < 2 * (R.fiberDimension : ℝ)

theorem parityObstruction_congr (a b : Lattice n → ℝ)
    (R S : «Σ».PrimitiveRelation) (hpos : R.positive = S.positive) :
    «Σ».parityObstruction a b R ↔ «Σ».parityObstruction a b S := by
  simp only [parityObstruction, R.degree_unique S hpos a, R.degree_unique S hpos b,
    R.fiberDimension_eq_of_positive_eq S hpos]

abbrev paritySelection (a b : Lattice n → ℝ) :=
  «Σ».selectedPrimitiveCollections («Σ».parityObstruction a b)

def paritySelectedRelation (a b : Lattice n → ℝ) (i : «Σ».paritySelection a b) :
    «Σ».PrimitiveRelation := «Σ».selectionRelation («Σ».parityObstruction a b) i

theorem parity_selection_exhaustive (a b : Lattice n → ℝ) (R : «Σ».PrimitiveRelation) :
    (∃ i : «Σ».paritySelection a b, R.positive = («Σ».paritySelectedRelation a b i).positive) ↔
      R.IsCombinatoriallyContractible ∧
        (R.degree a < 2 * (R.fiberDimension : ℝ) ∨
          R.degree b < 2 * (R.fiberDimension : ℝ)) :=
  «Σ».selectionRelation_exhaustive _ («Σ».parityObstruction_congr a b) R

theorem parity_selection_large (a b : Lattice n → ℝ)
    (ha : ∀ R : «Σ».PrimitiveRelation, R.IsCombinatoriallyContractible → (n : ℝ) ≤ R.degree a)
    (hb : ∀ R : «Σ».PrimitiveRelation, R.IsCombinatoriallyContractible → (n : ℝ) ≤ R.degree b)
    (i : «Σ».paritySelection a b) : n < 2 * («Σ».paritySelectedRelation a b i).fiberDimension := by
  let R := «Σ».paritySelectedRelation a b i
  have hR := «Σ».selectionRelation_contractible («Σ».parityObstruction a b) i
  have htest := «Σ».selectionRelation_test («Σ».parityObstruction a b) i
  have hh : (n : ℝ) < 2 * (R.fiberDimension : ℝ) := by
    rcases htest with h | h
    · exact (ha R hR).trans_lt h
    · exact (hb R hR).trans_lt h
  exact_mod_cast hh

theorem parity_selection_disjoint (hpure : «Σ».IsPure) (a b : Lattice n → ℝ)
    (ha : ∀ R : «Σ».PrimitiveRelation, R.IsCombinatoriallyContractible → (n : ℝ) ≤ R.degree a)
    (hb : ∀ R : «Σ».PrimitiveRelation, R.IsCombinatoriallyContractible → (n : ℝ) ≤ R.degree b) :
    «Σ».PairwiseDisjointFoci (fun i : «Σ».paritySelection a b =>
      («Σ».paritySelectedRelation a b i).negative) :=
  «Σ».selectionRelation_disjoint_of_large hpure _ («Σ».parity_selection_large a b ha hb)

theorem parity_unselected_degree_bounds (a b : Lattice n → ℝ)
    (R : «Σ».PrimitiveRelation) (hR : R.IsCombinatoriallyContractible)
    (hn : ∀ i : «Σ».paritySelection a b,
      R.positive ≠ («Σ».paritySelectedRelation a b i).positive) :
    2 * (R.fiberDimension : ℝ) ≤ R.degree a ∧
      2 * (R.fiberDimension : ℝ) ≤ R.degree b := by
  have ht : ¬ (R.degree a < 2 * (R.fiberDimension : ℝ) ∨
      R.degree b < 2 * (R.fiberDimension : ℝ)) := by
    intro hh
    obtain ⟨i, hi⟩ := («Σ».parity_selection_exhaustive a b R).mpr ⟨hR, hh⟩
    exact hn i hi
  simpa only [not_or, not_lt] using ht

/-- The exact adjoint obstruction in equation (12). -/
def adjointObstruction (b : Lattice n → ℝ) (R : «Σ».PrimitiveRelation) : Prop :=
  0 < 2 * (R.fiberDimension : ℝ) + 1 - R.degree b - R.coefficientSum

theorem adjointObstruction_congr (b : Lattice n → ℝ)
    (R S : «Σ».PrimitiveRelation) (hpos : R.positive = S.positive) :
    «Σ».adjointObstruction b R ↔ «Σ».adjointObstruction b S := by
  simp only [adjointObstruction, R.degree_unique S hpos b,
    R.fiberDimension_eq_of_positive_eq S hpos, R.coefficientSum_eq_of_positive_eq S hpos]

abbrev adjointSelection (b : Lattice n → ℝ) :=
  «Σ».selectedPrimitiveCollections («Σ».adjointObstruction b)

def adjointSelectedRelation (b : Lattice n → ℝ) (i : «Σ».adjointSelection b) :
    «Σ».PrimitiveRelation := «Σ».selectionRelation («Σ».adjointObstruction b) i

theorem adjoint_selection_exhaustive (b : Lattice n → ℝ) (R : «Σ».PrimitiveRelation) :
    (∃ i : «Σ».adjointSelection b, R.positive = («Σ».adjointSelectedRelation b i).positive) ↔
      R.IsCombinatoriallyContractible ∧
        0 < 2 * (R.fiberDimension : ℝ) + 1 - R.degree b - R.coefficientSum :=
  «Σ».selectionRelation_exhaustive _ («Σ».adjointObstruction_congr b) R

theorem adjoint_selection_large (b : Lattice n → ℝ)
    (hb : ∀ R : «Σ».PrimitiveRelation, R.IsCombinatoriallyContractible →
      (n : ℝ) + 1 ≤ R.degree b)
    (i : «Σ».adjointSelection b) : n < 2 * («Σ».adjointSelectedRelation b i).fiberDimension := by
  let R := «Σ».adjointSelectedRelation b i
  have hR := «Σ».selectionRelation_contractible («Σ».adjointObstruction b) i
  have htest := «Σ».selectionRelation_test («Σ».adjointObstruction b) i
  have hdegree := hb R hR
  have hcoeff : (0 : ℝ) ≤ R.coefficientSum := Nat.cast_nonneg _
  have hh : (n : ℝ) < 2 * (R.fiberDimension : ℝ) := by
    change 0 < 2 * (R.fiberDimension : ℝ) + 1 - R.degree b - R.coefficientSum at htest
    linarith
  exact_mod_cast hh

theorem adjoint_selection_disjoint (hpure : «Σ».IsPure) (b : Lattice n → ℝ)
    (hb : ∀ R : «Σ».PrimitiveRelation, R.IsCombinatoriallyContractible →
      (n : ℝ) + 1 ≤ R.degree b) :
    «Σ».PairwiseDisjointFoci (fun i : «Σ».adjointSelection b =>
      («Σ».adjointSelectedRelation b i).negative) :=
  «Σ».selectionRelation_disjoint_of_large hpure _ («Σ».adjoint_selection_large b hb)

theorem adjoint_unselected_degree_bound (b : Lattice n → ℝ)
    (R : «Σ».PrimitiveRelation) (hR : R.IsCombinatoriallyContractible)
    (hn : ∀ i : «Σ».adjointSelection b,
      R.positive ≠ («Σ».adjointSelectedRelation b i).positive) :
    2 * (R.fiberDimension : ℝ) + 1 ≤ R.degree b + R.coefficientSum := by
  by_contra hh
  have htest : 0 < 2 * (R.fiberDimension : ℝ) + 1 - R.degree b - R.coefficientSum := by
    linarith
  obtain ⟨i, hi⟩ := («Σ».adjoint_selection_exhaustive b R).mpr ⟨hR, htest⟩
  exact hn i hi

end SmoothCompleteFan

end PaperVerification.ToricGeometry
end
end Source_ToricObstructionSelection
-- END ORIGINAL PaperVerification.ToricObstructionSelection


-- BEGIN ORIGINAL PaperVerification.ToricCanonicalCorrections
section Source_ToricCanonicalCorrections

-- original header: module

-- original header: public import PaperVerification.ToricObstructionSelection
-- original header: public import PaperVerification.ToricCentersNef

-- original header: @[expose] public section

/-!
# Exact integer displacements from the actual primitive degrees

The ceiling corrections are evaluated on the genuine integral support
degree and the least actual negative coefficient. Their normal-height,
base-dimension, and fiber-repair bounds follow from the original literal
edge hypotheses.
-/

noncomputable section

namespace PaperVerification.ToricGeometry

open scoped BigOperators Classical

namespace SmoothCompleteFan.PrimitiveRelation

variable {n : ℕ} {«Σ» : SmoothCompleteFan n} (R : «Σ».PrimitiveRelation)

theorem coefficientSum_cast : (R.coefficientSum : ℝ) = R.negativeCoefficientSum := by
  simp only [coefficientSum, negativeCoefficientSum, Nat.cast_sum]

def baseDimension : ℕ := n - R.fiberDimension - R.negative.card

theorem dimension_eq (hR : R.IsCombinatoriallyContractible) :
    n = R.fiberDimension + R.negative.card + R.baseDimension := by
  have h := R.contractible_dimension_bound hR
  unfold baseDimension
  omega

def parityDisplacement (hne : R.negative.Nonempty) (a : Lattice n → ℤ) : ℤ :=
  parityCorrection R.fiberDimension R.negative.card (R.integerDegree a)
    (R.minimumCoefficient hne)

def adjointDisplacement (hne : R.negative.Nonempty) (a : Lattice n → ℤ) : ℤ :=
  adjointCorrection R.fiberDimension R.negative.card (R.integerDegree a)
    R.coefficientSum (R.minimumCoefficient hne)

/-- Every scalar bound for the exact parity displacement, with its degree
and minimum coefficient derived from the original polytope. -/
theorem parityDisplacement_bounds
    (hR : R.IsCombinatoriallyContractible) (hne : R.negative.Nonempty)
    (hlarge : n < 2 * R.fiberDimension)
    (hpure : «Σ».IsPure) (P : LatticePolytope n) (hP : P.Smooth)
    (hfan : «Σ».realCones = P.normalFan) (hbound : P.EdgesAtLeast n) :
    0 ≤ (R.parityDisplacement hne P.integralSupport : ℝ) ∧
      2 * ((R.negative.card : ℝ) - 1) ≤ R.parityDisplacement hne P.integralSupport ∧
      (R.parityDisplacement hne P.integralSupport : ℝ) ≤
        (n : ℝ) - 2 * R.baseDimension - 2 ∧
      (R.parityDisplacement hne P.integralSupport : ℝ) ≤
        (R.fiberDimension : ℝ) + R.negative.card - 2 ∧
      2 * (R.fiberDimension : ℝ) ≤ R.degree (fun u => (P.integralSupport u : ℝ)) +
        (R.minimumCoefficient hne : ℝ) * R.parityDisplacement hne P.integralSupport := by
  have hq : (1 : ℤ) ≤ R.negative.card := by exact_mod_cast Finset.card_pos.mpr hne
  have hb : (0 : ℤ) ≤ R.baseDimension := Int.natCast_nonneg _
  have hm : (1 : ℤ) ≤ R.minimumCoefficient hne := by
    exact_mod_cast (R.minimumCoefficient_spec hne).1
  have hdim : (n : ℤ) = R.fiberDimension + R.negative.card + R.baseDimension := by
    exact_mod_cast R.dimension_eq hR
  have hl : (n : ℤ) < 2 * (R.fiberDimension : ℤ) := by exact_mod_cast hlarge
  have hdR := P.contractible_degree_lower_bound hP «Σ» hpure hfan hbound R hR
  rw [← R.integerDegree_cast] at hdR
  have hd : (n : ℤ) ≤ R.integerDegree P.integralSupport := by exact_mod_cast hdR
  obtain ⟨h0, hlow, hup, hup', hrepair⟩ := parityCorrection_bounds
    n R.fiberDimension R.negative.card R.baseDimension
    (R.integerDegree P.integralSupport) (R.minimumCoefficient hne)
    hq hb hm hdim hl hd
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact_mod_cast h0
  · exact_mod_cast hlow
  · exact_mod_cast hup
  · exact_mod_cast hup'
  · rw [← R.integerDegree_cast]
    exact_mod_cast hrepair

/-- The exact adjoint correction, including its literal inner fiber-degree
repair and the complete normal-height budget. -/
theorem adjointDisplacement_bounds
    (hR : R.IsCombinatoriallyContractible) (hne : R.negative.Nonempty)
    (hpure : «Σ».IsPure) (P : LatticePolytope n) (hP : P.Smooth)
    (hfan : «Σ».realCones = P.normalFan) (hbound : P.EdgesAtLeast (n + 1))
    (hselected : «Σ».adjointObstruction (fun u => (P.integralSupport u : ℝ)) R) :
    n < 2 * R.fiberDimension ∧
      2 * ((R.negative.card : ℝ) - 1) ≤ R.adjointDisplacement hne P.integralSupport ∧
      (R.adjointDisplacement hne P.integralSupport : ℝ) ≤
        (n : ℝ) - 2 * R.baseDimension - 2 ∧
      2 * (R.fiberDimension : ℝ) + 1 ≤ R.degree (fun u => (P.integralSupport u : ℝ)) +
        R.negativeCoefficientSum + (R.minimumCoefficient hne : ℝ) *
          ((R.adjointDisplacement hne P.integralSupport : ℝ) + 1 - R.negative.card) := by
  have hq : (1 : ℤ) ≤ R.negative.card := by exact_mod_cast Finset.card_pos.mpr hne
  have hb : (0 : ℤ) ≤ R.baseDimension := Int.natCast_nonneg _
  have hm : (1 : ℤ) ≤ R.minimumCoefficient hne := by
    exact_mod_cast (R.minimumCoefficient_spec hne).1
  have hdim : (n : ℤ) = R.fiberDimension + R.negative.card + R.baseDimension := by
    exact_mod_cast R.dimension_eq hR
  have hdR := P.contractible_degree_lower_bound hP «Σ» hpure hfan hbound R hR
  rw [← R.integerDegree_cast] at hdR
  have hd : (n : ℤ) + 1 ≤ R.integerDegree P.integralSupport := by exact_mod_cast hdR
  have hcoeff : (R.negative.card : ℤ) ≤ R.coefficientSum := by
    exact_mod_cast R.negative_card_le_coefficientSum
  have hsel : (0 : ℤ) < 2 * (R.fiberDimension : ℤ) + 1 -
      R.integerDegree P.integralSupport - R.coefficientSum := by
    change 0 < 2 * (R.fiberDimension : ℝ) + 1 -
      R.degree (fun u => (P.integralSupport u : ℝ)) - R.coefficientSum at hselected
    rw [← R.integerDegree_cast] at hselected
    exact_mod_cast hselected
  obtain ⟨hlarge, hlow, hup, hrepair⟩ := adjointCorrection_bounds
    n R.fiberDimension R.negative.card R.baseDimension
    (R.integerDegree P.integralSupport) R.coefficientSum (R.minimumCoefficient hne)
    hq hb hm hdim hd hcoeff hsel
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact_mod_cast hlarge
  · exact_mod_cast hlow
  · exact_mod_cast hup
  · rw [← R.integerDegree_cast, ← R.coefficientSum_cast]
    exact_mod_cast hrepair

end SmoothCompleteFan.PrimitiveRelation

namespace SmoothCompleteFan

variable {n : ℕ} («Σ» : SmoothCompleteFan n)

theorem parity_selection_disjoint_of_edges (hpure : «Σ».IsPure)
    (P Q : LatticePolytope n) (hP : P.Smooth) (hQ : Q.Smooth)
    (hfanP : «Σ».realCones = P.normalFan) (hfanQ : «Σ».realCones = Q.normalFan)
    (hboundP : P.EdgesAtLeast n) (hboundQ : Q.EdgesAtLeast n) :
    «Σ».PairwiseDisjointFoci (fun i : «Σ».paritySelection
      (fun u => (P.integralSupport u : ℝ)) (fun u => (Q.integralSupport u : ℝ)) =>
      («Σ».paritySelectedRelation
        (fun u => (P.integralSupport u : ℝ)) (fun u => (Q.integralSupport u : ℝ)) i).negative) :=
  «Σ».parity_selection_disjoint hpure _ _
    (P.contractible_degree_lower_bound hP «Σ» hpure hfanP hboundP)
    (Q.contractible_degree_lower_bound hQ «Σ» hpure hfanQ hboundQ)

theorem adjoint_selection_disjoint_of_edges (hpure : «Σ».IsPure)
    (P : LatticePolytope n) (hP : P.Smooth)
    (hfan : «Σ».realCones = P.normalFan) (hbound : P.EdgesAtLeast (n + 1)) :
    «Σ».PairwiseDisjointFoci (fun i : «Σ».adjointSelection (fun u => (P.integralSupport u : ℝ)) =>
      («Σ».adjointSelectedRelation (fun u => (P.integralSupport u : ℝ)) i).negative) := by
  apply «Σ».adjoint_selection_disjoint hpure
  intro R hR
  simpa only [Nat.cast_add, Nat.cast_one] using
    P.contractible_degree_lower_bound hP «Σ» hpure hfan hbound R hR

end SmoothCompleteFan

end PaperVerification.ToricGeometry
end
end Source_ToricCanonicalCorrections
-- END ORIGINAL PaperVerification.ToricCanonicalCorrections


-- BEGIN ORIGINAL PaperVerification.ToricCanonicalCenters
section Source_ToricCanonicalCenters

-- original header: module

-- original header: public import PaperVerification.ToricCanonicalCorrections

-- original header: @[expose] public section

/-!
# Centers for the exhaustive obstruction families

The families below are determined by the original two integral polytopes.
Every displacement is the exact integer ceiling appearing in the paper.
Nefness is deduced from the original edge hypotheses; no numerical repair
inequality or unselected-class positivity is an additional hypothesis.
The nonempty-focus hypothesis describes the branch complementary to the
fiber-type case and is discharged by `selectionRelation_focus_cases`.
-/

noncomputable section

namespace PaperVerification.ToricGeometry

open scoped BigOperators Classical

namespace SmoothCompleteFan

variable {n : ℕ} («Σ» : SmoothCompleteFan n)

abbrev parityIndices (P Q : LatticePolytope n) :=
  «Σ».paritySelection (fun u => (P.integralSupport u : ℝ))
    (fun u => (Q.integralSupport u : ℝ))

def parityFamily (P Q : LatticePolytope n) (i : «Σ».parityIndices P Q) :
    «Σ».PrimitiveRelation :=
  «Σ».paritySelectedRelation (fun u => (P.integralSupport u : ℝ))
    (fun u => (Q.integralSupport u : ℝ)) i

theorem parityFamily_contractible (P Q : LatticePolytope n)
    (i : «Σ».parityIndices P Q) :
    («Σ».parityFamily P Q i).IsCombinatoriallyContractible :=
  «Σ».selectionRelation_contractible _ i

theorem parityFamily_large (hpure : «Σ».IsPure)
    (P Q : LatticePolytope n) (hP : P.Smooth) (hQ : Q.Smooth)
    (hfanP : «Σ».realCones = P.normalFan) (hfanQ : «Σ».realCones = Q.normalFan)
    (hboundP : P.EdgesAtLeast n) (hboundQ : Q.EdgesAtLeast n)
    (i : «Σ».parityIndices P Q) : n < 2 * («Σ».parityFamily P Q i).fiberDimension :=
  «Σ».parity_selection_large _ _
    (P.contractible_degree_lower_bound hP «Σ» hpure hfanP hboundP)
    (Q.contractible_degree_lower_bound hQ «Σ» hpure hfanQ hboundQ) i

theorem parityFamily_disjoint (hpure : «Σ».IsPure)
    (P Q : LatticePolytope n) (hP : P.Smooth) (hQ : Q.Smooth)
    (hfanP : «Σ».realCones = P.normalFan) (hfanQ : «Σ».realCones = Q.normalFan)
    (hboundP : P.EdgesAtLeast n) (hboundQ : Q.EdgesAtLeast n) :
    «Σ».PairwiseDisjointFoci (fun i => («Σ».parityFamily P Q i).negative) :=
  «Σ».parity_selection_disjoint_of_edges hpure P Q hP hQ hfanP hfanQ hboundP hboundQ

/-- The complete obstruction family either contains an empty focus, or
every focus is nonempty. In the former case the unique selected relation
supplies the bundle branch of the induction. -/
theorem parityFamily_focus_cases (hpure : «Σ».IsPure)
    (P Q : LatticePolytope n) (hP : P.Smooth) (hQ : Q.Smooth)
    (hfanP : «Σ».realCones = P.normalFan) (hfanQ : «Σ».realCones = Q.normalFan)
    (hboundP : P.EdgesAtLeast n) (hboundQ : Q.EdgesAtLeast n) :
    (∃ i : «Σ».parityIndices P Q, («Σ».parityFamily P Q i).negative = ∅) ∨
      (∀ i : «Σ».parityIndices P Q, («Σ».parityFamily P Q i).negative.Nonempty) := by
  rcases «Σ».selectionRelation_focus_cases
      («Σ».parityObstruction (fun u => (P.integralSupport u : ℝ))
        (fun u => (Q.integralSupport u : ℝ)))
      («Σ».parityFamily_disjoint hpure P Q hP hQ hfanP hfanQ hboundP hboundQ) with
    ⟨i, hi, _⟩ | hne
  · exact Or.inl ⟨i, hi⟩
  · exact Or.inr hne

def parityDisplacements (P Q L : LatticePolytope n)
    (hne : ∀ i, («Σ».parityFamily P Q i).negative.Nonempty)
    (i : «Σ».parityIndices P Q) : ℤ :=
  («Σ».parityFamily P Q i).parityDisplacement (hne i) L.integralSupport

def parityCenter (P Q L : LatticePolytope n)
    (hne : ∀ i, («Σ».parityFamily P Q i).negative.Nonempty) : Lattice n → ℝ :=
  fun v => «Σ».selectedPullback («Σ».parityFamily P Q)
    (fun w => (L.integralSupport w : ℝ)) v - 1 -
      ∑ i, if v = «Σ».selectedRay («Σ».parityFamily P Q) i then
        («Σ».parityDisplacements P Q L hne i : ℝ) else 0

/-- Both centers are nef on the same actual selected fan. All selection,
degree, displacement and disjointness data are derived from the two
original smooth polytopes and their literal edge lengths. -/
theorem canonical_parity_centers_isNef (hpure : «Σ».IsPure)
    (P Q : LatticePolytope n) (hP : P.Smooth) (hQ : Q.Smooth)
    (hfanP : «Σ».realCones = P.normalFan) (hfanQ : «Σ».realCones = Q.normalFan)
    (hboundP : P.EdgesAtLeast n) (hboundQ : Q.EdgesAtLeast n)
    (hne : ∀ i, («Σ».parityFamily P Q i).negative.Nonempty) :
    let «Σ'» := «Σ».selectedFan («Σ».parityFamily P Q) hne
      («Σ».parityFamily_disjoint hpure P Q hP hQ hfanP hfanQ hboundP hboundQ)
    «Σ'».IsNef («Σ».parityCenter P Q P hne) ∧
      «Σ'».IsNef («Σ».parityCenter P Q Q hne) := by
  let R := «Σ».parityFamily P Q
  have hR : ∀ i, (R i).IsCombinatoriallyContractible :=
    «Σ».parityFamily_contractible P Q
  have hlarge : ∀ i, n < 2 * (R i).fiberDimension :=
    «Σ».parityFamily_large hpure P Q hP hQ hfanP hfanQ hboundP hboundQ
  have hdisj := «Σ».parityFamily_disjoint hpure P Q hP hQ hfanP hfanQ hboundP hboundQ
  have make_center (L : LatticePolytope n) (hL : L.Smooth)
      (hfanL : «Σ».realCones = L.normalFan) (hboundL : L.EdgesAtLeast n)
      (hinactive : ∀ S : «Σ».PrimitiveRelation, S.IsCombinatoriallyContractible →
        (∀ i, S.positive ≠ (R i).positive) →
        2 * (S.fiberDimension : ℝ) ≤ S.degree (fun u => (L.integralSupport u : ℝ))) :
      («Σ».selectedFan R hne hdisj).IsNef («Σ».parityCenter P Q L hne) := by
    apply «Σ».parity_center_isNef R hR hne hdisj hpure L hL hfanL hboundL
      (fun i => («Σ».parityDisplacements P Q L hne i : ℝ))
    · intro i
      have hb := (R i).parityDisplacement_bounds (hR i) (hne i) (hlarge i)
        hpure L hL hfanL hboundL
      have hq : (1 : ℝ) ≤ (R i).negative.card := by
        exact_mod_cast Finset.card_pos.mpr (hne i)
      change ((R i).negative.card : ℝ) - 1 ≤
        ((R i).parityDisplacement (hne i) L.integralSupport : ℝ)
      linarith [hb.2.1]
    · intro i
      exact ((R i).parityDisplacement_bounds (hR i) (hne i) (hlarge i)
        hpure L hL hfanL hboundL).2.2.2.1
    · exact hinactive
  constructor
  · apply make_center P hP hfanP hboundP
    intro S hS hn
    exact («Σ».parity_unselected_degree_bounds _ _ S hS hn).1
  · apply make_center Q hQ hfanQ hboundQ
    intro S hS hn
    exact («Σ».parity_unselected_degree_bounds _ _ S hS hn).2

abbrev adjointIndices (Q : LatticePolytope n) :=
  «Σ».adjointSelection (fun u => (Q.integralSupport u : ℝ))

def adjointFamily (Q : LatticePolytope n) (i : «Σ».adjointIndices Q) :
    «Σ».PrimitiveRelation :=
  «Σ».adjointSelectedRelation (fun u => (Q.integralSupport u : ℝ)) i

theorem adjointFamily_contractible (Q : LatticePolytope n)
    (i : «Σ».adjointIndices Q) :
    («Σ».adjointFamily Q i).IsCombinatoriallyContractible :=
  «Σ».selectionRelation_contractible _ i

theorem adjointFamily_large (hpure : «Σ».IsPure)
    (Q : LatticePolytope n) (hQ : Q.Smooth)
    (hfanQ : «Σ».realCones = Q.normalFan) (hboundQ : Q.EdgesAtLeast (n + 1))
    (i : «Σ».adjointIndices Q) : n < 2 * («Σ».adjointFamily Q i).fiberDimension := by
  apply «Σ».adjoint_selection_large _ _ i
  intro S hS
  simpa only [Nat.cast_add, Nat.cast_one] using
    Q.contractible_degree_lower_bound hQ «Σ» hpure hfanQ hboundQ S hS

theorem adjointFamily_disjoint (hpure : «Σ».IsPure)
    (Q : LatticePolytope n) (hQ : Q.Smooth)
    (hfanQ : «Σ».realCones = Q.normalFan) (hboundQ : Q.EdgesAtLeast (n + 1)) :
    «Σ».PairwiseDisjointFoci (fun i => («Σ».adjointFamily Q i).negative) :=
  «Σ».adjoint_selection_disjoint_of_edges hpure Q hQ hfanQ hboundQ

theorem adjointFamily_focus_cases (hpure : «Σ».IsPure)
    (Q : LatticePolytope n) (hQ : Q.Smooth)
    (hfanQ : «Σ».realCones = Q.normalFan) (hboundQ : Q.EdgesAtLeast (n + 1)) :
    (∃ i : «Σ».adjointIndices Q, («Σ».adjointFamily Q i).negative = ∅) ∨
      (∀ i : «Σ».adjointIndices Q, («Σ».adjointFamily Q i).negative.Nonempty) := by
  rcases «Σ».selectionRelation_focus_cases
      («Σ».adjointObstruction (fun u => (Q.integralSupport u : ℝ)))
      («Σ».adjointFamily_disjoint hpure Q hQ hfanQ hboundQ) with
    ⟨i, hi, _⟩ | hne
  · exact Or.inl ⟨i, hi⟩
  · exact Or.inr hne

def adjointDisplacements (Q : LatticePolytope n)
    (hne : ∀ i, («Σ».adjointFamily Q i).negative.Nonempty)
    (i : «Σ».adjointIndices Q) : ℤ :=
  («Σ».adjointFamily Q i).adjointDisplacement (hne i) Q.integralSupport

def firstAdjointCenter (P Q : LatticePolytope n) : Lattice n → ℝ :=
  fun v => «Σ».selectedPullback («Σ».adjointFamily Q)
    (fun w => (P.integralSupport w : ℝ)) v - 1 / 2 -
      ∑ i, if v = «Σ».selectedRay («Σ».adjointFamily Q) i then
        ((«Σ».adjointFamily Q i).negative.card : ℝ) - 1 else 0

def secondAdjointCenter (Q : LatticePolytope n)
    (hne : ∀ i, («Σ».adjointFamily Q i).negative.Nonempty) : Lattice n → ℝ :=
  fun v => «Σ».selectedPullback («Σ».adjointFamily Q)
    (fun w => (Q.integralSupport w : ℝ)) v - 3 / 2 -
      ∑ i, if v = «Σ».selectedRay («Σ».adjointFamily Q) i then
        («Σ».adjointDisplacements Q hne i : ℝ) else 0

/-- The two unequal adjoint centers, with the exact original obstruction
test and integer correction. The second center is for boxes lying in the
interior lattice-point polytope of the second factor. -/
theorem canonical_adjoint_centers_isNef (hpure : «Σ».IsPure)
    (P Q : LatticePolytope n) (hP : P.Smooth) (hQ : Q.Smooth)
    (hfanP : «Σ».realCones = P.normalFan) (hfanQ : «Σ».realCones = Q.normalFan)
    (hboundP : P.EdgesAtLeast (n + 1)) (hboundQ : Q.EdgesAtLeast (n + 1))
    (hne : ∀ i, («Σ».adjointFamily Q i).negative.Nonempty) :
    let «Σ'» := «Σ».selectedFan («Σ».adjointFamily Q) hne
      («Σ».adjointFamily_disjoint hpure Q hQ hfanQ hboundQ)
    «Σ'».IsNef («Σ».firstAdjointCenter P Q) ∧
      «Σ'».IsNef («Σ».secondAdjointCenter Q hne) := by
  let R := «Σ».adjointFamily Q
  have hR : ∀ i, (R i).IsCombinatoriallyContractible :=
    «Σ».adjointFamily_contractible Q
  have hlarge : ∀ i, n < 2 * (R i).fiberDimension :=
    «Σ».adjointFamily_large hpure Q hQ hfanQ hboundQ
  have hdisj := «Σ».adjointFamily_disjoint hpure Q hQ hfanQ hboundQ
  constructor
  · exact «Σ».first_adjoint_center_isNef R hR hne hdisj
      hpure P hP hfanP hboundP hlarge
  · apply «Σ».second_adjoint_center_isNef R hR hne hdisj
      hpure Q hQ hfanQ hboundQ
      (fun i => («Σ».adjointDisplacements Q hne i : ℝ))
    · intro i
      exact ((R i).adjointDisplacement_bounds (hR i) (hne i)
        hpure Q hQ hfanQ hboundQ («Σ».selectionRelation_test _ i)).2.1
    · intro i
      exact ((R i).adjointDisplacement_bounds (hR i) (hne i)
        hpure Q hQ hfanQ hboundQ («Σ».selectionRelation_test _ i)).2.2.1
    · intro i
      exact ((R i).adjointDisplacement_bounds (hR i) (hne i)
        hpure Q hQ hfanQ hboundQ («Σ».selectionRelation_test _ i)).2.2.2
    · intro S hS hn
      have h := «Σ».adjoint_unselected_degree_bound
        (fun u => (Q.integralSupport u : ℝ)) S hS hn
      simpa only [S.coefficientSum_cast] using h

end SmoothCompleteFan

end PaperVerification.ToricGeometry
end
end Source_ToricCanonicalCenters
-- END ORIGINAL PaperVerification.ToricCanonicalCenters


-- BEGIN ORIGINAL PaperVerification.ToricParityClasses
section Source_ToricParityClasses

-- original header: module
-- original header: public import PaperVerification.ToricStatements
-- original header: public import Mathlib.GroupTheory.QuotientGroup.Defs
-- original header: @[expose] public section
/-!
# Prescribed parity as the actual quotient M / 2M

The principal Lean target quantifies over lattice representatives. This file
proves its equivalence to the paper's quantification over quotient classes.
The subgroup is exactly the image of doubling, with no finite restriction.
-/

noncomputable section

namespace PaperVerification.ToricGeometry

open Set
open PaperVerification.ToricExchange

/-- The actual subgroup 2M of the coordinate lattice. -/
def twiceLattice (n : ℕ) : AddSubgroup (Lattice n) where
  carrier := {z | ∃ w, z = w + w}
  zero_mem' := ⟨0, by simp⟩
  add_mem' := by
    rintro a b ⟨u, rfl⟩ ⟨v, rfl⟩
    exact ⟨u + v, by abel⟩
  neg_mem' := by
    rintro a ⟨u, rfl⟩
    exact ⟨-u, by abel⟩

/-- The quotient group used in the original prescribed-parity statement. -/
abbrev ParityClass (n : ℕ) := Lattice n ⧸ twiceLattice n

/-- Send a lattice vector to its actual class modulo the doubled lattice. -/
def parityClass (n : ℕ) : Lattice n →+ ParityClass n :=
  QuotientAddGroup.mk' (twiceLattice n)

theorem parityClass_surjective (n : ℕ) : Function.Surjective (parityClass n) :=
  QuotientAddGroup.mk'_surjective (twiceLattice n)

/-- The witness-based parity relation is precisely equality in M/2M. -/
theorem sameParity_iff_parityClass_eq {n : ℕ} (a b : Lattice n) :
    SameParity a b ↔ parityClass n a = parityClass n b := by
  change SameParity a b ↔ (a : Lattice n ⧸ twiceLattice n) = b
  rw [QuotientAddGroup.eq_iff_sub_mem]
  rfl

/-- Prescribing every representative is equivalent to prescribing every
quotient class, for arbitrary summand sets and an arbitrary fixed total. -/
theorem prescribedParity_representatives_iff_classes {n : ℕ}
    (S T : Set (Lattice n)) (m : Lattice n) :
    (∀ c : Lattice n, ∃ a b : Lattice n,
      a ∈ S ∧ b ∈ T ∧ a + b = m ∧ SameParity a c) ↔
    (∀ α : ParityClass n, ∃ a b : Lattice n,
      a ∈ S ∧ b ∈ T ∧ a + b = m ∧ parityClass n a = α) := by
  constructor
  · intro h α
    obtain ⟨c, rfl⟩ := parityClass_surjective n α
    obtain ⟨a, b, ha, hb, hab, hpar⟩ := h c
    exact ⟨a, b, ha, hb, hab, (sameParity_iff_parityClass_eq a c).mp hpar⟩
  · intro h c
    obtain ⟨a, b, ha, hb, hab, hpar⟩ := h (parityClass n c)
    exact ⟨a, b, ha, hb, hab, (sameParity_iff_parityClass_eq a c).mpr hpar⟩

/-- The principal parity target is exactly equivalent to the quotient-class
formulation used in the paper, with every other quantifier unchanged. -/
theorem theorem1_2_iff_quotient_classes :
    Theorem1_2PolytopeStatement ↔
      ∀ n : ℕ, ∀ P Q : LatticePolytope n,
        P.Smooth → Q.Smooth → P.SameNormalFan Q →
        P.EdgesAtLeast n → Q.EdgesAtLeast n →
        ∀ m : Lattice n, embed n m ∈ interior (P.minkowskiSum Q) →
          ∀ α : ParityClass n, ∃ a b : Lattice n,
            embed n a ∈ P.carrier ∧ embed n b ∈ Q.carrier ∧
            a + b = m ∧ parityClass n a = α := by
  constructor
  · intro h n P Q hP hQ hfan hlP hlQ m hm
    exact (prescribedParity_representatives_iff_classes
      ((embed n) ⁻¹' P.carrier) ((embed n) ⁻¹' Q.carrier) m).mp
        (h n P Q hP hQ hfan hlP hlQ m hm)
  · intro h n P Q hP hQ hfan hlP hlQ m hm
    exact (prescribedParity_representatives_iff_classes
      ((embed n) ⁻¹' P.carrier) ((embed n) ⁻¹' Q.carrier) m).mpr
        (h n P Q hP hQ hfan hlP hlQ m hm)

end PaperVerification.ToricGeometry

end
end Source_ToricParityClasses
-- END ORIGINAL PaperVerification.ToricParityClasses


-- BEGIN ORIGINAL PaperVerification.ToricCenterCovering
section Source_ToricCenterCovering

-- original header: module

-- original header: public import PaperVerification.ToricFanPolytopes
-- original header: public import PaperVerification.ToricInteriorDecomposition
-- original header: public import PaperVerification.ToricParityClasses

-- original header: @[expose] public section

/-!
# Lattice summands from the actual nef center polytopes

The finite box covering theorem is applied to the ordinary integer lattice.
For prescribed parity, the two sets are translated by complementary integral
vectors and divided by two. Thus the selected points give literal integral
summands in the requested coset, without a parity assumption on the centers.
The second set may be an ordinary interior; only convexity is used.
-/

noncomputable section

namespace PaperVerification.ToricGeometry

open Set
open scoped BigOperators
open PaperVerification.Toric PaperVerification.ToricExchange

section FiniteBoxes

variable {n : ℕ} {J : Type*} [Fintype J]

/-- An actual integral decomposition from a finite convex average of
matched integral-basis unit boxes. The containing convex sets are arbitrary. -/
theorem integral_summands_of_centered_unit_boxes
    (b : J → Module.Basis (Fin n) ℤ (Lattice n))
    (A B : Set (Ambient n)) (hA : Convex ℝ A) (hB : Convex ℝ B)
    (a c : J → Ambient n)
    (hboxA : ∀ (j : J) (t : Fin n → ℝ), (∀ i, |t i| ≤ 1 / 2) →
      a j + ∑ i, t i • integralBasisReal (b j) i ∈ A)
    (hboxB : ∀ (j : J) (t : Fin n → ℝ), (∀ i, |t i| ≤ 1 / 2) →
      c j + ∑ i, t i • integralBasisReal (b j) i ∈ B)
    (m : Lattice n)
    (hm : embed n m ∈ convexHull ℝ (Set.range fun j => a j + c j)) :
    ∃ x y : Lattice n, embed n x ∈ A ∧ embed n y ∈ B ∧ x + y = m := by
  classical
  obtain ⟨p, hp, hpsum, hpm⟩ :=
    exists_probability_of_mem_convexHull_range (fun j => a j + c j) hm
  let L := standardIntegerLattice n
  letI : DiscreteTopology L := standardIntegerLattice_discreteTopology n
  letI : DiscreteTopology L.toAddSubgroup := inferInstanceAs (DiscreteTopology L)
  have hclosed : IsClosed (L.toAddSubgroup : Set (Ambient n)) :=
    AddSubgroup.isClosed_of_discreteTopology
  have hbL (j : J) (i : Fin n) : integralBasisReal (b j) i ∈ L.toAddSubgroup := by
    rw [integralBasisReal_apply]
    exact (mem_standardIntegerLattice_iff _).mpr ⟨b j i, rfl⟩
  have hmL : embed n m ∈ L.toAddSubgroup :=
    (mem_standardIntegerLattice_iff _).mpr ⟨m, rfl⟩
  obtain ⟨x, hx, y, hy, hxL, hyL, hxy⟩ :=
    finite_basis_boxes_lattice_decomposition_pi (fun j => integralBasisReal (b j))
      L.toAddSubgroup hclosed hbL A B hA hB p hp hpsum a c
      hboxA hboxB (embed n m) hmL hpm.symm
  obtain ⟨xZ, hxZ⟩ := (mem_standardIntegerLattice_iff x).mp hxL
  obtain ⟨yZ, hyZ⟩ := (mem_standardIntegerLattice_iff y).mp hyL
  refine ⟨xZ, yZ, ?_, ?_, ?_⟩
  · simpa only [hxZ] using hx
  · simpa only [hyZ] using hy
  · apply embed_injective n
    simpa only [map_add, hxZ, hyZ] using hxy

theorem convex_double_translate_preimage (A : Set (Ambient n))
    (hA : Convex ℝ A) (e : Ambient n) :
    Convex ℝ {x | e + (2 : ℝ) • x ∈ A} := by
  intro x hx y hy a b ha hb hab
  have h := hA hx hy ha hb hab
  change e + (2 : ℝ) • (a • x + b • y) ∈ A
  have he : e + (2 : ℝ) • (a • x + b • y) =
      a • (e + (2 : ℝ) • x) + b • (e + (2 : ℝ) • y) := by
    calc
      _ = (a + b) • e + (2 : ℝ) • (a • x + b • y) := by rw [hab, one_smul]
      _ = _ := by module
  rw [he]
  exact h

/-- Side-two boxes produce every prescribed parity of the first actual
lattice summand. The centers need not be integral, half-integral, or equal. -/
theorem prescribed_parity_of_centered_side_two_boxes
    (b : J → Module.Basis (Fin n) ℤ (Lattice n))
    (A B : Set (Ambient n)) (hA : Convex ℝ A) (hB : Convex ℝ B)
    (a c : J → Ambient n)
    (hboxA : ∀ (j : J) (t : Fin n → ℝ), (∀ i, |t i| ≤ 1) →
      a j + ∑ i, t i • integralBasisReal (b j) i ∈ A)
    (hboxB : ∀ (j : J) (t : Fin n → ℝ), (∀ i, |t i| ≤ 1) →
      c j + ∑ i, t i • integralBasisReal (b j) i ∈ B)
    (m ε : Lattice n)
    (hm : embed n m ∈ convexHull ℝ (Set.range fun j => a j + c j)) :
    ∃ x y : Lattice n, embed n x ∈ A ∧ embed n y ∈ B ∧
      x + y = m ∧ SameParity x ε := by
  classical
  let e := embed n ε
  let f := embed n (m - ε)
  let A' : Set (Ambient n) := {x | e + (2 : ℝ) • x ∈ A}
  let B' : Set (Ambient n) := {x | f + (2 : ℝ) • x ∈ B}
  let a' : J → Ambient n := fun j => (1 / 2 : ℝ) • (a j - e)
  let c' : J → Ambient n := fun j => (1 / 2 : ℝ) • (c j - f)
  have hef : e + f = embed n m := by
    dsimp [e, f]
    rw [← map_add]
    congr 1
    abel
  have hboxA' (j : J) (t : Fin n → ℝ) (ht : ∀ i, |t i| ≤ 1 / 2) :
      a' j + ∑ i, t i • integralBasisReal (b j) i ∈ A' := by
    change e + (2 : ℝ) • (a' j + ∑ i, t i • integralBasisReal (b j) i) ∈ A
    have heq : e + (2 : ℝ) • (a' j + ∑ i, t i • integralBasisReal (b j) i) =
        a j + ∑ i, (2 * t i) • integralBasisReal (b j) i := by
      dsimp [a']
      rw [smul_add, smul_smul, show (2 : ℝ) * (1 / 2) = 1 by norm_num,
        one_smul, Finset.smul_sum]
      simp only [smul_smul]
      abel
    rw [heq]
    apply hboxA
    intro i
    rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
    linarith [ht i]
  have hboxB' (j : J) (t : Fin n → ℝ) (ht : ∀ i, |t i| ≤ 1 / 2) :
      c' j + ∑ i, t i • integralBasisReal (b j) i ∈ B' := by
    change f + (2 : ℝ) • (c' j + ∑ i, t i • integralBasisReal (b j) i) ∈ B
    have heq : f + (2 : ℝ) • (c' j + ∑ i, t i • integralBasisReal (b j) i) =
        c j + ∑ i, (2 * t i) • integralBasisReal (b j) i := by
      dsimp [c']
      rw [smul_add, smul_smul, show (2 : ℝ) * (1 / 2) = 1 by norm_num,
        one_smul, Finset.smul_sum]
      simp only [smul_smul]
      abel
    rw [heq]
    apply hboxB
    intro i
    rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
    linarith [ht i]
  obtain ⟨p, hp, hpsum, hpm⟩ :=
    exists_probability_of_mem_convexHull_range (fun j => a j + c j) hm
  have hsum' : ∑ j, p j • (a' j + c' j) = 0 := by
    calc
      (∑ j, p j • (a' j + c' j)) =
          ∑ j, (1 / 2 : ℝ) • (p j • (a j + c j) - p j • (e + f)) := by
        apply Finset.sum_congr rfl
        intro j hj
        dsimp [a', c']
        simp only [smul_add, smul_sub, smul_smul]
        rw [mul_comm (p j) (1 / 2 : ℝ)]
        abel
      _ = (1 / 2 : ℝ) • ((∑ j, p j • (a j + c j)) -
          (∑ j, p j) • (e + f)) := by
        rw [← Finset.smul_sum, Finset.sum_sub_distrib, ← Finset.sum_smul]
      _ = 0 := by rw [hpm, hpsum, one_smul, hef, sub_self, smul_zero]
  have hzero : embed n (0 : Lattice n) ∈
      convexHull ℝ (Set.range fun j => a' j + c' j) := by
    rw [map_zero, ← hsum']
    exact (convex_convexHull ℝ _).sum_mem (fun j _ => hp j) hpsum
      (fun j _ => subset_convexHull ℝ _ (Set.mem_range_self j))
  obtain ⟨x, y, hx, hy, hxy⟩ := integral_summands_of_centered_unit_boxes b A' B'
    (convex_double_translate_preimage A hA e)
    (convex_double_translate_preimage B hB f) a' c' hboxA' hboxB' 0 hzero
  refine ⟨ε + x + x, (m - ε) + y + y, ?_, ?_, ?_, ⟨x, by abel⟩⟩
  · change e + (2 : ℝ) • embed n x ∈ A at hx
    simpa only [map_add, two_smul, e, add_assoc] using hx
  · change f + (2 : ℝ) • embed n y ∈ B at hy
    simpa only [map_add, two_smul, f, add_assoc] using hy
  · calc
      _ = m + (x + y) + (x + y) := by abel
      _ = m := by rw [hxy]; simp

end FiniteBoxes

namespace SmoothCompleteFan

variable {n : ℕ} («Σ» : SmoothCompleteFan n)

/-- The covered-target branch of the parity argument, on the actual
nef center polytopes and the original containing convex sets. -/
theorem parity_summands_of_nef_centers (hpure : «Σ».IsPure)
    (A B : Set (Ambient n)) (hA : Convex ℝ A) (hB : Convex ℝ B)
    (a c : Lattice n → ℝ) (ha : «Σ».IsNef a) (hc : «Σ».IsNef c)
    (hboxA : ∀ (s : «Σ».fullCones) (t : Fin n → ℝ), (∀ i, |t i| ≤ 1) →
      «Σ».cartierPoint a s + ∑ i, t i • «Σ».cartierBasis s i ∈ A)
    (hboxB : ∀ (s : «Σ».fullCones) (t : Fin n → ℝ), (∀ i, |t i| ≤ 1) →
      «Σ».cartierPoint c s + ∑ i, t i • «Σ».cartierBasis s i ∈ B)
    (m ε : Lattice n) (hm : embed n m ∈ «Σ».fanPolytope (a + c)) :
    ∃ x y : Lattice n, embed n x ∈ A ∧ embed n y ∈ B ∧
      x + y = m ∧ SameParity x ε := by
  have hhull : embed n m ∈ convexHull ℝ
      (Set.range fun s => «Σ».cartierPoint a s + «Σ».cartierPoint c s) := by
    rw [«Σ».fanPolytope_eq_convexHull_cartier hpure (a + c) (IsNef.add «Σ» ha hc)] at hm
    have hpoint : «Σ».cartierPoint (a + c) =
        fun s => «Σ».cartierPoint a s + «Σ».cartierPoint c s := by
      funext s
      exact «Σ».cartierPoint_add a c s
    rw [hpoint] at hm
    exact hm
  exact prescribed_parity_of_centered_side_two_boxes
    (fun s => integralDualBasis («Σ».fullConeBasis s)) A B hA hB
    («Σ».cartierPoint a) («Σ».cartierPoint c) hboxA hboxB m ε hhull

/-- The covered-target branch for unit boxes. Taking `B` to be the actual
interior of the second polytope gives an interior lattice summand. -/
theorem integral_summands_of_nef_centers (hpure : «Σ».IsPure)
    (A B : Set (Ambient n)) (hA : Convex ℝ A) (hB : Convex ℝ B)
    (a c : Lattice n → ℝ) (ha : «Σ».IsNef a) (hc : «Σ».IsNef c)
    (hboxA : ∀ (s : «Σ».fullCones) (t : Fin n → ℝ), (∀ i, |t i| ≤ 1 / 2) →
      «Σ».cartierPoint a s + ∑ i, t i • «Σ».cartierBasis s i ∈ A)
    (hboxB : ∀ (s : «Σ».fullCones) (t : Fin n → ℝ), (∀ i, |t i| ≤ 1 / 2) →
      «Σ».cartierPoint c s + ∑ i, t i • «Σ».cartierBasis s i ∈ B)
    (m : Lattice n) (hm : embed n m ∈ «Σ».fanPolytope (a + c)) :
    ∃ x y : Lattice n, embed n x ∈ A ∧ embed n y ∈ B ∧ x + y = m := by
  have hhull : embed n m ∈ convexHull ℝ
      (Set.range fun s => «Σ».cartierPoint a s + «Σ».cartierPoint c s) := by
    rw [«Σ».fanPolytope_eq_convexHull_cartier hpure (a + c) (IsNef.add «Σ» ha hc)] at hm
    have hpoint : «Σ».cartierPoint (a + c) =
        fun s => «Σ».cartierPoint a s + «Σ».cartierPoint c s := by
      funext s
      exact «Σ».cartierPoint_add a c s
    rw [hpoint] at hm
    exact hm
  exact integral_summands_of_centered_unit_boxes
    (fun s => integralDualBasis («Σ».fullConeBasis s)) A B hA hB
    («Σ».cartierPoint a) («Σ».cartierPoint c) hboxA hboxB m hhull

end SmoothCompleteFan

end PaperVerification.ToricGeometry
end
end Source_ToricCenterCovering
-- END ORIGINAL PaperVerification.ToricCenterCovering


-- BEGIN ORIGINAL PaperVerification.ToricCenterTargets
section Source_ToricCenterTargets

-- original header: module

-- original header: public import PaperVerification.ToricCanonicalCenters
-- original header: public import PaperVerification.ToricCenterCovering
-- original header: public import PaperVerification.ToricAdjointSupport

-- original header: @[expose] public section

/-!
# Literal ray inequalities for the covered targets

The center-polytope tests are derived on the actual common subdivision.
Singleton selected foci remain old rays and are included in the same
calculation. The integral slacks are the genuine primitive pairings with
the lattice target, before any cast to the reals.
-/

noncomputable section

namespace PaperVerification.ToricGeometry

open Set
open scoped BigOperators Classical Pointwise

def latticeSlack {n : ℕ} (a : Lattice n → ℤ) (m u : Lattice n) : ℤ :=
  (∑ j, u j * m j) + a u

namespace SmoothCompleteFan

variable {n : ℕ} («Σ» : SmoothCompleteFan n)

theorem latticeSlack_cast («Σ» : SmoothCompleteFan n)
    (a : Lattice n → ℤ) (m u : Lattice n) :
    (latticeSlack a m u : ℝ) =
      (dotProductEquiv ℝ (Fin n) (embed n u)) (embed n m) + a u := by
  rw [normalRay_pairing_lattice]
  simp only [latticeSlack, Int.cast_add]

theorem latticeSlack_pos_of_interior (a : Lattice n → ℤ) (m : Lattice n)
    (hm : embed n m ∈ interior («Σ».fanPolytope (fun u => (a u : ℝ))))
    (u : Lattice n) (hu : u ∈ «Σ».rays) : 0 < latticeSlack a m u := by
  rw [«Σ».interior_fanPolytope_eq] at hm
  have h := hm u hu
  have hc := «Σ».latticeSlack_cast a m u
  have hr : (0 : ℝ) < (latticeSlack a m u : ℝ) := by linarith
  exact_mod_cast hr

theorem normalRay_sum_pairing («Σ» : SmoothCompleteFan n)
    (T : Finset (Lattice n)) (x : Ambient n) :
    (dotProductEquiv ℝ (Fin n) (embed n (∑ u ∈ T, u))) x =
      ∑ u ∈ T, (dotProductEquiv ℝ (Fin n) (embed n u)) x := by
  simp only [map_sum, LinearMap.sum_apply]

variable {ι : Type*} [Fintype ι] (R : ι → «Σ».PrimitiveRelation)
variable (hne : ∀ i, (R i).negative.Nonempty)
variable (hdisj : «Σ».PairwiseDisjointFoci (fun i => (R i).negative))

theorem selectedFan_isPure (hpure : «Σ».IsPure) :
    («Σ».selectedFan R hne hdisj).IsPure :=
  «Σ».isPure_simultaneousSubdivision («Σ».selectedStarFocus R) hpure
    (fun i => (R i).negative_cone) (fun i => hne i)
    («Σ».selectedStarFocus_disjoint R hdisj)

theorem selectedPullback_old (a : Lattice n → ℝ)
    (u : Lattice n) (hu : u ∈ «Σ».rays) : «Σ».selectedPullback R a u = a u :=
  «Σ».simultaneousSupport_old («Σ».selectedStarFocus R)
    (fun i => (R i).negative_cone) (fun i => i.property) a 0 u hu

theorem selectedPullback_add (a b : Lattice n → ℝ) :
    «Σ».selectedPullback R (a + b) = «Σ».selectedPullback R a + «Σ».selectedPullback R b := by
  funext v
  simp only [selectedPullback, simultaneousSupport, Pi.add_apply, Pi.zero_apply,
    sub_zero, Finset.sum_add_distrib]
  have h : (∑ i : «Σ».BlowupIndices R,
      if v = ∑ w ∈ «Σ».selectedStarFocus R i, w then
        ((∑ w ∈ «Σ».selectedStarFocus R i, a w) + ∑ w ∈ «Σ».selectedStarFocus R i, b w) -
          (a v + b v) else 0) =
      (∑ i : «Σ».BlowupIndices R,
        if v = ∑ w ∈ «Σ».selectedStarFocus R i, w then
          (∑ w ∈ «Σ».selectedStarFocus R i, a w) - a v else 0) +
      ∑ i : «Σ».BlowupIndices R,
        if v = ∑ w ∈ «Σ».selectedStarFocus R i, w then
          (∑ w ∈ «Σ».selectedStarFocus R i, b w) - b v else 0 := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    split_ifs <;> ring
  rw [h]
  ring

def selectedCenterSupport (a : Lattice n → ℝ) (c : ℝ) (t : ι → ℝ) : Lattice n → ℝ :=
  fun v => «Σ».selectedPullback R a v - c -
    ∑ i, if v = «Σ».selectedRay R i then t i else 0

theorem selectedCenterSupport_add (a b : Lattice n → ℝ)
    (c d : ℝ) (t s : ι → ℝ) :
    «Σ».selectedCenterSupport R a c t + «Σ».selectedCenterSupport R b d s =
      «Σ».selectedCenterSupport R (a + b) (c + d) (t + s) := by
  funext v
  simp only [selectedCenterSupport, «Σ».selectedPullback_add R, Pi.add_apply]
  have h : (∑ i, if v = «Σ».selectedRay R i then t i + s i else 0) =
      (∑ i, if v = «Σ».selectedRay R i then t i else 0) +
      ∑ i, if v = «Σ».selectedRay R i then s i else 0 := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    split_ifs <;> simp
  rw [h]
  ring

include hne hdisj in
theorem selectedCenterSupport_at_selected_ray
    (a : Lattice n → ℝ) (c : ℝ) (t : ι → ℝ) (i : ι) :
    «Σ».selectedCenterSupport R a c t («Σ».selectedRay R i) =
      (∑ u ∈ (R i).negative, a u) - c - t i := by
  rw [selectedCenterSupport, «Σ».selectedPullback_at_selected_ray R hne hdisj]
  have h : (∑ j, if «Σ».selectedRay R i = «Σ».selectedRay R j then t j else 0) = t i := by
    simp only [(«Σ».selectedRay_injective R hdisj).eq_iff]
    simp
  rw [h]

/-- The old inequalities and the total-height inequality at every
selected locus imply membership in the literal center polytope. -/
theorem mem_selectedCenterSupport_of_slacks
    (a : Lattice n → ℝ) (c : ℝ) (t : ι → ℝ) (x : Ambient n)
    (hold : ∀ u ∈ «Σ».rays,
      c ≤ (dotProductEquiv ℝ (Fin n) (embed n u)) x + a u)
    (hselected : ∀ i, c + t i ≤ ∑ u ∈ (R i).negative,
      ((dotProductEquiv ℝ (Fin n) (embed n u)) x + a u)) :
    x ∈ («Σ».selectedFan R hne hdisj).fanPolytope
      («Σ».selectedCenterSupport R a c t) := by
  intro u hu
  by_cases hex : ∃ i, u = «Σ».selectedRay R i
  · obtain ⟨i, rfl⟩ := hex
    rw [«Σ».selectedCenterSupport_at_selected_ray R hne hdisj]
    have hd := «Σ».normalRay_sum_pairing (R i).negative x
    have hh := hselected i
    rw [Finset.sum_add_distrib] at hh
    change (dotProductEquiv ℝ (Fin n)
      (embed n («Σ».selectedRay R i))) x = _ at hd
    linarith
  · have hn : ∀ i, u ≠ «Σ».selectedRay R i := by simpa only [not_exists] using hex
    have holdray : u ∈ «Σ».rays := by
      rw [selectedFan, «Σ».simultaneous_rays_eq («Σ».selectedStarFocus R)
        (fun i => (R i).negative_cone) (fun i => hne i)
        («Σ».selectedStarFocus_disjoint R hdisj) (fun i => i.property)] at hu
      rcases Finset.mem_union.mp hu with hu | hu
      · exact hu
      · obtain ⟨i, hi, he⟩ := Finset.mem_image.mp hu
        exact False.elim (hn i he.symm)
    rw [selectedCenterSupport, «Σ».selectedPullback_old R a u holdray]
    simp only [hn, if_false, Finset.sum_const_zero, sub_zero]
    linarith [hold u holdray]

end SmoothCompleteFan

namespace SmoothCompleteFan

variable {n : ℕ} («Σ» : SmoothCompleteFan n)

/-- Exact sufficient height test from Section 6.3, including a selected
old ray when its focus has cardinality one. -/
theorem parity_centers_cover_of_slacks (hpure : «Σ».IsPure)
    (P Q : LatticePolytope n) (hP : P.Smooth) (hQ : Q.Smooth)
    (hfanP : «Σ».realCones = P.normalFan) (hfanQ : «Σ».realCones = Q.normalFan)
    (hboundP : P.EdgesAtLeast n) (hboundQ : Q.EdgesAtLeast n)
    (hne : ∀ i, («Σ».parityFamily P Q i).negative.Nonempty)
    (m : Lattice n)
    (hold : ∀ u ∈ «Σ».rays, 2 ≤ latticeSlack (P.integralSupport + Q.integralSupport) m u)
    (hselected : ∀ i,
      «Σ».parityDisplacements P Q P hne i + «Σ».parityDisplacements P Q Q hne i + 2 ≤
        ∑ u ∈ («Σ».parityFamily P Q i).negative,
          latticeSlack (P.integralSupport + Q.integralSupport) m u) :
    let Γ := «Σ».selectedFan («Σ».parityFamily P Q) hne
      («Σ».parityFamily_disjoint hpure P Q hP hQ hfanP hfanQ hboundP hboundQ)
    embed n m ∈ Γ.fanPolytope
      («Σ».parityCenter P Q P hne + «Σ».parityCenter P Q Q hne) := by
  let R := «Σ».parityFamily P Q
  let t : «Σ».parityIndices P Q → ℝ := fun i => «Σ».parityDisplacements P Q P hne i
  let s : «Σ».parityIndices P Q → ℝ := fun i => «Σ».parityDisplacements P Q Q hne i
  let a : Lattice n → ℝ := fun u => (P.integralSupport u : ℝ)
  let b : Lattice n → ℝ := fun u => (Q.integralSupport u : ℝ)
  change embed n m ∈ («Σ».selectedFan R hne
    («Σ».parityFamily_disjoint hpure P Q hP hQ hfanP hfanQ hboundP hboundQ)).fanPolytope
    («Σ».selectedCenterSupport R a 1 t + «Σ».selectedCenterSupport R b 1 s)
  rw [«Σ».selectedCenterSupport_add]
  apply «Σ».mem_selectedCenterSupport_of_slacks R hne
    («Σ».parityFamily_disjoint hpure P Q hP hQ hfanP hfanQ hboundP hboundQ)
  · intro u hu
    have hh : (2 : ℝ) ≤ (latticeSlack (P.integralSupport + Q.integralSupport) m u : ℝ) := by
      exact_mod_cast hold u hu
    rw [«Σ».latticeSlack_cast] at hh
    simpa only [a, b, Pi.add_apply, Int.cast_add, show (1 : ℝ) + 1 = 2 by norm_num]
      using hh
  · intro i
    have hh : («Σ».parityDisplacements P Q P hne i : ℝ) +
        («Σ».parityDisplacements P Q Q hne i : ℝ) + 2 ≤
        ∑ u ∈ (R i).negative,
          (latticeSlack (P.integralSupport + Q.integralSupport) m u : ℝ) := by
      exact_mod_cast hselected i
    simp only [«Σ».latticeSlack_cast, Pi.add_apply, Int.cast_add] at hh
    dsimp [a, b, t, s]
    linarith

/-- Exact sufficient height test from Section 7.5. The two different
canonical shifts add to two on old rays, and to q+t+1 at a selected locus. -/
theorem adjoint_centers_cover_of_slacks (hpure : «Σ».IsPure)
    (P Q : LatticePolytope n) (hP : P.Smooth) (hQ : Q.Smooth)
    (hfanP : «Σ».realCones = P.normalFan) (hfanQ : «Σ».realCones = Q.normalFan)
    (hboundP : P.EdgesAtLeast (n + 1)) (hboundQ : Q.EdgesAtLeast (n + 1))
    (hne : ∀ i, («Σ».adjointFamily Q i).negative.Nonempty)
    (m : Lattice n)
    (hold : ∀ u ∈ «Σ».rays, 2 ≤ latticeSlack (P.integralSupport + Q.integralSupport) m u)
    (hselected : ∀ i, ((«Σ».adjointFamily Q i).negative.card : ℤ) +
      «Σ».adjointDisplacements Q hne i + 1 ≤
        ∑ u ∈ («Σ».adjointFamily Q i).negative,
          latticeSlack (P.integralSupport + Q.integralSupport) m u) :
    let Γ := «Σ».selectedFan («Σ».adjointFamily Q) hne
      («Σ».adjointFamily_disjoint hpure Q hQ hfanQ hboundQ)
    embed n m ∈ Γ.fanPolytope
      («Σ».firstAdjointCenter P Q + «Σ».secondAdjointCenter Q hne) := by
  let R := «Σ».adjointFamily Q
  let t : «Σ».adjointIndices Q → ℝ := fun i => (R i).negative.card - 1
  let s : «Σ».adjointIndices Q → ℝ := fun i => «Σ».adjointDisplacements Q hne i
  let a : Lattice n → ℝ := fun u => (P.integralSupport u : ℝ)
  let b : Lattice n → ℝ := fun u => (Q.integralSupport u : ℝ)
  change embed n m ∈ («Σ».selectedFan R hne
    («Σ».adjointFamily_disjoint hpure Q hQ hfanQ hboundQ)).fanPolytope
    («Σ».selectedCenterSupport R a (1 / 2) t +
      «Σ».selectedCenterSupport R b (3 / 2) s)
  rw [«Σ».selectedCenterSupport_add]
  apply «Σ».mem_selectedCenterSupport_of_slacks R hne
    («Σ».adjointFamily_disjoint hpure Q hQ hfanQ hboundQ)
  · intro u hu
    have hh : (2 : ℝ) ≤ (latticeSlack (P.integralSupport + Q.integralSupport) m u : ℝ) := by
      exact_mod_cast hold u hu
    rw [«Σ».latticeSlack_cast] at hh
    simpa only [a, b, Pi.add_apply, Int.cast_add,
      show (1 / 2 : ℝ) + 3 / 2 = 2 by norm_num] using hh
  · intro i
    have hh : ((R i).negative.card : ℝ) + («Σ».adjointDisplacements Q hne i : ℝ) + 1 ≤
        ∑ u ∈ (R i).negative,
          (latticeSlack (P.integralSupport + Q.integralSupport) m u : ℝ) := by
      exact_mod_cast hselected i
    simp only [«Σ».latticeSlack_cast, Pi.add_apply, Int.cast_add] at hh
    dsimp [a, b, t, s]
    linarith

/-- The primitive slacks of an actual interior Minkowski target are
positive integers. No interior condition has been replaced by a weaker
set of inequalities in the final induction. -/
theorem latticeSlack_pos_of_interior_minkowski (hpure : «Σ».IsPure)
    (P Q : LatticePolytope n)
    (hfanP : «Σ».realCones = P.normalFan) (hfanQ : «Σ».realCones = Q.normalFan)
    (m : Lattice n) (hm : embed n m ∈ interior (P.minkowskiSum Q)) :
    ∀ u ∈ «Σ».rays, 0 < latticeSlack (P.integralSupport + Q.integralSupport) m u := by
  have ha := P.integralSupport_isStrictSupport «Σ» hfanP
  have hb := Q.integralSupport_isStrictSupport «Σ» hfanQ
  have he : (fun u => ((P.integralSupport + Q.integralSupport) u : ℝ)) =
      (fun u => (P.integralSupport u : ℝ)) +
        (fun u => (Q.integralSupport u : ℝ)) := by
    funext u
    simp
  have hset : «Σ».fanPolytope
      (fun u => ((P.integralSupport + Q.integralSupport) u : ℝ)) = P.minkowskiSum Q := by
    rw [he, «Σ».fanPolytope_add hpure _ _
      (IsStrictSupport.isNef «Σ» ha) (IsStrictSupport.isNef «Σ» hb),
      P.fanPolytope_integralSupport_eq «Σ» hfanP,
      Q.fanPolytope_integralSupport_eq «Σ» hfanQ]
    rfl
  intro u hu
  exact «Σ».latticeSlack_pos_of_interior _ m (hset.symm ▸ hm) u hu

end SmoothCompleteFan

end PaperVerification.ToricGeometry
end
end Source_ToricCenterTargets
-- END ORIGINAL PaperVerification.ToricCenterTargets


-- BEGIN ORIGINAL PaperVerification.ToricQuotientFacePolytopes
section Source_ToricQuotientFacePolytopes

-- original header: module

-- original header: public import PaperVerification.ToricQuotientFaceSupport
-- original header: public import PaperVerification.ToricDisplacedEdgeBounds
-- original header: public import PaperVerification.ToricSmoothFaces

-- original header: @[expose] public section

/-!
# Actual smooth lattice polytopes of displaced faces

Integral restriction coefficients construct a full-dimensional smooth
polytope in the saturated face lattice. Its exact fan, affine image, and
all edge bounds follow from the preceding geometric results.
-/

noncomputable section

namespace PaperVerification.ToricGeometry.SmoothCompleteFan

open Set
open scoped BigOperators Classical

variable {n : ℕ} («Σ» : SmoothCompleteFan n)
    (b : Module.Basis (Fin n) ℤ (Lattice n)) (I : Finset (Fin n))
    (hF : I.image b ∈ «Σ».cones)

theorem isStrictSupport_of_dimension_zero {d : ℕ} (Ψ : SmoothCompleteFan d)
    (hd : d = 0) (a : Lattice d → ℝ) : Ψ.IsStrictSupport a := by
  subst d
  have hnoray (u : Lattice 0) : u ∉ Ψ.rays := by
    intro hu
    exact Ψ.ray_ne_zero hu (Subsingleton.elim u 0)
  intro s hs
  refine ⟨0, ?_, ?_⟩
  · intro u hu
    exact (hnoray u (Ψ.ray_mem_of_mem_cone hs hu)).elim
  · intro u hu hus
    exact (hnoray u hu).elim

/-- Global nefness is enough when the actual restriction is strictly
supported. This includes collapsed normal directions at an endpoint. -/
theorem exists_face_supportPolytope_of_nefRestriction (hpure : «Σ».IsPure)
    (a : Lattice n → ℤ) (ha : «Σ».IsNef (fun u => (a u : ℝ)))
    (hq : («Σ».completeQuotientStarFan b I hF).IsStrictSupport
      (fun u => («Σ».faceSupportLattice b I hF a u : ℝ))) :
    ∃ Q : LatticePolytope (n - I.card),
      Q.carrier = («Σ».completeQuotientStarFan b I hF).fanPolytope
        (fun u => («Σ».faceSupportLattice b I hF a u : ℝ)) ∧
      Q.Smooth ∧ Q.normalFan = («Σ».completeQuotientStarFan b I hF).realCones ∧
      (quotientFaceIntegralChart a b I).realMap '' Q.carrier =
        «Σ».supportFace (fun u => (a u : ℝ)) (I.image b) := by
  let Ψ := «Σ».completeQuotientStarFan b I hF
  obtain ⟨Q, hQ, hQs, hQfan⟩ :=
    Ψ.exists_smooth_latticePolytope_of_integral_strictSupport
      («Σ».completeQuotientStarFan_isPure hpure b I hF)
      («Σ».faceSupportLattice b I hF a) hq
  refine ⟨Q, hQ, hQs, hQfan, ?_⟩
  rw [hQ]
  exact «Σ».quotientFaceIntegralChart_image_fanPolytope b I hF hpure a ha

/-- Actual smooth face polytopes, with exact normal fan and unchanged edge
bound, in the chosen saturated chart. -/
theorem exists_face_supportPolytope (hpure : «Σ».IsPure)
    (a : Lattice n → ℤ) (ha : «Σ».IsStrictSupport (fun u => (a u : ℝ)))
    (P : LatticePolytope n) (hP : P.carrier = «Σ».fanPolytope (fun u => (a u : ℝ)))
    {bound : ℕ} (hbound : P.EdgesAtLeast bound) :
    ∃ Q : LatticePolytope (n - I.card),
      Q.carrier = («Σ».completeQuotientStarFan b I hF).fanPolytope
        (fun u => («Σ».faceSupportLattice b I hF a u : ℝ)) ∧
      Q.Smooth ∧ Q.normalFan = («Σ».completeQuotientStarFan b I hF).realCones ∧
      Q.EdgesAtLeast bound ∧
      (quotientFaceIntegralChart a b I).realMap '' Q.carrier =
        «Σ».supportFace (fun u => (a u : ℝ)) (I.image b) := by
  let Ψ := «Σ».completeQuotientStarFan b I hF
  let c := «Σ».faceSupportLattice b I hF a
  have hcpure : Ψ.IsPure := «Σ».completeQuotientStarFan_isPure hpure b I hF
  have hc : Ψ.IsStrictSupport (fun u => (c u : ℝ)) := by
    change Ψ.IsStrictSupport (fun u => («Σ».faceSupportLattice b I hF a u : ℝ))
    rw [«Σ».faceSupportLattice_cast]
    exact «Σ».faceSupport_isStrictSupport b I hF _ ha
  obtain ⟨Q, hQ, hQs, hQfan⟩ :=
    Ψ.exists_smooth_latticePolytope_of_integral_strictSupport hcpure c hc
  have himage : (quotientFaceIntegralChart a b I).realMap '' Q.carrier =
      «Σ».supportFace (fun u => (a u : ℝ)) (I.image b) := by
    rw [hQ]
    exact «Σ».quotientFaceIntegralChart_image_fanPolytope b I hF hpure a
      (IsStrictSupport.isNef «Σ» ha)
  have hface : IsExtreme ℝ P.carrier
      («Σ».supportFace (fun u => (a u : ℝ)) (I.image b)) := by
    rw [hP]
    exact «Σ».supportFace_isExtreme _ _ (fun u hu => «Σ».ray_mem_of_mem_cone hF hu)
  have hlength := P.edgesAtLeast_face_chart hbound _ hface Q
    (quotientFaceIntegralChart a b I) himage
  exact ⟨Q, hQ, hQs, hQfan, hlength, himage⟩

def displacedSupportLattice (a : Lattice n → ℤ)
    (T : Finset (Lattice n)) (h : Lattice n → ℕ) : Lattice n → ℤ :=
  fun u => a u - if u ∈ T then (h u : ℤ) else 0

theorem displacedSupportLattice_cast (a : Lattice n → ℤ)
    (T : Finset (Lattice n)) (h : Lattice n → ℕ) :
    (fun u => (displacedSupportLattice a T h u : ℝ)) =
      displacedSupport (fun u => (a u : ℝ)) T (fun u => (h u : ℝ)) := by
  funext u
  simp only [displacedSupportLattice, displacedSupport, Pi.sub_apply, facetWeight]
  split_ifs <;> simp

/-- Exact integral slices below the original edge threshold, with genuine
smoothness, a common actual quotient fan, saturation, and all edge bounds. -/
theorem exists_displaced_facePolytope (hpure : «Σ».IsPure)
    (a : Lattice n → ℤ) (ha : «Σ».IsStrictSupport (fun u => (a u : ℝ)))
    {e : ℕ} (hedges : («Σ».supportLatticePolytope hpure a ha).EdgesAtLeast e)
    (h : Lattice n → ℕ) (hbudget : (∑ u ∈ I.image b, h u) < e) :
    ∃ Q : LatticePolytope (n - I.card),
      Q.carrier = («Σ».completeQuotientStarFan b I hF).fanPolytope
        (fun u => («Σ».faceSupportLattice b I hF
          (displacedSupportLattice a (I.image b) h) u : ℝ)) ∧
      Q.Smooth ∧ Q.normalFan = («Σ».completeQuotientStarFan b I hF).realCones ∧
      Q.EdgesAtLeast (e - ∑ u ∈ I.image b, h u) ∧
      (quotientFaceIntegralChart (displacedSupportLattice a (I.image b) h) b I).realMap ''
        Q.carrier = {x ∈ «Σ».fanPolytope (fun u => (a u : ℝ)) | ∀ u ∈ I.image b,
          (dotProductEquiv ℝ (Fin n) (embed n u)) x + (a u : ℝ) = (h u : ℝ)} := by
  let d := displacedSupportLattice a (I.image b) h
  have hsum : (∑ u ∈ I.image b, (h u : ℝ)) = (∑ u ∈ I.image b, h u : ℕ) := by
    simp only [Nat.cast_sum]
  have hbudgetR : (∑ u ∈ I.image b, (h u : ℝ)) < (e : ℝ) := by
    rw [hsum]
    exact_mod_cast hbudget
  have hd : «Σ».IsStrictSupport (fun u => (d u : ℝ)) := by
    rw [displacedSupportLattice_cast]
    exact «Σ».displacedSupport_isStrictSupport_of_edges hpure a ha hedges _ _
      (fun u hu => Nat.cast_nonneg _) hbudgetR
  let D := «Σ».supportLatticePolytope hpure d hd
  have hDbound : D.EdgesAtLeast (e - ∑ u ∈ I.image b, h u) := by
    apply «Σ».displacedSupport_edgesAtLeast hpure a d ha hd (by omega) hedges
      (I.image b) (fun u => (h u : ℝ)) (fun u hu => Nat.cast_nonneg _)
      (displacedSupportLattice_cast a _ h) hbudgetR.le
    rw [hsum, Nat.cast_sub hbudget.le]
  obtain ⟨Q, hQ, hQs, hQfan, hQbound, himage⟩ :=
    «Σ».exists_face_supportPolytope b I hF hpure d hd D
      («Σ».supportLatticePolytope_carrier hpure d hd) hDbound
  refine ⟨Q, hQ, hQs, hQfan, hQbound, ?_⟩
  rw [himage, displacedSupportLattice_cast]
  exact «Σ».displaced_supportFace_eq_slice _ _ _ (fun u hu => Nat.cast_nonneg _)

/-- The first normal slice of an actual facet has the required dimension
and edge bound, including the zero-dimensional endpoint when `n=1`. -/
theorem exists_displaced_facetPolytope (hpure : «Σ».IsPure)
    (hIcard : I.card = 1)
    (a : Lattice n → ℤ) (ha : «Σ».IsStrictSupport (fun u => (a u : ℝ)))
    (hedges : («Σ».supportLatticePolytope hpure a ha).EdgesAtLeast n)
    (h : Lattice n → ℕ) (hbudget : (∑ u ∈ I.image b, h u) ≤ 1) :
    ∃ Q : LatticePolytope (n - I.card),
      Q.carrier = («Σ».completeQuotientStarFan b I hF).fanPolytope
        (fun u => («Σ».faceSupportLattice b I hF
          (displacedSupportLattice a (I.image b) h) u : ℝ)) ∧
      Q.Smooth ∧ Q.normalFan = («Σ».completeQuotientStarFan b I hF).realCones ∧
      Q.EdgesAtLeast (n - I.card) ∧
      (quotientFaceIntegralChart (displacedSupportLattice a (I.image b) h) b I).realMap ''
        Q.carrier = {x ∈ «Σ».fanPolytope (fun u => (a u : ℝ)) | ∀ u ∈ I.image b,
          (dotProductEquiv ℝ (Fin n) (embed n u)) x + (a u : ℝ) = (h u : ℝ)} := by
  have hIn : I.card ≤ n := by
    simpa only [Finset.card_fin] using Finset.card_le_card (Finset.subset_univ I)
  by_cases hlt : (∑ u ∈ I.image b, h u) < n
  · obtain ⟨Q, hQ, hQs, hQfan, hQbound, himage⟩ :=
      «Σ».exists_displaced_facePolytope b I hF hpure a ha hedges h hlt
    exact ⟨Q, hQ, hQs, hQfan, Q.edgesAtLeast_mono hQbound (by omega), himage⟩
  · have hn : n = 1 := by omega
    have hdim : n - I.card = 0 := by omega
    let d := displacedSupportLattice a (I.image b) h
    have hsum : (∑ u ∈ I.image b, (h u : ℝ)) = (∑ u ∈ I.image b, h u : ℕ) := by
      simp only [Nat.cast_sum]
    have hd : «Σ».IsNef (fun u => (d u : ℝ)) := by
      rw [displacedSupportLattice_cast]
      apply «Σ».displacedSupport_isNef_of_edges hpure a ha hedges _ _
        (fun u hu => Nat.cast_nonneg _)
      rw [hsum]
      exact_mod_cast (by omega : (∑ u ∈ I.image b, h u) ≤ n)
    have hq := isStrictSupport_of_dimension_zero («Σ».completeQuotientStarFan b I hF) hdim
      (fun u => («Σ».faceSupportLattice b I hF d u : ℝ))
    obtain ⟨Q, hQ, hQs, hQfan, himage⟩ :=
      «Σ».exists_face_supportPolytope_of_nefRestriction b I hF hpure d hd hq
    have hQbound : Q.EdgesAtLeast (n - I.card) := by
      apply (Q.edgesAtLeast_iff (n - I.card)).mpr
      intro x y hxy
      calc
        n - I.card = 0 := hdim
        _ ≤ LatticePolytope.latticeLength x y := Nat.zero_le _
    refine ⟨Q, hQ, hQs, hQfan, hQbound, ?_⟩
    rw [himage, displacedSupportLattice_cast]
    exact «Σ».displaced_supportFace_eq_slice _ _ _ (fun u hu => Nat.cast_nonneg _)

end PaperVerification.ToricGeometry.SmoothCompleteFan
end
end Source_ToricQuotientFacePolytopes
-- END ORIGINAL PaperVerification.ToricQuotientFacePolytopes


-- BEGIN ORIGINAL PaperVerification.ToricSliceCoordinates
section Source_ToricSliceCoordinates

-- original header: module

-- original header: public import PaperVerification.ToricQuotientFacePolytopes
-- original header: public import PaperVerification.ToricCanonicalSlices

-- original header: @[expose] public section

/-!
# Addition, interior targets, and prescribed parity in exact face charts

The two affine origins add, the tangent lattice map is shared, and every
integral target satisfying the active equations has integral quotient
coordinates. Normal parity compatibility is exactly the condition needed
to represent an ambient parity class in the selected affine chart.
-/

noncomputable section

namespace PaperVerification.ToricGeometry

open Set
open PaperVerification.ToricExchange
open scoped BigOperators Classical

variable {n : ℕ}

theorem quotientFaceOrigin_add (a c : Lattice n → ℝ)
    (b : Module.Basis (Fin n) ℤ (Lattice n)) (I : Finset (Fin n)) :
    quotientFaceOrigin (a + c) b I = quotientFaceOrigin a b I + quotientFaceOrigin c b I := by
  simp only [quotientFaceOrigin, Pi.add_apply, add_smul, Finset.sum_add_distrib, neg_add]

theorem quotientFaceMap_add (a c : Lattice n → ℝ)
    (b : Module.Basis (Fin n) ℤ (Lattice n)) (I : Finset (Fin n))
    (x y : Ambient (n - I.card)) :
    quotientFaceMap (a + c) b I (x + y) =
      quotientFaceMap a b I x + quotientFaceMap c b I y := by
  simp only [quotientFaceMap_apply, quotientFaceOrigin_add, map_add]
  abel

theorem quotientFaceIntegralChart_add (a c : Lattice n → ℤ)
    (b : Module.Basis (Fin n) ℤ (Lattice n)) (I : Finset (Fin n))
    (x y : Lattice (n - I.card)) :
    (quotientFaceIntegralChart (a + c) b I).latticeMap (x + y) =
      (quotientFaceIntegralChart a b I).latticeMap x +
        (quotientFaceIntegralChart c b I).latticeMap y := by
  apply embed_injective n
  rw [map_add, IntegralAffineEmbedding.embed_latticeMap,
    IntegralAffineEmbedding.embed_latticeMap, IntegralAffineEmbedding.embed_latticeMap,
    quotientFaceIntegralChart_realMap, quotientFaceIntegralChart_realMap,
    quotientFaceIntegralChart_realMap, map_add]
  have hcast : (fun u => ((a + c) u : ℝ)) =
      (fun u => (a u : ℝ)) + (fun u => (c u : ℝ)) := by
    funext u
    simp
  rw [hcast, quotientFaceMap_add]

theorem quotientFaceOriginLattice_coordinate (a : Lattice n → ℤ)
    (b : Module.Basis (Fin n) ℤ (Lattice n)) (I : Finset (Fin n)) (i : Fin n) :
    (integralDualBasis b).repr (quotientFaceOriginLattice a b I) i =
      if i ∈ I then -a (b i) else 0 := by
  simp only [quotientFaceOriginLattice, map_neg, map_sum, LinearEquiv.map_smul,
    Finsupp.neg_apply, Finsupp.finsetSum_apply, Finsupp.smul_apply,
    Module.Basis.repr_self_apply]
  by_cases hi : i ∈ I <;> simp [hi, smul_eq_mul]

/-- A parity class is represented in an actual saturated selected-basis
chart whenever its omitted coordinates have the required even residual. -/
theorem selectedBasisChart_parity_representative {d : ℕ}
    (v : Lattice n) (B : Module.Basis (Fin n) ℤ (Lattice n))
    (a : Fin d ↪ Fin n) (p : Lattice n)
    (hpar : ∀ i ∉ Set.range a, ∃ w : ℤ, B.repr (p - v) i = w + w) :
    ∃ q : Lattice d, SameParity ((selectedBasisChart v B a).latticeMap q) p := by
  let q : Lattice d := fun j => B.repr (p - v) (a j)
  let w : Fin n → ℤ := fun i => if hi : i ∉ Set.range a then Classical.choose (hpar i hi) else 0
  have hw (i : Fin n) (hi : i ∉ Set.range a) : B.repr (p - v) i = w i + w i := by
    simpa only [w, dif_pos hi] using Classical.choose_spec (hpar i hi)
  have hsum (i : Fin n) : B.repr (∑ j, w j • B j) i = w i := by
    simp only [map_sum, LinearEquiv.map_smul, Finsupp.finsetSum_apply,
      Finsupp.smul_apply, Module.Basis.repr_self_apply]
    simp [smul_eq_mul]
  refine ⟨q, -(∑ j, w j • B j), ?_⟩
  apply B.ext_elem
  intro i
  change B.repr (v + selectedBasisMap B a q - p) i = _
  simp only [map_add, map_sub, map_neg, Finsupp.add_apply, Finsupp.sub_apply,
    Finsupp.neg_apply, hsum]
  by_cases hi : i ∈ Set.range a
  · obtain ⟨j, rfl⟩ := hi
    rw [selectedBasisMap_coordinate]
    have hwzero : w (a j) = 0 := by
      have hjmem : a j ∈ Set.range a := ⟨j, rfl⟩
      simp only [w, dif_neg (not_not.mpr hjmem)]
    rw [hwzero]
    simp only [q, map_sub, Finsupp.sub_apply]
    ring
  · rw [selectedBasisMap_coordinate_eq_zero B a q i hi]
    have hwi := hw i hi
    simp only [map_sub, Finsupp.sub_apply] at hwi
    omega

/-- Prescribed normal parity lifts to the actual quotient face chart. -/
theorem quotientFace_parity_representative (a : Lattice n → ℤ)
    (b : Module.Basis (Fin n) ℤ (Lattice n)) (I : Finset (Fin n))
    (p : Lattice n)
    (hpar : ∀ i ∈ I, ∃ w : ℤ, (∑ j, p j * b i j) + a (b i) = w + w) :
    ∃ q : Lattice (n - I.card),
      SameParity ((quotientFaceIntegralChart a b I).latticeMap q) p := by
  apply selectedBasisChart_parity_representative
    (quotientFaceOriginLattice a b I) (integralDualBasis b) (complementaryEmbedding I) p
  intro i hi
  have hiI : i ∈ I := by
    simpa only [mem_range_complementaryEmbedding_iff, not_not] using hi
  obtain ⟨w, hw⟩ := hpar i hiI
  refine ⟨w, ?_⟩
  rw [map_sub, Finsupp.sub_apply, quotientFaceOriginLattice_coordinate,
    if_pos hiI, integralDualBasis_repr, sub_neg_eq_add, hw]

namespace SmoothCompleteFan

variable («Σ» : SmoothCompleteFan n)
    (b : Module.Basis (Fin n) ℤ (Lattice n)) (I : Finset (Fin n))
    (hF : I.image b ∈ «Σ».cones)

theorem faceSupport_add (a c : Lattice n → ℝ) :
    «Σ».faceSupport b I hF (a + c) = «Σ».faceSupport b I hF a + «Σ».faceSupport b I hF c := by
  funext u
  by_cases hu : u ∈ («Σ».completeQuotientStarFan b I hF).rays
  · simp only [faceSupport, dif_pos hu, Pi.add_apply, quotientFaceOrigin_add, map_add]
    ring
  · simp only [faceSupport, dif_neg hu, Pi.add_apply, zero_add]

theorem faceSupportLattice_add (a c : Lattice n → ℤ) :
    «Σ».faceSupportLattice b I hF (a + c) =
      «Σ».faceSupportLattice b I hF a + «Σ».faceSupportLattice b I hF c := by
  funext u
  apply Int.cast_injective (α := ℝ)
  have he := congrFun («Σ».faceSupport_add b I hF
    (fun v => (a v : ℝ)) (fun v => (c v : ℝ))) u
  have hcast : (fun v => ((a + c) v : ℝ)) =
      (fun v => (a v : ℝ)) + (fun v => (c v : ℝ)) := by funext v; simp
  rw [← hcast, ← «Σ».faceSupportLattice_cast, ← «Σ».faceSupportLattice_cast,
    ← «Σ».faceSupportLattice_cast] at he
  simpa only [Pi.add_apply, Int.cast_add] using he

/-- A strictly interior original target remains strictly interior in the
exact quotient slice. Only adjacent primitive inequalities are relevant. -/
theorem quotient_slice_interior (a : Lattice n → ℝ) (h : Lattice n → ℝ)
    (x : Ambient (n - I.card))
    (hx : quotientFaceMap (displacedSupport a (I.image b) h) b I x ∈
      interior («Σ».fanPolytope a)) :
    x ∈ interior ((«Σ».completeQuotientStarFan b I hF).fanPolytope
      («Σ».faceSupport b I hF (displacedSupport a (I.image b) h))) := by
  rw [(«Σ».completeQuotientStarFan b I hF).interior_fanPolytope_eq]
  rw [«Σ».interior_fanPolytope_eq] at hx
  intro u hu
  let u' : («Σ».completeQuotientStarFan b I hF).rays := ⟨u, hu⟩
  obtain ⟨s, hs, hFs, hv, hproj⟩ := «Σ».starRayLift_spec b I hF u'
  let v := «Σ».starRayLift b I hF u'
  have hvF : v ∉ I.image b := (Finset.mem_sdiff.mp hv).2
  have hvray := «Σ».ray_mem_of_mem_cone hs (Finset.mem_sdiff.mp hv).1
  have hbound := hx v hvray
  rw [quotientFaceMap_pairing, hproj] at hbound
  have hcoeff := «Σ».faceSupport_lift b I hF (displacedSupport a (I.image b) h) u'
  change «Σ».faceSupport b I hF (displacedSupport a (I.image b) h) u =
    displacedSupport a (I.image b) h v +
      (dotProductEquiv ℝ (Fin n) (embed n v))
        (quotientFaceOrigin (displacedSupport a (I.image b) h) b I) at hcoeff
  have hvalue : displacedSupport a (I.image b) h v = a v := by
    simp only [displacedSupport, Pi.sub_apply, facetWeight, if_neg hvF, sub_zero]
  rw [hvalue] at hcoeff
  rw [hcoeff]
  linarith

end SmoothCompleteFan

end PaperVerification.ToricGeometry
end
end Source_ToricSliceCoordinates
-- END ORIGINAL PaperVerification.ToricSliceCoordinates


-- BEGIN ORIGINAL PaperVerification.ToricNearFacetParity
section Source_ToricNearFacetParity

-- original header: module

-- original header: public import PaperVerification.ToricSliceCoordinates
-- original header: public import PaperVerification.ToricCenterTargets

-- original header: @[expose] public section

/-!
# Prescribed parity at the first old-facet slice

The normal parity chooses the two heights zero and one. The actual
saturated slice polytopes share their quotient fan and have dimension
`n-1`; the induction hypothesis supplies the remaining tangent parity.
The zero-dimensional endpoint is included.
-/

noncomputable section

namespace PaperVerification.ToricGeometry

open Set
open PaperVerification.ToricExchange
open scoped BigOperators Classical Pointwise

/-- The exact mixed parity statement in a fixed dimension, used only as
an induction predicate. -/
def ParityDimensionStatement (d : ℕ) : Prop :=
  ∀ P Q : LatticePolytope d, P.Smooth → Q.Smooth → P.SameNormalFan Q →
    P.EdgesAtLeast d → Q.EdgesAtLeast d →
    ∀ m : Lattice d, embed d m ∈ interior (P.minkowskiSum Q) →
    ∀ p : Lattice d, ∃ x y : Lattice d,
      embed d x ∈ P.carrier ∧ embed d y ∈ Q.carrier ∧ x + y = m ∧ SameParity x p

namespace SmoothCompleteFan

variable {n : ℕ} («Σ» : SmoothCompleteFan n)

theorem near_facet_parity_in_basis (hpure : «Σ».IsPure)
    (a c : Lattice n → ℤ)
    (ha : «Σ».IsStrictSupport (fun v => (a v : ℝ)))
    (hc : «Σ».IsStrictSupport (fun v => (c v : ℝ)))
    (hedgesA : («Σ».supportLatticePolytope hpure a ha).EdgesAtLeast n)
    (hedgesC : («Σ».supportLatticePolytope hpure c hc).EdgesAtLeast n)
    (b : Module.Basis (Fin n) ℤ (Lattice n)) (I : Finset (Fin n))
    (u : Lattice n) (hI : I.image b = {u}) (hF : I.image b ∈ «Σ».cones)
    (m : Lattice n)
    (hm : embed n m ∈ interior («Σ».fanPolytope (fun v => ((a + c) v : ℝ))))
    (hslack : latticeSlack (a + c) m u = 1)
    (IH : ∀ d : ℕ, d < n → ParityDimensionStatement d) (p : Lattice n) :
    ∃ x y : Lattice n,
      embed n x ∈ «Σ».fanPolytope (fun v => (a v : ℝ)) ∧
      embed n y ∈ «Σ».fanPolytope (fun v => (c v : ℝ)) ∧
      x + y = m ∧ SameParity x p := by
  have hIcard : I.card = 1 := by
    rw [← Finset.card_image_of_injective I b.injective, hI, Finset.card_singleton]
  have hn : 1 ≤ n := by
    have h := Finset.card_le_card (Finset.subset_univ I)
    simpa only [hIcard, Finset.card_fin] using h
  have huF : u ∈ I.image b := by rw [hI]; exact Finset.mem_singleton_self u
  let z := latticeSlack a p u
  let ε : ℕ := (z % 2).toNat
  let η : ℕ := 1 - ε
  have hz0 : 0 ≤ z % 2 := Int.emod_nonneg z (by norm_num)
  have hz2 : z % 2 < 2 := Int.emod_lt_of_pos z (by norm_num)
  have hε : (ε : ℤ) = z % 2 := Int.toNat_of_nonneg hz0
  have hε1 : ε ≤ 1 := by omega
  have hη1 : η ≤ 1 := Nat.sub_le _ _
  have hεη : ε + η = 1 := by omega
  have hεηZ : (ε : ℤ) + (η : ℤ) = 1 := by exact_mod_cast hεη
  let hA : Lattice n → ℕ := fun _ => ε
  let hC : Lattice n → ℕ := fun _ => η
  let dA := displacedSupportLattice a (I.image b) hA
  let dC := displacedSupportLattice c (I.image b) hC
  let Ψ := «Σ».completeQuotientStarFan b I hF
  let eA := quotientFaceIntegralChart dA b I
  let eC := quotientFaceIntegralChart dC b I
  let eSum := quotientFaceIntegralChart (dA + dC) b I
  have hsumA : (∑ v ∈ I.image b, hA v) ≤ 1 := by simpa only [hI, Finset.sum_singleton, hA] using hε1
  have hsumC : (∑ v ∈ I.image b, hC v) ≤ 1 := by simpa only [hI, Finset.sum_singleton, hC] using hη1
  obtain ⟨A, hApoly, hAsm, hAfan, hAlen, hAimage⟩ :=
    «Σ».exists_displaced_facetPolytope b I hF hpure hIcard a ha hedgesA hA hsumA
  obtain ⟨C, hCpoly, hCsm, hCfan, hClen, hCimage⟩ :=
    «Σ».exists_displaced_facetPolytope b I hF hpure hIcard c hc hedgesC hC hsumC
  have hcoeffZ (v : Lattice n) : (dA + dC) v =
      (a + c) v - if v ∈ I.image b then 1 else 0 := by
    dsimp only [dA, dC, displacedSupportLattice, Pi.add_apply, hA, hC]
    split_ifs <;> omega
  have hcoeff : (fun v => ((dA + dC) v : ℝ)) =
      displacedSupport (fun v => ((a + c) v : ℝ)) (I.image b) (fun _ => 1) := by
    funext v
    rw [hcoeffZ]
    simp only [displacedSupport, Pi.sub_apply, facetWeight]
    split_ifs <;> simp
  have hmactive : ∀ i ∈ I,
      (dotProductEquiv ℝ (Fin n) (embed n (b i))) (embed n m) = -((dA + dC) (b i) : ℝ) := by
    intro i hi
    have hbi : b i = u := Finset.mem_singleton.mp (hI ▸ Finset.mem_image.mpr ⟨i, hi, rfl⟩)
    rw [hbi, normalRay_pairing_lattice, hcoeffZ, if_pos huF]
    have hz : (∑ j, u j * m j) = -((a + c) u - 1) := by
      dsimp only [latticeSlack] at hslack
      omega
    exact_mod_cast hz
  obtain ⟨mQ, hmQmap⟩ := eSum.exists_latticeMap_of_mem_range m (by
    rw [quotientFaceIntegralChart_realMap]
    exact (mem_range_quotientFaceMap_iff _ b I _).mpr hmactive)
  have hmQreal : quotientFaceMap (fun v => ((dA + dC) v : ℝ)) b I
      (embed (n - I.card) mQ) = embed n m := by
    rw [← quotientFaceIntegralChart_realMap, ← IntegralAffineEmbedding.embed_latticeMap]
    exact congrArg (embed n) hmQmap
  have hmQinterior : embed (n - I.card) mQ ∈ interior (Ψ.fanPolytope
      («Σ».faceSupport b I hF (fun v => ((dA + dC) v : ℝ)))) := by
    rw [hcoeff]
    apply «Σ».quotient_slice_interior b I hF _ (fun _ => 1)
    rw [← hcoeff, hmQreal]
    exact hm
  have hDA : «Σ».IsNef (fun v => (dA v : ℝ)) := by
    rw [displacedSupportLattice_cast]
    apply «Σ».displacedSupport_isNef_of_edges hpure a ha hedgesA _ _
      (fun v hv => Nat.cast_nonneg _)
    simpa only [hI, Finset.sum_singleton, hA] using
      (by exact_mod_cast hε1.trans hn : (ε : ℝ) ≤ n)
  have hDC : «Σ».IsNef (fun v => (dC v : ℝ)) := by
    rw [displacedSupportLattice_cast]
    apply «Σ».displacedSupport_isNef_of_edges hpure c hc hedgesC _ _
      (fun v hv => Nat.cast_nonneg _)
    simpa only [hI, Finset.sum_singleton, hC] using
      (by exact_mod_cast hη1.trans hn : (η : ℝ) ≤ n)
  have hqA := «Σ».faceSupport_isNef b I hF _ hDA
  have hqC := «Σ».faceSupport_isNef b I hF _ hDC
  have hsumSupport : «Σ».faceSupport b I hF (fun v => ((dA + dC) v : ℝ)) =
      «Σ».faceSupport b I hF (fun v => (dA v : ℝ)) +
        «Σ».faceSupport b I hF (fun v => (dC v : ℝ)) := by
    have hcast : (fun v => ((dA + dC) v : ℝ)) =
        (fun v => (dA v : ℝ)) + (fun v => (dC v : ℝ)) := by funext v; simp
    rw [hcast, «Σ».faceSupport_add]
  have hsumPoly : Ψ.fanPolytope («Σ».faceSupport b I hF
      (fun v => ((dA + dC) v : ℝ))) = A.minkowskiSum C := by
    rw [hsumSupport, Ψ.fanPolytope_add («Σ».completeQuotientStarFan_isPure hpure b I hF)
      _ _ hqA hqC, ← «Σ».faceSupportLattice_cast, ← «Σ».faceSupportLattice_cast]
    change _ = A.carrier + C.carrier
    rw [← hApoly, ← hCpoly]
  rw [hsumPoly] at hmQinterior
  obtain ⟨pQ, hpQ⟩ := quotientFace_parity_representative dA b I p (by
    intro i hi
    have hbi : b i = u := Finset.mem_singleton.mp (hI ▸ Finset.mem_image.mpr ⟨i, hi, rfl⟩)
    rw [hbi]
    refine ⟨z / 2, ?_⟩
    have hcomm : (∑ j, p j * u j) = ∑ j, u j * p j :=
      Finset.sum_congr rfl (fun j hj => mul_comm _ _)
    rw [hcomm]
    dsimp only [dA, displacedSupportLattice, hA]
    rw [if_pos huF]
    have hz : z = (∑ j, u j * p j) + a u := rfl
    omega)
  have hd : n - I.card < n := by omega
  obtain ⟨xQ, yQ, hxQ, hyQ, hxyQ, hpQ'⟩ := IH (n - I.card) hd A C hAsm hCsm
    (hAfan.trans hCfan.symm) hAlen hClen mQ hmQinterior pQ
  refine ⟨eA.latticeMap xQ, eC.latticeMap yQ, ?_, ?_, ?_, ?_⟩
  · have hx : eA.realMap (embed (n - I.card) xQ) ∈ eA.realMap '' A.carrier :=
      Set.mem_image_of_mem _ hxQ
    rw [hAimage] at hx
    simpa only [IntegralAffineEmbedding.embed_latticeMap] using hx.1
  · have hy : eC.realMap (embed (n - I.card) yQ) ∈ eC.realMap '' C.carrier :=
      Set.mem_image_of_mem _ hyQ
    rw [hCimage] at hy
    simpa only [IntegralAffineEmbedding.embed_latticeMap] using hy.1
  · rw [← quotientFaceIntegralChart_add, hxyQ]
    exact hmQmap
  · obtain ⟨v, hv⟩ := eA.sameParity_latticeMap hpQ'
    obtain ⟨w, hw⟩ := hpQ
    refine ⟨v + w, ?_⟩
    calc
      eA.latticeMap xQ - p =
          (eA.latticeMap xQ - eA.latticeMap pQ) + (eA.latticeMap pQ - p) := by abel
      _ = (v + v) + (w + w) := by rw [hv, hw]
      _ = (v + w) + (v + w) := by abel

/-- The old-facet branch of Theorem 1.2, stated for an arbitrary actual
primitive old ray and the literal integer slack. -/
theorem near_facet_parity_decomposition (hpure : «Σ».IsPure)
    (a c : Lattice n → ℤ)
    (ha : «Σ».IsStrictSupport (fun v => (a v : ℝ)))
    (hc : «Σ».IsStrictSupport (fun v => (c v : ℝ)))
    (hedgesA : («Σ».supportLatticePolytope hpure a ha).EdgesAtLeast n)
    (hedgesC : («Σ».supportLatticePolytope hpure c hc).EdgesAtLeast n)
    (u : Lattice n) (hu : u ∈ «Σ».rays)
    (m : Lattice n)
    (hm : embed n m ∈ interior («Σ».fanPolytope (fun v => ((a + c) v : ℝ))))
    (hslack : latticeSlack (a + c) m u = 1)
    (IH : ∀ d : ℕ, d < n → ParityDimensionStatement d) (p : Lattice n) :
    ∃ x y : Lattice n,
      embed n x ∈ «Σ».fanPolytope (fun v => (a v : ℝ)) ∧
      embed n y ∈ «Σ».fanPolytope (fun v => (c v : ℝ)) ∧
      x + y = m ∧ SameParity x p := by
  have hsing := «Σ».singleton_mem_of_mem_rays hu
  obtain ⟨b, I, hI⟩ := «Σ».smooth {u} hsing
  exact «Σ».near_facet_parity_in_basis hpure a c ha hc hedgesA hedgesC b I u hI.symm
    (hI ▸ hsing) m hm hslack IH p

end SmoothCompleteFan

end PaperVerification.ToricGeometry
end
end Source_ToricNearFacetParity
-- END ORIGINAL PaperVerification.ToricNearFacetParity


-- BEGIN ORIGINAL PaperVerification.ToricNearFacetAdjoint
section Source_ToricNearFacetAdjoint

-- original header: module

-- original header: public import PaperVerification.ToricNearFacetParity
-- original header: public import PaperVerification.ToricCanonicalSlices

-- original header: @[expose] public section

/-!
# Adjoint splitting at the first old-facet slice

The first summand has normal height zero and the second has normal height
one. The canonical slice identity carries an interior lattice point of the
second quotient polytope back to an interior lattice point of the original
polytope. Only the ordinary lower-dimensional mixed adjoint statement is used.
-/

noncomputable section

namespace PaperVerification.ToricGeometry

open Set
open scoped BigOperators Classical Pointwise

/-- The exact mixed adjoint statement in a fixed dimension. -/
def AdjointDimensionStatement (d : ℕ) : Prop :=
  ∀ P Q : LatticePolytope d, P.Smooth → Q.Smooth → P.SameNormalFan Q →
    P.EdgesAtLeast (d + 1) → Q.EdgesAtLeast (d + 1) →
    ∀ m : Lattice d, embed d m ∈ interior (P.minkowskiSum Q) →
    ∃ x y : Lattice d, embed d x ∈ P.carrier ∧
      embed d y ∈ interior Q.carrier ∧ x + y = m

namespace SmoothCompleteFan

variable {n : ℕ} («Σ» : SmoothCompleteFan n)

theorem near_facet_adjoint_in_basis (hpure : «Σ».IsPure)
    (a c : Lattice n → ℤ)
    (ha : «Σ».IsStrictSupport (fun v => (a v : ℝ)))
    (hc : «Σ».IsStrictSupport (fun v => (c v : ℝ)))
    (hedgesA : («Σ».supportLatticePolytope hpure a ha).EdgesAtLeast (n + 1))
    (hedgesC : («Σ».supportLatticePolytope hpure c hc).EdgesAtLeast (n + 1))
    (b : Module.Basis (Fin n) ℤ (Lattice n)) (I : Finset (Fin n))
    (u : Lattice n) (hI : I.image b = {u}) (hF : I.image b ∈ «Σ».cones)
    (m : Lattice n)
    (hm : embed n m ∈ interior («Σ».fanPolytope (fun v => ((a + c) v : ℝ))))
    (hslack : latticeSlack (a + c) m u = 1)
    (IH : ∀ d : ℕ, d < n → AdjointDimensionStatement d) :
    ∃ x y : Lattice n,
      embed n x ∈ «Σ».fanPolytope (fun v => (a v : ℝ)) ∧
      embed n y ∈ interior («Σ».fanPolytope (fun v => (c v : ℝ))) ∧ x + y = m := by
  have hIcard : I.card = 1 := by
    rw [← Finset.card_image_of_injective I b.injective, hI, Finset.card_singleton]
  have hn : 1 ≤ n := by
    have h := Finset.card_le_card (Finset.subset_univ I)
    simpa only [hIcard, Finset.card_fin] using h
  have huF : u ∈ I.image b := by rw [hI]; exact Finset.mem_singleton_self u
  let hA : Lattice n → ℕ := fun _ => 0
  let hC : Lattice n → ℕ := fun _ => 1
  let dA := displacedSupportLattice a (I.image b) hA
  let dC := displacedSupportLattice c (I.image b) hC
  let Ψ := «Σ».completeQuotientStarFan b I hF
  let eA := quotientFaceIntegralChart dA b I
  let eC := quotientFaceIntegralChart dC b I
  let eSum := quotientFaceIntegralChart (dA + dC) b I
  have hsumA : (∑ v ∈ I.image b, hA v) = 0 := by simp [hA]
  have hsumC : (∑ v ∈ I.image b, hC v) = 1 := by simp [hI, hC]
  obtain ⟨A, hApoly, hAsm, hAfan, hAlen, hAimage⟩ :=
    «Σ».exists_displaced_facePolytope b I hF hpure a ha hedgesA hA (by rw [hsumA]; omega)
  obtain ⟨C, hCpoly, hCsm, hCfan, hClen, hCimage⟩ :=
    «Σ».exists_displaced_facePolytope b I hF hpure c hc hedgesC hC (by rw [hsumC]; omega)
  have hcoeffZ (v : Lattice n) : (dA + dC) v =
      (a + c) v - if v ∈ I.image b then 1 else 0 := by
    dsimp only [dA, dC, displacedSupportLattice, Pi.add_apply, hA, hC]
    split_ifs <;> omega
  have hcoeff : (fun v => ((dA + dC) v : ℝ)) =
      displacedSupport (fun v => ((a + c) v : ℝ)) (I.image b) (fun _ => 1) := by
    funext v
    rw [hcoeffZ]
    simp only [displacedSupport, Pi.sub_apply, facetWeight]
    split_ifs <;> simp
  have hmactive : ∀ i ∈ I,
      (dotProductEquiv ℝ (Fin n) (embed n (b i))) (embed n m) = -((dA + dC) (b i) : ℝ) := by
    intro i hi
    have hbi : b i = u := Finset.mem_singleton.mp (hI ▸ Finset.mem_image.mpr ⟨i, hi, rfl⟩)
    rw [hbi, normalRay_pairing_lattice, hcoeffZ, if_pos huF]
    have hz : (∑ j, u j * m j) = -((a + c) u - 1) := by
      dsimp only [latticeSlack] at hslack
      omega
    exact_mod_cast hz
  obtain ⟨mQ, hmQmap⟩ := eSum.exists_latticeMap_of_mem_range m (by
    rw [quotientFaceIntegralChart_realMap]
    exact (mem_range_quotientFaceMap_iff _ b I _).mpr hmactive)
  have hmQreal : quotientFaceMap (fun v => ((dA + dC) v : ℝ)) b I
      (embed (n - I.card) mQ) = embed n m := by
    rw [← quotientFaceIntegralChart_realMap, ← IntegralAffineEmbedding.embed_latticeMap]
    exact congrArg (embed n) hmQmap
  have hmQinterior : embed (n - I.card) mQ ∈ interior (Ψ.fanPolytope
      («Σ».faceSupport b I hF (fun v => ((dA + dC) v : ℝ)))) := by
    rw [hcoeff]
    apply «Σ».quotient_slice_interior b I hF _ (fun _ => 1)
    rw [← hcoeff, hmQreal]
    exact hm
  have hDA : «Σ».IsNef (fun v => (dA v : ℝ)) := by
    rw [displacedSupportLattice_cast]
    apply «Σ».displacedSupport_isNef_of_edges hpure a ha hedgesA _ _
      (fun v hv => Nat.cast_nonneg _)
    simp only [hA, Nat.cast_zero, Finset.sum_const_zero]
    positivity
  have hDC : «Σ».IsNef (fun v => (dC v : ℝ)) := by
    rw [displacedSupportLattice_cast]
    apply «Σ».displacedSupport_isNef_of_edges hpure c hc hedgesC _ _
      (fun v hv => Nat.cast_nonneg _)
    simp only [hI, Finset.sum_singleton, hC, Nat.cast_one]
    exact_mod_cast (by omega : 1 ≤ n + 1)
  have hsumSupport : «Σ».faceSupport b I hF (fun v => ((dA + dC) v : ℝ)) =
      «Σ».faceSupport b I hF (fun v => (dA v : ℝ)) +
        «Σ».faceSupport b I hF (fun v => (dC v : ℝ)) := by
    have hcast : (fun v => ((dA + dC) v : ℝ)) =
        (fun v => (dA v : ℝ)) + (fun v => (dC v : ℝ)) := by funext v; simp
    rw [hcast, «Σ».faceSupport_add]
  have hsumPoly : Ψ.fanPolytope («Σ».faceSupport b I hF
      (fun v => ((dA + dC) v : ℝ))) = A.minkowskiSum C := by
    rw [hsumSupport, Ψ.fanPolytope_add («Σ».completeQuotientStarFan_isPure hpure b I hF)
      _ _ («Σ».faceSupport_isNef b I hF _ hDA) («Σ».faceSupport_isNef b I hF _ hDC),
      ← «Σ».faceSupportLattice_cast, ← «Σ».faceSupportLattice_cast]
    change _ = A.carrier + C.carrier
    rw [← hApoly, ← hCpoly]
  rw [hsumPoly] at hmQinterior
  have hd : n - I.card < n := by omega
  have hAlen' : A.EdgesAtLeast ((n - I.card) + 1) :=
    A.edgesAtLeast_mono hAlen (by rw [hsumA]; omega)
  have hClen' : C.EdgesAtLeast ((n - I.card) + 1) :=
    C.edgesAtLeast_mono hClen (by rw [hsumC]; omega)
  obtain ⟨xQ, yQ, hxQ, hyQ, hxyQ⟩ := IH (n - I.card) hd A C hAsm hCsm
    (hAfan.trans hCfan.symm) hAlen' hClen' mQ hmQinterior
  refine ⟨eA.latticeMap xQ, eC.latticeMap yQ, ?_, ?_, ?_⟩
  · have hx : eA.realMap (embed (n - I.card) xQ) ∈ eA.realMap '' A.carrier :=
      Set.mem_image_of_mem _ hxQ
    rw [hAimage] at hx
    simpa only [IntegralAffineEmbedding.embed_latticeMap] using hx.1
  · rw [hCpoly] at hyQ
    have hyadj := (Ψ.lattice_mem_interior_iff_adjointSupport
      («Σ».faceSupportLattice b I hF dC) yQ).mp hyQ
    have hycanonical : embed (n - I.card) yQ ∈ Ψ.fanPolytope
        (fun v => «Σ».faceSupport b I hF (fun v => (dC v : ℝ)) v - 1) := by
      simpa only [← «Σ».faceSupportLattice_cast, Int.cast_sub, Int.cast_one] using hyadj
    have hcanonical := «Σ».canonical_slice_eq_of_edges b I hF hpure c hc hedgesC
      (fun _ => (1 : ℝ)) (fun v hv => le_rfl) (by simp only [hI, Finset.sum_singleton]; exact_mod_cast (by omega : 1 + 1 ≤ n + 1))
    have hDCcast : (fun v => (dC v : ℝ)) =
        displacedSupport (fun v => (c v : ℝ)) (I.image b) (fun _ => 1) := by
      simpa only [hC, Nat.cast_one] using
        (displacedSupportLattice_cast c (I.image b) hC)
    rw [← hDCcast] at hcanonical
    have hyimage : eC.realMap (embed (n - I.card) yQ) ∈
        {x ∈ «Σ».fanPolytope (fun v => (c v : ℝ) - 1) | ∀ v ∈ I.image b,
          (dotProductEquiv ℝ (Fin n) (embed n v)) x + (c v : ℝ) = 1} := by
      rw [← hcanonical, quotientFaceIntegralChart_realMap]
      exact Set.mem_image_of_mem _ hycanonical
    apply («Σ».lattice_mem_interior_iff_adjointSupport c (eC.latticeMap yQ)).mpr
    simpa only [IntegralAffineEmbedding.embed_latticeMap, Int.cast_sub, Int.cast_one] using hyimage.1
  · rw [← quotientFaceIntegralChart_add, hxyQ]
    exact hmQmap

/-- The old-facet branch of Theorem 1.3 for the literal integer slack. -/
theorem near_facet_adjoint_decomposition (hpure : «Σ».IsPure)
    (a c : Lattice n → ℤ)
    (ha : «Σ».IsStrictSupport (fun v => (a v : ℝ)))
    (hc : «Σ».IsStrictSupport (fun v => (c v : ℝ)))
    (hedgesA : («Σ».supportLatticePolytope hpure a ha).EdgesAtLeast (n + 1))
    (hedgesC : («Σ».supportLatticePolytope hpure c hc).EdgesAtLeast (n + 1))
    (u : Lattice n) (hu : u ∈ «Σ».rays) (m : Lattice n)
    (hm : embed n m ∈ interior («Σ».fanPolytope (fun v => ((a + c) v : ℝ))))
    (hslack : latticeSlack (a + c) m u = 1)
    (IH : ∀ d : ℕ, d < n → AdjointDimensionStatement d) :
    ∃ x y : Lattice n,
      embed n x ∈ «Σ».fanPolytope (fun v => (a v : ℝ)) ∧
      embed n y ∈ interior («Σ».fanPolytope (fun v => (c v : ℝ))) ∧ x + y = m := by
  have hsing := «Σ».singleton_mem_of_mem_rays hu
  obtain ⟨b, I, hI⟩ := «Σ».smooth {u} hsing
  exact «Σ».near_facet_adjoint_in_basis hpure a c ha hc hedgesA hedgesC b I u hI.symm
    (hI ▸ hsing) m hm hslack IH

end SmoothCompleteFan

end PaperVerification.ToricGeometry
end
end Source_ToricNearFacetAdjoint
-- END ORIGINAL PaperVerification.ToricNearFacetAdjoint


-- BEGIN ORIGINAL PaperVerification.ToricMixedPolytopeBridges
section Source_ToricMixedPolytopeBridges

-- original header: module

-- original header: public import PaperVerification.ToricNearFacetParity
-- original header: public import PaperVerification.ToricNearFacetAdjoint
-- original header: public import PaperVerification.ToricBundleFanInduction

-- original header: @[expose] public section

/-!
# Applying the local support-coordinate proofs to the original polytopes

Reconstruction of a polytope from its actual support function does not
change its carrier, actual edges, or normal fan. These equalities eliminate
support-coordinate presentations from the hypotheses of the induction.
-/

noncomputable section

namespace PaperVerification.ToricGeometry

open Set
open scoped BigOperators Classical Pointwise
open PaperVerification.ToricExchange

namespace LatticePolytope

variable {n : ℕ} (P Q : LatticePolytope n)

theorem smooth_iff_of_carrier_eq (h : P.carrier = Q.carrier) :
    P.Smooth ↔ Q.Smooth := by
  unfold Smooth IsEdge
  rw [h]

theorem edgesAtLeast_iff_of_carrier_eq (h : P.carrier = Q.carrier) (e : ℕ) :
    P.EdgesAtLeast e ↔ Q.EdgesAtLeast e := by
  unfold EdgesAtLeast IsEdge
  rw [h]

theorem normalFan_eq_of_carrier_eq (h : P.carrier = Q.carrier) :
    P.normalFan = Q.normalFan := by
  unfold normalFan normalCone
  rw [h]

theorem supportReconstruction_carrier («Σ» : SmoothCompleteFan n) (hpure : «Σ».IsPure)
    (hfan : «Σ».realCones = P.normalFan) :
    («Σ».supportLatticePolytope hpure P.integralSupport
      (P.integralSupport_isStrictSupport «Σ» hfan)).carrier = P.carrier := by
  rw [«Σ».supportLatticePolytope_carrier,
    P.fanPolytope_integralSupport_eq «Σ» hfan]

theorem supportReconstruction_edgesAtLeast («Σ» : SmoothCompleteFan n) (hpure : «Σ».IsPure)
    (hfan : «Σ».realCones = P.normalFan) {e : ℕ} (hbound : P.EdgesAtLeast e) :
    («Σ».supportLatticePolytope hpure P.integralSupport
      (P.integralSupport_isStrictSupport «Σ» hfan)).EdgesAtLeast e :=
  ((«Σ».supportLatticePolytope hpure P.integralSupport
    (P.integralSupport_isStrictSupport «Σ» hfan)).edgesAtLeast_iff_of_carrier_eq P
      (P.supportReconstruction_carrier «Σ» hpure hfan) e).mpr hbound

end LatticePolytope

namespace SmoothCompleteFan

variable {n : ℕ} («Σ» : SmoothCompleteFan n)

theorem integralSupport_sum_polytope_eq (hpure : «Σ».IsPure)
    (P Q : LatticePolytope n)
    (hfanP : «Σ».realCones = P.normalFan) (hfanQ : «Σ».realCones = Q.normalFan) :
    «Σ».fanPolytope (fun u => ((P.integralSupport + Q.integralSupport) u : ℝ)) =
      P.minkowskiSum Q := by
  have he : (fun u => ((P.integralSupport + Q.integralSupport) u : ℝ)) =
      (fun u => (P.integralSupport u : ℝ)) +
        (fun u => (Q.integralSupport u : ℝ)) := by
    funext u
    simp
  rw [he, «Σ».fanPolytope_add hpure _ _
    (IsStrictSupport.isNef «Σ» (P.integralSupport_isStrictSupport «Σ» hfanP))
    (IsStrictSupport.isNef «Σ» (Q.integralSupport_isStrictSupport «Σ» hfanQ)),
    P.fanPolytope_integralSupport_eq «Σ» hfanP,
    Q.fanPolytope_integralSupport_eq «Σ» hfanQ]
  rfl

/-- The old-facet parity branch for the original input polytopes. Its
only recursive input is the unchanged theorem in smaller dimensions. -/
theorem polytope_near_facet_parity (hpure : «Σ».IsPure)
    (P Q : LatticePolytope n) (hP : P.Smooth) (hQ : Q.Smooth)
    (hfanP : «Σ».realCones = P.normalFan) (hfanQ : «Σ».realCones = Q.normalFan)
    (hboundP : P.EdgesAtLeast n) (hboundQ : Q.EdgesAtLeast n)
    (u : Lattice n) (hu : u ∈ «Σ».rays)
    (m : Lattice n) (hm : embed n m ∈ interior (P.minkowskiSum Q))
    (hslack : latticeSlack (P.integralSupport + Q.integralSupport) m u = 1)
    (IH : ∀ d : ℕ, d < n → ParityDimensionStatement d) (p : Lattice n) :
    ∃ x y : Lattice n,
      embed n x ∈ P.carrier ∧ embed n y ∈ Q.carrier ∧
      x + y = m ∧ SameParity x p := by
  have ha := P.integralSupport_isStrictSupport «Σ» hfanP
  have hb := Q.integralSupport_isStrictSupport «Σ» hfanQ
  have hedgesP := P.supportReconstruction_edgesAtLeast «Σ» hpure hfanP hboundP
  have hedgesQ := Q.supportReconstruction_edgesAtLeast «Σ» hpure hfanQ hboundQ
  have hm' : embed n m ∈ interior («Σ».fanPolytope
      (fun v => ((P.integralSupport + Q.integralSupport) v : ℝ))) := by
    rw [«Σ».integralSupport_sum_polytope_eq hpure P Q hfanP hfanQ]
    exact hm
  obtain ⟨x, y, hx, hy, hxy, hp⟩ := «Σ».near_facet_parity_decomposition hpure
    P.integralSupport Q.integralSupport ha hb hedgesP hedgesQ u hu m hm' hslack IH p
  exact ⟨x, y, (P.fanPolytope_integralSupport_eq «Σ» hfanP) ▸ hx,
    (Q.fanPolytope_integralSupport_eq «Σ» hfanQ) ▸ hy, hxy, hp⟩

/-- The old-facet adjoint branch retains the ambient interior condition
through the exact canonical slice identity. -/
theorem polytope_near_facet_adjoint (hpure : «Σ».IsPure)
    (P Q : LatticePolytope n) (hP : P.Smooth) (hQ : Q.Smooth)
    (hfanP : «Σ».realCones = P.normalFan) (hfanQ : «Σ».realCones = Q.normalFan)
    (hboundP : P.EdgesAtLeast (n + 1)) (hboundQ : Q.EdgesAtLeast (n + 1))
    (u : Lattice n) (hu : u ∈ «Σ».rays)
    (m : Lattice n) (hm : embed n m ∈ interior (P.minkowskiSum Q))
    (hslack : latticeSlack (P.integralSupport + Q.integralSupport) m u = 1)
    (IH : ∀ d : ℕ, d < n → AdjointDimensionStatement d) :
    ∃ x y : Lattice n,
      embed n x ∈ P.carrier ∧ embed n y ∈ interior Q.carrier ∧ x + y = m := by
  have ha := P.integralSupport_isStrictSupport «Σ» hfanP
  have hb := Q.integralSupport_isStrictSupport «Σ» hfanQ
  have hedgesP := P.supportReconstruction_edgesAtLeast «Σ» hpure hfanP hboundP
  have hedgesQ := Q.supportReconstruction_edgesAtLeast «Σ» hpure hfanQ hboundQ
  have hm' : embed n m ∈ interior («Σ».fanPolytope
      (fun v => ((P.integralSupport + Q.integralSupport) v : ℝ))) := by
    rw [«Σ».integralSupport_sum_polytope_eq hpure P Q hfanP hfanQ]
    exact hm
  obtain ⟨x, y, hx, hy, hxy⟩ := «Σ».near_facet_adjoint_decomposition hpure
    P.integralSupport Q.integralSupport ha hb hedgesP hedgesQ u hu m hm' hslack IH
  rw [P.fanPolytope_integralSupport_eq «Σ» hfanP] at hx
  rw [Q.fanPolytope_integralSupport_eq «Σ» hfanQ] at hy
  exact ⟨x, y, hx, hy, hxy⟩

/-- An empty-focus primitive relation supplies its actual saturated
bundle coordinates internally. No split-bundle presentation is assumed. -/
theorem polytope_fiber_type_parity (hpure : «Σ».IsPure)
    (P Q : LatticePolytope n) (hP : P.Smooth) (hQ : Q.Smooth)
    (hfanP : «Σ».realCones = P.normalFan) (hfanQ : «Σ».realCones = Q.normalFan)
    (hboundP : P.EdgesAtLeast n) (hboundQ : Q.EdgesAtLeast n)
    (R : «Σ».PrimitiveRelation) (hR : R.IsCombinatoriallyContractible)
    (hN : R.negative = ∅)
    (IH : ∀ d : ℕ, d < n → ParityDimensionStatement d)
    (m : Lattice n) (hm : embed n m ∈ interior (P.minkowskiSum Q)) (p : Lattice n) :
    ∃ x y : Lattice n,
      embed n x ∈ P.carrier ∧ embed n y ∈ Q.carrier ∧
      x + y = m ∧ SameParity x p :=
  R.bundleCoordinates.bundle_parity_decomposition hR hN hpure
    P Q hP hQ hfanP hfanQ hboundP hboundQ IH m hm p

theorem polytope_fiber_type_adjoint (hpure : «Σ».IsPure)
    (P Q : LatticePolytope n) (hP : P.Smooth) (hQ : Q.Smooth)
    (hfanP : «Σ».realCones = P.normalFan) (hfanQ : «Σ».realCones = Q.normalFan)
    (hboundP : P.EdgesAtLeast (n + 1)) (hboundQ : Q.EdgesAtLeast (n + 1))
    (R : «Σ».PrimitiveRelation) (hR : R.IsCombinatoriallyContractible)
    (hN : R.negative = ∅)
    (IH : ∀ d : ℕ, d < n → ∀ A B : LatticePolytope d,
      A.Smooth → B.Smooth → A.SameNormalFan B →
      A.EdgesAtLeast (d + 1) → B.EdgesAtLeast (d + 1) →
      ∀ m : Lattice d, embed d m ∈ interior (A.minkowskiSum B) →
      ∃ x y : Lattice d,
        embed d x ∈ A.carrier ∧ embed d y ∈ interior B.carrier ∧ x + y = m)
    (m : Lattice n) (hm : embed n m ∈ interior (P.minkowskiSum Q)) :
    ∃ x y : Lattice n,
      embed n x ∈ P.carrier ∧ embed n y ∈ interior Q.carrier ∧ x + y = m :=
  R.bundleCoordinates.bundle_adjoint_decomposition hR hN hpure
    P Q hP hQ hfanP hfanQ hboundP hboundQ IH m hm

end SmoothCompleteFan

end PaperVerification.ToricGeometry
end
end Source_ToricMixedPolytopeBridges
-- END ORIGINAL PaperVerification.ToricMixedPolytopeBridges


-- BEGIN ORIGINAL PaperVerification.ToricSelectedWallCounts
section Source_ToricSelectedWallCounts

-- original header: module

-- original header: public import PaperVerification.ToricSelectedDegreeEstimates

-- original header: @[expose] public section

/-!
# The complementary wall count in Proposition 5.2

Every full cone over a selected ray retains exactly `r` of the original
positive fiber rays. For a primitive pair this makes at most one common
fiber ray lie outside its actual wall. The remaining zero-coefficient wall
rays are bounded by the two actual base dimensions.
-/

noncomputable section

namespace PaperVerification.ToricGeometry

open scoped BigOperators Classical

/-- A finite-set form of the wall count. Both selected intersections are
counted inside `D`; their overlap can escape `N` only through the wall's
complement or through its zero-coefficient rays. -/
theorem two_intersections_card_le_wall_count {α : Type*} [DecidableEq α]
    (D U V W N : Finset α) (hNW : N ⊆ W) (b : ℕ)
    (hzero : (W \ N).card ≤ b) (hout : ((U ∩ V) \ W).card ≤ 1) :
    (D ∩ U).card + (D ∩ V).card ≤ D.card + (D ∩ N).card + b + 1 := by
  let C := (D ∩ U) ∩ V
  have hsub : C ⊆ (D ∩ N) ∪ (W \ N) ∪ ((U ∩ V) \ W) := by
    intro x hx
    obtain ⟨hxDU, hxV⟩ := Finset.mem_inter.mp hx
    obtain ⟨hxD, hxU⟩ := Finset.mem_inter.mp hxDU
    by_cases hxW : x ∈ W
    · by_cases hxN : x ∈ N
      · exact Finset.mem_union_left _
          (Finset.mem_union_left _ (Finset.mem_inter.mpr ⟨hxD, hxN⟩))
      · exact Finset.mem_union_left _
          (Finset.mem_union_right _ (Finset.mem_sdiff.mpr ⟨hxW, hxN⟩))
    · exact Finset.mem_union_right _
        (Finset.mem_sdiff.mpr ⟨Finset.mem_inter.mpr ⟨hxU, hxV⟩, hxW⟩)
  have hc := Finset.card_le_card hsub
  have hu1 := Finset.card_union_le ((D ∩ N) ∪ (W \ N)) ((U ∩ V) \ W)
  have hu2 := Finset.card_union_le (D ∩ N) (W \ N)
  have hC : C.card ≤ (D ∩ N).card + b + 1 := by omega
  have hUD : (D ∩ U) ∪ (D ∩ V) ⊆ D :=
    Finset.union_subset Finset.inter_subset_left Finset.inter_subset_left
  have hUcard := Finset.card_le_card hUD
  have hinter : (D ∩ U) ∩ (D ∩ V) = C := by
    ext x
    simp only [C, Finset.mem_inter]
    tauto
  have hcount := Finset.card_union_add_card_inter (D ∩ U) (D ∩ V)
  rw [hinter] at hcount
  omega

namespace SmoothCompleteFan

variable {n : ℕ} («Σ» : SmoothCompleteFan n)
variable {ι : Type*} [Fintype ι] (R : ι → «Σ».PrimitiveRelation)
variable (hR : ∀ i, (R i).IsCombinatoriallyContractible)
variable (hne : ∀ i, (R i).negative.Nonempty)
variable (hdisj : «Σ».PairwiseDisjointFoci (fun i => (R i).negative))

include hne in
theorem selected_ray_not_own_positive (i : ι) :
    «Σ».selectedRay R i ∉ (R i).positive := by
  by_cases hi : 2 ≤ (R i).negative.card
  · intro hh
    exact «Σ».sum_rays_not_mem_rays (R i).negative_cone hi ((R i).primitive.1 hh)
  · have hf := «Σ».selected_focus_of_not_blowup R hne i hi
    exact fun hh => Finset.disjoint_left.mp (R i).disjoint hh
      (hf.symm ▸ Finset.mem_singleton_self _)

include hR in
/-- Exactly the original `r` positive fiber rays occur in every full cone
above the selected locus, after all disjoint subdivisions. -/
theorem selected_positive_count_full_cone (i : ι)
    {s : Finset (Lattice n)} (hs : s ∈ («Σ».selectedFan R hne hdisj).cones)
    (hscard : s.card = n) (he : «Σ».selectedRay R i ∈ s) :
    ((R i).positive ∩ s).card = (R i).fiberDimension := by
  by_cases hi : 2 ≤ (R i).negative.card
  · let i' : «Σ».BlowupIndices R := ⟨i, hi⟩
    have hsingle := («Σ».simultaneous_cone_over_sum_iff («Σ».selectedStarFocus R)
      (fun j => (R j).negative_cone) (fun j => hne j)
      («Σ».selectedStarFocus_disjoint R hdisj) (fun j => j.property) i' he).mp hs
    obtain ⟨U, hU, hUcard, hNU, p, hp, hseq⟩ :=
      «Σ».full_star_cone_parent (R i).negative (R i).negative_cone (hne i) hi
        hsingle hscard he
    have hpP : p ∉ (R i).positive := fun hh => Finset.disjoint_left.mp (R i).disjoint hh hp
    have heP := «Σ».selected_ray_not_own_positive R hne i
    have hinter : (R i).positive ∩ s = (R i).positive ∩ U := by
      rw [hseq]
      ext v
      simp only [starRaySet, Finset.mem_inter, Finset.mem_insert, Finset.mem_erase]
      constructor
      · rintro ⟨hvP, hve | ⟨hvp, hvU⟩⟩
        · change v = «Σ».selectedRay R i at hve
          exact (heP (hve ▸ hvP)).elim
        · exact ⟨hvP, hvU⟩
      · rintro ⟨hvP, hvU⟩
        refine ⟨hvP, Or.inr ⟨?_, hvU⟩⟩
        exact fun hvp => hpP (hvp ▸ hvP)
    rw [hinter]
    exact (R i).positive_count_in_full_cone (hR i) hU hUcard hNU
  · have hf := «Σ».selected_focus_of_not_blowup R hne i hi
    have hold := («Σ».selected_divisor_cone_iff R hne hdisj i hi he).mp hs
    exact (R i).positive_count_in_full_cone (hR i) hold hscard
      (by simpa only [hf, Finset.singleton_subset_iff] using he)

include hR hne hdisj in
theorem selected_positive_missing_from_wall_card (i : ι) (W : Finset (Lattice n))
    (hs : insert («Σ».selectedRay R i) W ∈ («Σ».selectedFan R hne hdisj).cones)
    (hscard : (insert («Σ».selectedRay R i) W).card = n) :
    ((R i).positive \ W).card = 1 := by
  have hcount := «Σ».selected_positive_count_full_cone R hR hne hdisj i
    hs hscard (Finset.mem_insert_self _ _)
  have heP := «Σ».selected_ray_not_own_positive R hne i
  have hinter : (R i).positive ∩ insert («Σ».selectedRay R i) W = (R i).positive ∩ W := by
    ext v
    simp only [Finset.mem_inter, Finset.mem_insert]
    constructor
    · rintro ⟨hvP, hve | hvW⟩
      · exact (heP (hve ▸ hvP)).elim
      · exact ⟨hvP, hvW⟩
    · rintro ⟨hvP, hvW⟩
      exact ⟨hvP, Or.inr hvW⟩
  rw [hinter] at hcount
  have hsplit := Finset.card_sdiff_add_card_inter (R i).positive W
  have htotal := (R i).positive_card_eq_fiberDimension_add_one
  omega

include hR in
/-- The weighted negative-wall estimate used for the complementary
two-positive bound. `D` may be any collection of at most `n` old rays. -/
theorem selected_pair_negative_weight_bound (hpure : «Σ».IsPure)
    (S : («Σ».selectedFan R hne hdisj).PrimitiveRelation)
    (hS : S.IsCombinatoriallyContractible) (i j : ι) (hij : i ≠ j)
    (hi : «Σ».selectedRay R i ∈ S.positive)
    (hj : «Σ».selectedRay R j ∈ S.positive)
    (D : Finset (Lattice n)) (hDcard : D.card ≤ n) :
    (((D ∩ (R i).positive).card : ℝ) + ((D ∩ (R j).positive).card : ℝ) -
      n - «Σ».selectedBaseDimension R i - «Σ».selectedBaseDimension R j - 1) ≤
      S.negativeWeightOn D := by
  have hP := «Σ».primitive_selected_pair_eq R hne hdisj S.primitive i j hij hi hj
  have hef := («Σ».selectedRay_injective R hdisj).ne hij
  have hΓpure := «Σ».isPure_simultaneousSubdivision («Σ».selectedStarFocus R) hpure
    (fun k => (R k).negative_cone) (fun k => hne k) («Σ».selectedStarFocus_disjoint R hdisj)
  obtain ⟨W, hWP, hNW, hfirst, hfirstcard, hsecond, hsecondcard⟩ :=
    S.exists_full_pair_wall hΓpure hS («Σ».selectedRay R i) («Σ».selectedRay R j) hef hP
  have heW : «Σ».selectedRay R i ∉ W := fun hh => Finset.disjoint_left.mp hWP hh hi
  have hWcard : W.card + 1 = n := by
    simpa only [Finset.card_insert_of_notMem heW] using hfirstcard
  have hqbound := («Σ».selected_two_positive_card_bound R hR hne hdisj
    hpure S hS i j hij hi hj).2
  have hzero : (W \ S.negative).card ≤
      «Σ».selectedBaseDimension R i + «Σ».selectedBaseDimension R j := by
    have hsplit := Finset.card_sdiff_add_card_eq_card hNW
    omega
  have hout : (((R i).positive ∩ (R j).positive) \ W).card ≤ 1 := by
    have hsub : ((R i).positive ∩ (R j).positive) \ W ⊆ (R i).positive \ W := by
      intro v hv
      obtain ⟨hvP, hvW⟩ := Finset.mem_sdiff.mp hv
      exact Finset.mem_sdiff.mpr ⟨(Finset.mem_inter.mp hvP).1, hvW⟩
    have hh := Finset.card_le_card hsub
    rw [«Σ».selected_positive_missing_from_wall_card R hR hne hdisj i W hfirst hfirstcard] at hh
    exact hh
  have hcount := two_intersections_card_le_wall_count D (R i).positive (R j).positive
    W S.negative hNW («Σ».selectedBaseDimension R i + «Σ».selectedBaseDimension R j)
    hzero hout
  have hcount' : (D ∩ (R i).positive).card + (D ∩ (R j).positive).card ≤
      n + (S.negative ∩ D).card + «Σ».selectedBaseDimension R i +
        «Σ».selectedBaseDimension R j + 1 := by
    rw [Finset.inter_comm D S.negative] at hcount
    omega
  have hcountR : ((D ∩ (R i).positive).card : ℝ) + ((D ∩ (R j).positive).card : ℝ) ≤
      (n : ℝ) + ((S.negative ∩ D).card : ℝ) + «Σ».selectedBaseDimension R i +
        «Σ».selectedBaseDimension R j + 1 := by exact_mod_cast hcount'
  have hweight := S.card_negative_inter_le_weight D
  linarith

theorem outside_cone_avoids_selected_rays {σ D : Finset (Lattice n)}
    (hσ : σ ∈ «Σ».cones) (hD : D ⊆ σ)
    (houtside : ∀ i, ¬ (R i).negative ⊆ σ) :
    ∀ i, «Σ».selectedRay R i ∉ D := by
  intro i hi
  exact houtside i ((«Σ».sum_rays_mem_cone_iff (R i).negative_cone hσ).mp
    (latticeRayCone_generator σ (hD hi)))

theorem outside_focus_selection_card_bound {σ D : Finset (Lattice n)}
    (hD : D ⊆ σ) (houtside : ∀ i, ¬ (R i).negative ⊆ σ) (i : ι) :
    ((R i).negative ∩ D).card + 1 ≤ (R i).negative.card := by
  have hproper : (R i).negative ∩ D ⊂ (R i).negative := by
    refine Finset.ssubset_iff_subset_ne.mpr ⟨Finset.inter_subset_left, ?_⟩
    intro heq
    exact houtside i (by
      rw [← heq]
      exact Finset.inter_subset_right.trans hD)
  exact Finset.card_lt_card hproper

end SmoothCompleteFan

end PaperVerification.ToricGeometry
end
end Source_ToricSelectedWallCounts
-- END ORIGINAL PaperVerification.ToricSelectedWallCounts


-- BEGIN ORIGINAL PaperVerification.ToricOutsideBoxNef
section Source_ToricOutsideBoxNef

-- original header: module

-- original header: public import PaperVerification.ToricSelectedWallCounts
-- original header: public import PaperVerification.ToricSelectedCenterCriterion

-- original header: @[expose] public section

/-!
# The full corrected nefness argument for original side-two boxes

The two-positive case uses both independent lower bounds. One comes from
the correction-height budget and the other from the actual negative-wall
count. No positive degree or box containment is included in the hypotheses.
-/

noncomputable section

namespace PaperVerification.ToricGeometry

open scoped BigOperators Classical

namespace SmoothCompleteFan

variable {n : ℕ} («Σ» : SmoothCompleteFan n)
variable {ι : Type*} [Fintype ι] (R : ι → «Σ».PrimitiveRelation)
variable (hR : ∀ i, (R i).IsCombinatoriallyContractible)
variable (hne : ∀ i, (R i).negative.Nonempty)
variable (hdisj : «Σ».PairwiseDisjointFoci (fun i => (R i).negative))

include hR in
/-- Proposition 5.2's corrected support is genuinely nef. The family is
the finite family of activated old contractible relations; the exact
ceiling construction supplies the displayed scalar repair and budgets. -/
theorem outside_side_two_corrected_isNef
    (hpure : «Σ».IsPure) (P : LatticePolytope n) (hP : P.Smooth)
    (hfan : «Σ».realCones = P.normalFan) (hbound : P.EdgesAtLeast n)
    (σ D : Finset (Lattice n)) (hσ : σ ∈ «Σ».cones) (hDσ : D ⊆ σ)
    (houtside : ∀ i, ¬ (R i).negative ⊆ σ)
    (τ : ι → ℝ) (hτ0 : ∀ i, 0 ≤ τ i)
    (hτfiber : ∀ i, τ i ≤ 2 * ((R i).fiberDimension : ℝ) - n)
    (hτbudget : ∀ i, τ i ≤ 2 * ((D ∩ (R i).positive).card : ℝ) -
      2 * (((R i).negative ∩ D).card : ℝ) - n)
    (hrepair : ∀ i, 0 ≤
      (R i).degree (fun v => (P.integralSupport v : ℝ) -
        2 * (if v ∈ D then 1 else 0)) +
      ((R i).minimumCoefficient (hne i) : ℝ) * τ i)
    (hinactive : ∀ Q : «Σ».PrimitiveRelation, Q.IsCombinatoriallyContractible →
      (∀ i, Q.positive ≠ (R i).positive) →
      0 ≤ Q.degree (fun v => (P.integralSupport v : ℝ) -
        2 * (if v ∈ D then 1 else 0))) :
    («Σ».selectedFan R hne hdisj).IsNef
      (simultaneousSupport (fun i => (R i).negative)
        (fun v => (P.integralSupport v : ℝ) - 2 * (if v ∈ D then 1 else 0)) τ) := by
  let Γ := «Σ».selectedFan R hne hdisj
  let a : Lattice n → ℝ := fun v => (P.integralSupport v : ℝ)
  let F := simultaneousSupport (fun i => (R i).negative)
    (fun v => a v - 2 * (if v ∈ D then 1 else 0)) τ
  let u := «Σ».selectedCorrectionWeight R 0 2 D τ
  have hD := «Σ».outside_cone_avoids_selected_rays R hσ hDσ houtside
  have hformula : F = fun v => «Σ».selectedPullback R a v -
      2 * (if v ∈ D then 1 else 0) -
      ∑ i, if v = «Σ».selectedRay R i then u i else 0 := by
    simpa only [F, sub_zero] using
      «Σ».selected_support_coefficient_formula R hne hdisj a 0 2 D hD τ
  have hu (i : ι) : u i = 2 * (((R i).negative ∩ D).card : ℝ) + τ i := by
    simp only [u, selectedCorrectionWeight, zero_mul, zero_add]
  have hk (i : ι) : (((R i).negative ∩ D).card : ℝ) + 1 ≤ (R i).negative.card := by
    exact_mod_cast «Σ».outside_focus_selection_card_bound R hDσ houtside i
  have hdim (i : ι) : (n : ℝ) = (R i).fiberDimension + (R i).negative.card +
      «Σ».selectedBaseDimension R i := by exact_mod_cast «Σ».selected_dimension_eq R hR i
  have hΓpure : Γ.IsPure := «Σ».isPure_simultaneousSubdivision
    («Σ».selectedStarFocus R) hpure (fun i => (R i).negative_cone)
    (fun i => hne i) («Σ».selectedStarFocus_disjoint R hdisj)
  obtain ⟨H, hH⟩ := «Σ».exists_integral_strictSupport_simultaneousSubdivision
    («Σ».selectedStarFocus R) (fun i => (R i).negative_cone)
    (fun i => hne i) («Σ».selectedStarFocus_disjoint R hdisj)
    (fun i => i.property) P.integralSupport
    (P.integralSupport_isStrictSupport «Σ» hfan)
  apply (Γ.isNef_iff_extremal_primitive_nonneg hΓpure H hH F).mpr
  intro S hSext
  have hS := S.combinatoriallyContractible_of_extremal hSext
  by_cases hex : ∃ i, «Σ».selectedRay R i ∈ S.positive
  · obtain ⟨i, hi⟩ := hex
    have hB := «Σ».selected_positive_pullback_degree_lower_bound R hne hdisj
      hpure P hP hfan hbound S hS ⟨i, hi⟩
    by_cases hexj : ∃ j, j ≠ i ∧ «Σ».selectedRay R j ∈ S.positive
    · obtain ⟨j, hji, hj⟩ := hexj
      have hij := hji.symm
      have hdeg := «Σ».selected_two_positive_degree_bound R hne hdisj S hS i j hij hi hj
        («Σ».selectedPullback R a) (n : ℝ) 0 2 le_rfl hB D hD u
      have hdeg' : (n : ℝ) + 2 * S.negativeWeightOn D - u i - u j ≤ S.degree F := by
        simpa only [hformula, sub_zero, mul_zero, zero_mul, add_zero] using hdeg
      rw [hu i, hu j] at hdeg'
      have hfirst : 2 * ((«Σ».selectedBaseDimension R i : ℝ) +
          «Σ».selectedBaseDimension R j) + 4 - n ≤ S.degree F := by
        have hns := S.negativeWeightOn_nonneg D
        have hki := hk i
        have hkj := hk j
        have hti := hτfiber i
        have htj := hτfiber j
        have hdi := hdim i
        have hdj := hdim j
        linarith
      have hweight := «Σ».selected_pair_negative_weight_bound R hR hne hdisj
        hpure S hS i j hij hi hj D ((Finset.card_le_card hDσ).trans («Σ».card_cone_le hσ))
      have hsecond : (n : ℝ) - 2 * ((«Σ».selectedBaseDimension R i : ℝ) +
          «Σ».selectedBaseDimension R j) - 2 ≤ S.degree F := by
        have hti := hτbudget i
        have htj := hτbudget j
        linarith
      exact zero_le_one.trans (outside_box_two_positive_bound n
        ((«Σ».selectedBaseDimension R i : ℝ) + «Σ».selectedBaseDimension R j)
        (S.degree F) hfirst hsecond)
    · have hother : ∀ j, j ≠ i → «Σ».selectedRay R j ∉ S.positive := by
        intro j hji hj
        exact hexj ⟨j, hji, hj⟩
      have hdeg := «Σ».selected_one_positive_degree_bound R hR hne hdisj S hS i hi hother
        («Σ».selectedPullback R a) (n : ℝ) 0 2 le_rfl (by norm_num) hB D hD u
      have hdeg' : (n : ℝ) - 2 * ((«Σ».selectedBaseDimension R i : ℝ) + 1) - u i ≤
          S.degree F := by
        simpa only [hformula, sub_zero, mul_zero, zero_mul] using hdeg
      rw [hu i] at hdeg'
      have hki := hk i
      have hti := hτfiber i
      have hdi := hdim i
      linarith
  · have hnone : ∀ i, «Σ».selectedRay R i ∉ S.positive := by
      simpa only [not_exists] using hex
    exact «Σ».selected_no_positive_degree_nonneg R hR hne hdisj
      (fun v => a v - 2 * (if v ∈ D then 1 else 0)) τ hτ0 hrepair
      (fun Q hQ hpos hother => hinactive Q hQ hother) S hS hnone

end SmoothCompleteFan

end PaperVerification.ToricGeometry
end
end Source_ToricOutsideBoxNef
-- END ORIGINAL PaperVerification.ToricOutsideBoxNef


