module

public import Lean.Elab.BuiltinEvalCommand
public meta import Lean.Elab.BuiltinEvalCommand
public import Lean.Util.CollectAxioms
public meta import Lean.Util.CollectAxioms
public import Lean.Util.FoldConsts
public meta import Lean.Util.FoldConsts
public import Mathlib.Analysis.Convex.Intrinsic
public import Mathlib.Topology.Algebra.ConstMulAction
public import Mathlib.Topology.Algebra.Group.Pointwise
public import paper_verification.toric001
public import paper_verification.toric002
public import paper_verification.toric005
public import paper_verification.toric017
public import paper_verification.toric018
public import paper_verification.toric019
public import paper_verification.toric020
public import paper_verification.toric021

@[expose] public section


-- BEGIN ORIGINAL PaperVerification.ToricOutsideInnerBoxNef
section Source_ToricOutsideInnerBoxNef

-- original header: module

-- original header: public import PaperVerification.ToricOutsideBoxNef

-- original header: @[expose] public section

/-!
# Corrected nefness for the inner unit boxes

This is the actual degree calculation in Section 7.2, including the
canonical coefficient, the old selected ray coefficients, and every
activated selected-divisor correction.
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
theorem outside_inner_unit_corrected_isNef
    (hpure : «Σ».IsPure) (P : LatticePolytope n) (hP : P.Smooth)
    (hfan : «Σ».realCones = P.normalFan) (hbound : P.EdgesAtLeast (n + 1))
    (σ D : Finset (Lattice n)) (hσ : σ ∈ «Σ».cones) (hDσ : D ⊆ σ)
    (houtside : ∀ i, ¬ (R i).negative ⊆ σ)
    (τ : ι → ℝ) (hτ0 : ∀ i, 0 ≤ τ i)
    (hτupper : ∀ i, τ i ≤ 2 * ((R i).fiberDimension : ℝ) - n - (R i).negative.card)
    (hrepair : ∀ i, 0 ≤
      (R i).degree (fun v => (P.integralSupport v : ℝ) - 1 -
        (if v ∈ D then 1 else 0)) +
      ((R i).minimumCoefficient (hne i) : ℝ) * τ i)
    (hinactive : ∀ Q : «Σ».PrimitiveRelation, Q.IsCombinatoriallyContractible →
      (∀ i, Q.positive ≠ (R i).positive) →
      0 ≤ Q.degree (fun v => (P.integralSupport v : ℝ) - 1 -
        (if v ∈ D then 1 else 0))) :
    («Σ».selectedFan R hne hdisj).IsNef
      (simultaneousSupport (fun i => (R i).negative)
        (fun v => (P.integralSupport v : ℝ) - 1 - (if v ∈ D then 1 else 0)) τ) := by
  let Γ := «Σ».selectedFan R hne hdisj
  let a : Lattice n → ℝ := fun v => (P.integralSupport v : ℝ)
  let F := simultaneousSupport (fun i => (R i).negative)
    (fun v => a v - 1 - (if v ∈ D then 1 else 0)) τ
  let u := «Σ».selectedCorrectionWeight R 1 1 D τ
  have hD := «Σ».outside_cone_avoids_selected_rays R hσ hDσ houtside
  have hformula : F = fun v => «Σ».selectedPullback R a v - 1 -
      (if v ∈ D then 1 else 0) -
      ∑ i, if v = «Σ».selectedRay R i then u i else 0 := by
    simpa only [F, one_mul] using
      «Σ».selected_support_coefficient_formula R hne hdisj a 1 1 D hD τ
  have hu (i : ι) : u i = ((R i).negative.card : ℝ) - 1 +
      (((R i).negative ∩ D).card : ℝ) + τ i := by
    simp only [u, selectedCorrectionWeight, one_mul]
  have hk (i : ι) : (((R i).negative ∩ D).card : ℝ) + 1 ≤ (R i).negative.card := by
    exact_mod_cast «Σ».outside_focus_selection_card_bound R hDσ houtside i
  have hdim (i : ι) : (n : ℝ) = (R i).fiberDimension + (R i).negative.card +
      «Σ».selectedBaseDimension R i := by exact_mod_cast «Σ».selected_dimension_eq R hR i
  have hr (i : ι) : ((R i).fiberDimension : ℝ) ≤ n := by
    have hh := (R i).contractible_dimension_bound (hR i)
    exact_mod_cast (show (R i).fiberDimension ≤ n by omega)
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
        («Σ».selectedPullback R a) ((n + 1 : ℕ) : ℝ) 1 1 zero_le_one hB D hD u
      have hdeg' : (n : ℝ) - 1 + S.negative.card + S.negativeWeightOn D -
          u i - u j ≤ S.degree F := by
        have hh : ((n + 1 : ℕ) : ℝ) - 2 + S.negative.card + S.negativeWeightOn D -
            u i - u j ≤ S.degree F := by
          simpa only [hformula, one_mul, mul_one] using hdeg
        norm_num only [Nat.cast_add, Nat.cast_one] at hh
        linarith
      rw [hu i, hu j] at hdeg'
      have hcard := («Σ».selected_two_positive_card_bound R hR hne hdisj
        hpure S hS i j hij hi hj).2
      have hcardR : (n : ℝ) ≤ (S.negative.card : ℝ) +
          «Σ».selectedBaseDimension R i + «Σ».selectedBaseDimension R j + 1 := by
        exact_mod_cast hcard
      have hns := S.negativeWeightOn_nonneg D
      have hki := hk i
      have hkj := hk j
      have hti := hτupper i
      have htj := hτupper j
      have hdi := hdim i
      have hdj := hdim j
      have hri := hr i
      have hrj := hr j
      linarith
    · have hother : ∀ j, j ≠ i → «Σ».selectedRay R j ∉ S.positive := by
        intro j hji hj
        exact hexj ⟨j, hji, hj⟩
      have hdeg := «Σ».selected_one_positive_degree_bound R hR hne hdisj S hS i hi hother
        («Σ».selectedPullback R a) ((n + 1 : ℕ) : ℝ) 1 1 zero_le_one zero_le_one hB D hD u
      have hdeg' : (n : ℝ) - 2 * «Σ».selectedBaseDimension R i - 2 - u i ≤ S.degree F := by
        have hh : ((n + 1 : ℕ) : ℝ) - ((«Σ».selectedBaseDimension R i : ℝ) + 2) -
            ((«Σ».selectedBaseDimension R i : ℝ) + 1) - u i =
            (n : ℝ) - 2 * «Σ».selectedBaseDimension R i - 2 - u i := by
          push_cast
          ring
        simpa only [hformula, one_mul, hh] using hdeg
      rw [hu i] at hdeg'
      have hki := hk i
      have hti := hτupper i
      have hdi := hdim i
      have hq : (0 : ℝ) ≤ (R i).negative.card := Nat.cast_nonneg _
      linarith
  · have hnone : ∀ i, «Σ».selectedRay R i ∉ S.positive := by
      simpa only [not_exists] using hex
    exact «Σ».selected_no_positive_degree_nonneg R hR hne hdisj
      (fun v => a v - 1 - (if v ∈ D then 1 else 0)) τ hτ0 hrepair
      (fun Q hQ hpos hother => hinactive Q hQ hother) S hS hnone

end SmoothCompleteFan

end PaperVerification.ToricGeometry
end
end Source_ToricOutsideInnerBoxNef
-- END ORIGINAL PaperVerification.ToricOutsideInnerBoxNef


-- BEGIN ORIGINAL PaperVerification.ToricNefBoxGeometry
section Source_ToricNefBoxGeometry

-- original header: module

-- original header: public import PaperVerification.ToricOutsideInnerBoxNef
-- original header: public import PaperVerification.ToricAdjointSupport

-- original header: @[expose] public section

/-!
# From the corrected support to actual boxes

The supporting linear form furnished by genuine nefness identifies the
actual coordinate corner. Old-ray coefficient inequalities then put the
point in the original halfspaces. A coordinatewise linear minimization
proves containment of the entire real box.
-/

noncomputable section

namespace PaperVerification.ToricGeometry

open Set
open scoped BigOperators Classical

namespace SmoothCompleteFan

variable {n : ℕ} («Σ» : SmoothCompleteFan n)

theorem point_mem_fanPolytope_of_refinement_nef
    (Γ : SmoothCompleteFan n) (hrays : «Σ».rays ⊆ Γ.rays)
    (a F : Lattice n → ℝ) (hF : Γ.IsNef F)
    (d : Module.Basis (Fin n) ℤ (Lattice n))
    (hd : Finset.univ.image d ∈ Γ.cones) (x : Ambient n)
    (hactive : ∀ i, (dotProductEquiv ℝ (Fin n) (embed n (d i))) x = -F (d i))
    (hle : ∀ u ∈ «Σ».rays, F u ≤ a u) : x ∈ «Σ».fanPolytope a := by
  obtain ⟨ℓ, he, hbound⟩ := hF (Finset.univ.image d) hd
  let q : Ambient n →ₗ[ℝ] ℝ := -(dotProductEquiv ℝ (Fin n) x)
  have hq (u : Lattice n) :
      q (embed n u) = -(dotProductEquiv ℝ (Fin n) (embed n u)) x := by
    simp only [q, LinearMap.neg_apply]
    congr 1
    exact dotProduct_comm x (embed n u)
  have hℓq : ℓ = q := by
    apply (integralBasisReal d).ext
    intro i
    rw [integralBasisReal_apply, he _ (Finset.mem_image.mpr
      ⟨i, Finset.mem_univ i, rfl⟩), hq, hactive i, neg_neg]
  intro u hu
  have hh := hbound u (hrays hu)
  rw [hℓq, hq] at hh
  have hu' := hle u hu
  linarith

theorem box_corner_mem_of_refinement_nef
    (Γ : SmoothCompleteFan n) (hrays : «Σ».rays ⊆ Γ.rays)
    (a F : Lattice n → ℝ) (hF : Γ.IsNef F)
    (d : Module.Basis (Fin n) ℤ (Lattice n))
    (hd : Finset.univ.image d ∈ Γ.cones) (v : Ambient n)
    (hv : ∀ i, (dotProductEquiv ℝ (Fin n) (embed n (d i))) v = -a (d i))
    (I : Finset (Fin n)) (side : ℝ)
    (hcoeff : ∀ i, F (d i) = a (d i) - side * (if i ∈ I then 1 else 0))
    (hle : ∀ u ∈ «Σ».rays, F u ≤ a u) :
    v + side • (∑ i ∈ I, integralBasisReal (integralDualBasis d) i) ∈
      «Σ».fanPolytope a := by
  apply «Σ».point_mem_fanPolytope_of_refinement_nef Γ hrays a F hF d hd _ ?_ hle
  intro i
  rw [map_add, map_smul, map_sum, hv i, hcoeff i]
  simp only [LatticePolytope.normal_basis_dual_pairing, Finset.sum_ite_eq', smul_eq_mul]
  split_ifs <;> ring

/-- The entire box lies in the literal ray halfspaces as soon as each of
its finitely many corners does. -/
theorem box_mem_fanPolytope_of_vertices
    (a : Lattice n → ℝ) (v : Ambient n) (b : Fin n → Ambient n)
    (side : ℝ) (hside : 0 ≤ side)
    (hvertices : ∀ I : Finset (Fin n), v + side • (∑ i ∈ I, b i) ∈ «Σ».fanPolytope a)
    (t : Fin n → ℝ) (ht : ∀ i, 0 ≤ t i ∧ t i ≤ side) :
    v + ∑ i, t i • b i ∈ «Σ».fanPolytope a := by
  intro u hu
  let f : Ambient n →ₗ[ℝ] ℝ := dotProductEquiv ℝ (Fin n) (embed n u)
  let I := Finset.univ.filter (fun i => f (b i) < 0)
  have hc := hvertices I u hu
  apply hc.trans
  change f (v + side • (∑ i ∈ I, b i)) ≤ f (v + ∑ i, t i • b i)
  simp only [map_add, map_smul, map_sum, smul_eq_mul]
  refine add_le_add le_rfl ?_
  rw [Finset.mul_sum]
  calc
    (∑ i ∈ I, side * f (b i)) =
        ∑ i, if i ∈ I then side * f (b i) else 0 := by simp
    _ ≤ ∑ i, t i * f (b i) := by
      apply Finset.sum_le_sum
      intro i hi
      by_cases hiI : i ∈ I
      · rw [if_pos hiI]
        exact mul_le_mul_of_nonpos_right (ht i).2 (Finset.mem_filter.mp hiI).2.le
      · rw [if_neg hiI]
        have hfi : 0 ≤ f (b i) := by
          simpa only [I, Finset.mem_filter, Finset.mem_univ, true_and, not_lt] using hiI
        exact mul_nonneg (ht i).1 hfi

theorem fanPolytope_sub_pos_subset_interior (a : Lattice n → ℝ)
    (c : ℝ) (hc : 0 < c) :
    «Σ».fanPolytope (fun u => a u - c) ⊆ interior («Σ».fanPolytope a) := by
  intro x hx
  rw [«Σ».interior_fanPolytope_eq]
  intro u hu
  have hh := hx u hu
  change -(a u - c) ≤ _ at hh
  linarith

variable {ι : Type*} [Fintype ι] (R : ι → «Σ».PrimitiveRelation)
variable (hne : ∀ i, (R i).negative.Nonempty)
variable (hdisj : «Σ».PairwiseDisjointFoci (fun i => (R i).negative))

theorem old_rays_subset_selected : «Σ».rays ⊆ («Σ».selectedFan R hne hdisj).rays := by
  intro v hv
  exact «Σ».simultaneous_old_ray_mem_rays («Σ».selectedStarFocus R)
    (fun i => (R i).negative_cone) (fun i => hne i)
    («Σ».selectedStarFocus_disjoint R hdisj) (fun i => i.property) hv

theorem selectedPullback_old_ray (a : Lattice n → ℝ)
    {v : Lattice n} (hv : v ∈ «Σ».rays) : «Σ».selectedPullback R a v = a v :=
  «Σ».simultaneousSupport_old («Σ».selectedStarFocus R)
    (fun i => (R i).negative_cone) (fun i => i.property) a 0 v hv

include hne hdisj in
theorem selected_support_le_old_on_rays (a : Lattice n → ℝ)
    (t : ι → ℝ) (ht : ∀ i, 0 ≤ t i) {v : Lattice n} (hv : v ∈ «Σ».rays) :
    simultaneousSupport (fun i => (R i).negative) a t v ≤ a v := by
  rw [«Σ».selectedSupport_eq_pullback_sub R hne hdisj a t]
  change «Σ».selectedPullback R a v -
    (∑ i, if v = «Σ».selectedRay R i then t i else 0) ≤ a v
  rw [«Σ».selectedPullback_old_ray R a hv]
  exact sub_le_self _ (Finset.sum_nonneg (fun i hi => by
    split_ifs
    · exact ht i
    · exact le_rfl))

theorem outside_cone_mem_selected {σ : Finset (Lattice n)} (hσ : σ ∈ «Σ».cones)
    (houtside : ∀ i, ¬ (R i).negative ⊆ σ) :
    σ ∈ («Σ».selectedFan R hne hdisj).cones :=
  «Σ».mem_simultaneousSubdivision_of_unchanged («Σ».selectedStarFocus R)
    (fun i => (R i).negative_cone) (fun i => hne i)
    («Σ».selectedStarFocus_disjoint R hdisj) hσ (fun i => houtside i)

theorem selected_support_eq_old_on_outside_cone
    (a : Lattice n → ℝ) (t : ι → ℝ) {σ : Finset (Lattice n)}
    (hσ : σ ∈ «Σ».cones) (houtside : ∀ i, ¬ (R i).negative ⊆ σ)
    {v : Lattice n} (hv : v ∈ σ) :
    simultaneousSupport (fun i => (R i).negative) a t v = a v := by
  apply simultaneousSupport_of_not_sum
  intro i hve
  apply houtside i
  apply («Σ».sum_rays_mem_cone_iff (R i).negative_cone hσ).mp
  exact latticeRayCone_generator σ (hve ▸ hv)

end SmoothCompleteFan

end PaperVerification.ToricGeometry
end
end Source_ToricNefBoxGeometry
-- END ORIGINAL PaperVerification.ToricNefBoxGeometry


-- BEGIN ORIGINAL PaperVerification.ToricSelectedCharts
section Source_ToricSelectedCharts

-- original header: module

-- original header: public import PaperVerification.ToricSelectedLoci
-- original header: public import PaperVerification.ToricNefBoxGeometry
-- original header: public import PaperVerification.ToricFanPolytopeSmoothness

-- original header: @[expose] public section

/-!
# All full cones of the selected fan

Every full cone is either an unchanged cone outside the selected loci or
an actual integral star chart at exactly one selected locus. A focus with
one ray is included as the identity star chart.
-/

noncomputable section

namespace PaperVerification.ToricGeometry

open scoped BigOperators Classical

theorem integralDualBasis_starRayBasis {n : ℕ}
    (b : Module.Basis (Fin n) ℤ (Lattice n))
    (I : Finset (Fin n)) (j : Fin n) (hj : j ∈ I) :
    integralDualBasis (starRayBasis b I j) =
      starShearBasis (integralDualBasis b) I j := by
  have h := congrArg integralDualBasis
    (integralDualBasis_starShearBasis (integralDualBasis b) I j hj)
  simpa only [integralDualBasis_involutive] using h.symm

theorem integralBasisReal_dual_starRayBasis {n : ℕ}
    (b : Module.Basis (Fin n) ℤ (Lattice n))
    (I : Finset (Fin n)) (j : Fin n) (hj : j ∈ I) :
    integralBasisReal (integralDualBasis (starRayBasis b I j)) =
      starShearBasis (integralBasisReal (integralDualBasis b)) I j := by
  rw [integralDualBasis_starRayBasis b I j hj, integralBasisReal_starShearBasis]

namespace SmoothCompleteFan

variable {n : ℕ} («Σ» : SmoothCompleteFan n)
variable {ι : Type*} [Fintype ι] (R : ι → «Σ».PrimitiveRelation)
variable (hne : ∀ i, (R i).negative.Nonempty)
variable (hdisj : «Σ».PairwiseDisjointFoci (fun i => (R i).negative))

theorem selected_full_cone_chart
    (s : («Σ».selectedFan R hne hdisj).fullCones) :
    ((s : Finset (Lattice n)) ∈ «Σ».cones ∧
      ∀ i, ¬ (R i).negative ⊆ (s : Finset (Lattice n))) ∨
    ∃ (i : ι) (b : Module.Basis (Fin n) ℤ (Lattice n))
      (I : Finset (Fin n)) (j : Fin n),
      Finset.univ.image b ∈ «Σ».cones ∧ I.image b = (R i).negative ∧
      j ∈ I ∧ (s : Finset (Lattice n)) =
        Finset.univ.image (starRayBasis b I j) := by
  let Γ := «Σ».selectedFan R hne hdisj
  have hs : (s : Finset (Lattice n)) ∈ Γ.cones := Γ.fullCones_mem s
  have hcard : (s : Finset (Lattice n)).card = n := Γ.fullCones_card s
  by_cases hex : ∃ i, «Σ».selectedRay R i ∈ (s : Finset (Lattice n))
  · obtain ⟨i, hi⟩ := hex
    right
    by_cases hqi : 2 ≤ (R i).negative.card
    · let i' : «Σ».BlowupIndices R := ⟨i, hqi⟩
      have hsingle := («Σ».simultaneous_cone_over_sum_iff («Σ».selectedStarFocus R)
        (fun k => (R k).negative_cone) (fun k => hne k)
        («Σ».selectedStarFocus_disjoint R hdisj) (fun k => k.property) i' hi).mp hs
      obtain ⟨U, hU, hUcard, hNU, p, hp, hseq⟩ :=
        «Σ».full_star_cone_parent (R i).negative (R i).negative_cone (hne i)
          hqi hsingle hcard hi
      obtain ⟨b, hUb⟩ := «Σ».full_cone_basis hU hUcard
      let I := basisRayIndices b (R i).negative
      have hI : I.image b = (R i).negative :=
        image_basisRayIndices b _ (hUb ▸ hNU)
      obtain ⟨j, hj, hbj⟩ := Finset.mem_image.mp (hI.symm ▸ hp)
      refine ⟨i, b, I, j, hUb ▸ hU, hI, hj, ?_⟩
      rw [hseq, hUb, ← hI, ← hbj,
        lattice_starRaySet_basis b Finset.univ I (Finset.subset_univ I) j hj]
    · have hfocus := «Σ».selected_focus_of_not_blowup R hne i hqi
      have hold := («Σ».selected_divisor_cone_iff R hne hdisj i hqi hi).mp hs
      obtain ⟨b, hsb⟩ := «Σ».full_cone_basis hold hcard
      obtain ⟨j, hj, hbj⟩ := Finset.mem_image.mp (hsb ▸ hi)
      have hstar : starRayBasis b {j} j = b := by
        apply DFunLike.ext
        intro k
        by_cases hkj : k = j <;> simp [starRayBasis_apply, starRayVector, hkj]
      refine ⟨i, b, {j}, j, hsb ▸ hold, ?_, Finset.mem_singleton_self j, ?_⟩
      · simp only [Finset.image_singleton, hbj, hfocus]
      · rw [hstar]
        exact hsb
  · left
    have hnone : ∀ i, «Σ».selectedRay R i ∉ (s : Finset (Lattice n)) := by
      simpa only [not_exists] using hex
    have h := («Σ».simultaneous_cone_without_sums_iff («Σ».selectedStarFocus R)
      (fun i => (R i).negative_cone) (fun i => hne i)
      («Σ».selectedStarFocus_disjoint R hdisj) (fun i => hnone i)).mp hs
    refine ⟨h.1, ?_⟩
    intro i hi
    by_cases hqi : 2 ≤ (R i).negative.card
    · exact h.2 ⟨i, hqi⟩ hi
    · have hfocus := «Σ».selected_focus_of_not_blowup R hne i hqi
      exact hnone i (hi (hfocus.symm ▸ Finset.mem_singleton_self («Σ».selectedRay R i)))

end SmoothCompleteFan

end PaperVerification.ToricGeometry
end
end Source_ToricSelectedCharts
-- END ORIGINAL PaperVerification.ToricSelectedCharts


-- BEGIN ORIGINAL PaperVerification.ToricCartierBoxCoordinates
section Source_ToricCartierBoxCoordinates

-- original header: module

-- original header: public import PaperVerification.ToricSelectedCharts
-- original header: public import PaperVerification.ToricFanFaceHulls

-- original header: @[expose] public section

/-!
# Cartier centers in arbitrary chosen full-cone bases

The displayed centers are identified by their actual supporting
equalities. Permuting primitive normals permutes the dual basis, so the
containment statements apply to the fan's chosen Cartier basis as well as
the adapted star basis.
-/

noncomputable section

namespace PaperVerification.ToricGeometry

open scoped BigOperators Classical

theorem integral_normal_basis_ext {n : ℕ}
    (b : Module.Basis (Fin n) ℤ (Lattice n)) (x y : Ambient n)
    (h : ∀ i, (dotProductEquiv ℝ (Fin n) (embed n (b i))) x =
      (dotProductEquiv ℝ (Fin n) (embed n (b i))) y) : x = y := by
  apply (integralBasisReal (integralDualBasis b)).ext_elem
  intro i
  have hx := integralDualBasis_real_pairing (integralDualBasis b) i x
  have hy := integralDualBasis_real_pairing (integralDualBasis b) i y
  simp only [integralDualBasis_involutive] at hx hy
  exact hx.symm.trans ((h i).trans hy)

theorem normal_pairing_sum {n : ℕ}
    (b : Module.Basis (Fin n) ℤ (Lattice n)) (I : Finset (Fin n))
    (x : Ambient n) :
    (dotProductEquiv ℝ (Fin n) (embed n (∑ i ∈ I, b i))) x =
      ∑ i ∈ I, (dotProductEquiv ℝ (Fin n) (embed n (b i))) x := by
  simp only [map_sum, LinearMap.sum_apply]

namespace SmoothCompleteFan

variable {n : ℕ} («Σ» : SmoothCompleteFan n)

theorem cartierPoint_eq_of_active_basis (a : Lattice n → ℝ)
    (s : «Σ».fullCones) (d : Module.Basis (Fin n) ℤ (Lattice n))
    (hset : (s : Finset (Lattice n)) = Finset.univ.image d) (x : Ambient n)
    (hx : ∀ i, (dotProductEquiv ℝ (Fin n) (embed n (d i))) x = -a (d i)) :
    «Σ».cartierPoint a s = x := by
  apply integral_normal_basis_ext d
  intro i
  rw [«Σ».cartierPoint_support_eq a s
    (hset.symm ▸ Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩), hx i]

theorem cartierBasis_eq_permuted
    (s : «Σ».fullCones) (d : Module.Basis (Fin n) ℤ (Lattice n))
    (hset : (s : Finset (Lattice n)) = Finset.univ.image d) :
    ∃ σ : Equiv.Perm (Fin n), ∀ i,
      «Σ».cartierBasis s i = integralBasisReal (integralDualBasis d) (σ i) := by
  obtain ⟨σ, hσ⟩ := integral_bases_perm_of_equal_ray_cones («Σ».fullConeBasis s) d
    (by rw [← «Σ».fullConeBasis_ray_set s, ← hset])
  have hdual := integralDualBasis_of_permuted_normals
    («Σ».fullConeBasis s) (integralDualBasis d) σ
    (by simpa only [integralDualBasis_involutive] using hσ)
  refine ⟨σ, ?_⟩
  intro i
  change integralBasisReal (integralDualBasis («Σ».fullConeBasis s)) i = _
  rw [integralBasisReal_apply, integralBasisReal_apply, hdual i]

/-- The full closed centered box is independent of the ordering of the
primitive normals in its actual full cone. -/
theorem centered_box_in_cartierBasis
    (a : Lattice n → ℝ) (s : «Σ».fullCones)
    (d : Module.Basis (Fin n) ℤ (Lattice n))
    (hset : (s : Finset (Lattice n)) = Finset.univ.image d)
    (A : Set (Ambient n)) (radius : ℝ)
    (hbox : ∀ t : Fin n → ℝ, (∀ i, |t i| ≤ radius) →
      «Σ».cartierPoint a s + ∑ i, t i • integralBasisReal (integralDualBasis d) i ∈ A)
    (t : Fin n → ℝ) (ht : ∀ i, |t i| ≤ radius) :
    «Σ».cartierPoint a s + ∑ i, t i • «Σ».cartierBasis s i ∈ A := by
  obtain ⟨σ, hσ⟩ := «Σ».cartierBasis_eq_permuted s d hset
  have hsum : (∑ i, t i • «Σ».cartierBasis s i) =
      ∑ k, t (σ.symm k) • integralBasisReal (integralDualBasis d) k := by
    apply Fintype.sum_equiv σ
    intro i
    rw [hσ i, σ.symm_apply_apply]
  rw [hsum]
  exact hbox (fun k => t (σ.symm k)) (fun k => ht (σ.symm k))

variable {ι : Type*} [Fintype ι] (R : ι → «Σ».PrimitiveRelation)
variable (hne : ∀ i, (R i).negative.Nonempty)
variable (hdisj : «Σ».PairwiseDisjointFoci (fun i => (R i).negative))

def selectedCenteredSupport (a : Lattice n → ℝ) (c : ℝ) (u : ι → ℝ) :
    Lattice n → ℝ := fun v => «Σ».selectedPullback R a v - c -
      ∑ i, if v = «Σ».selectedRay R i then u i else 0

include hne hdisj in
theorem selectedCenteredSupport_at_selected_ray
    (a : Lattice n → ℝ) (c : ℝ) (u : ι → ℝ) (i : ι) :
    «Σ».selectedCenteredSupport R a c u («Σ».selectedRay R i) =
      (∑ v ∈ (R i).negative, a v) - c - u i := by
  rw [selectedCenteredSupport, «Σ».selectedPullback_at_selected_ray R hne hdisj a i]
  simp only [(«Σ».selectedRay_injective R hdisj).eq_iff,
    Finset.sum_ite_eq, Finset.mem_univ, if_true]

theorem selectedCenteredSupport_on_outside_cone
    (a : Lattice n → ℝ) (c : ℝ) (u : ι → ℝ)
    {s : Finset (Lattice n)} (hs : s ∈ «Σ».cones)
    (houtside : ∀ i, ¬ (R i).negative ⊆ s) {v : Lattice n} (hv : v ∈ s) :
    «Σ».selectedCenteredSupport R a c u v = a v - c := by
  rw [selectedCenteredSupport,
    «Σ».selectedPullback_old_ray R a («Σ».ray_mem_of_mem_cone hs hv)]
  have hne' (i : ι) : v ≠ «Σ».selectedRay R i := by
    intro h
    apply houtside i
    apply («Σ».sum_rays_mem_cone_iff (R i).negative_cone hs).mp
    have hmem : «Σ».selectedRay R i ∈ s := h ▸ hv
    change (∑ w ∈ (R i).negative, w) ∈ s at hmem
    exact latticeRayCone_generator s hmem
  simp only [if_neg (hne' _), Finset.sum_const_zero, sub_zero]

theorem selected_center_outside_chart
    (a : Lattice n → ℝ) (c : ℝ) (u : ι → ℝ)
    (s : («Σ».selectedFan R hne hdisj).fullCones)
    (hs : (s : Finset (Lattice n)) ∈ «Σ».cones)
    (houtside : ∀ i, ¬ (R i).negative ⊆ (s : Finset (Lattice n)))
    (b : Module.Basis (Fin n) ℤ (Lattice n))
    (hset : (s : Finset (Lattice n)) = Finset.univ.image b)
    (v : Ambient n)
    (hv : ∀ i, (dotProductEquiv ℝ (Fin n) (embed n (b i))) v = -a (b i)) :
    («Σ».selectedFan R hne hdisj).cartierPoint
      («Σ».selectedCenteredSupport R a c u) s =
      v + ∑ i, c • integralBasisReal (integralDualBasis b) i := by
  apply («Σ».selectedFan R hne hdisj).cartierPoint_eq_of_active_basis _ s b hset
  intro i
  rw [map_add, map_sum, hv i,
    «Σ».selectedCenteredSupport_on_outside_cone R a c u hs houtside
      (hset.symm ▸ Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩)]
  simp only [map_smul, LatticePolytope.normal_basis_dual_pairing,
    smul_eq_mul, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
    Finset.mem_univ, if_true]
  ring

theorem selected_center_star_chart
    (a : Lattice n → ℝ) (c : ℝ) (u : ι → ℝ)
    (s : («Σ».selectedFan R hne hdisj).fullCones) (i : ι)
    (b : Module.Basis (Fin n) ℤ (Lattice n)) (I : Finset (Fin n))
    (hfull : Finset.univ.image b ∈ «Σ».cones) (hI : I.image b = (R i).negative)
    (j : Fin n) (hj : j ∈ I)
    (hset : (s : Finset (Lattice n)) = Finset.univ.image (starRayBasis b I j))
    (v : Ambient n)
    (hv : ∀ k, (dotProductEquiv ℝ (Fin n) (embed n (b k))) v = -a (b k)) :
    («Σ».selectedFan R hne hdisj).cartierPoint
      («Σ».selectedCenteredSupport R a c u) s =
      v + u i • integralBasisReal (integralDualBasis b) j +
        ∑ k, c • starShearBasis (integralBasisReal (integralDualBasis b)) I j k := by
  let d := starRayBasis b I j
  have hdj : d j = «Σ».selectedRay R i := by
    rw [starRayBasis_pivot b I j hj, selectedRay, ← hI, Finset.sum_image]
    exact fun k _ l _ hkl => b.injective hkl
  have he : «Σ».selectedRay R i ∈ (s : Finset (Lattice n)) := by
    rw [hset]
    exact Finset.mem_image.mpr ⟨j, Finset.mem_univ j, hdj⟩
  have hother (k : Fin n) (hkj : k ≠ j) :
      «Σ».selectedCenteredSupport R a c u (d k) = a (b k) - c := by
    have hdk : d k = b k := starRayBasis_other b I j k hkj
    have hdold : d k ∈ «Σ».rays := by
      rw [hdk]
      exact «Σ».ray_mem_of_mem_cone hfull (Finset.mem_image.mpr ⟨k, Finset.mem_univ k, rfl⟩)
    have hnot (l : ι) : d k ≠ «Σ».selectedRay R l := by
      intro h
      by_cases hli : l = i
      · subst l
        exact hkj (d.injective (h.trans hdj.symm))
      · exact «Σ».selected_no_common_rays R hne hdisj i l (Ne.symm hli)
          ((«Σ».selectedFan R hne hdisj).fullCones_mem s) he
          (hset.symm ▸ Finset.mem_image.mpr ⟨k, Finset.mem_univ k, h⟩)
    rw [selectedCenteredSupport, «Σ».selectedPullback_old_ray R a hdold, hdk]
    simp only [← hdk, if_neg (hnot _), Finset.sum_const_zero, sub_zero]
  have hsum : (∑ k ∈ I, a (b k)) = ∑ w ∈ (R i).negative, a w := by
    rw [← hI, Finset.sum_image]
    exact fun k _ l _ hkl => b.injective hkl
  have hdual : integralBasisReal (integralDualBasis d) =
      starShearBasis (integralBasisReal (integralDualBasis b)) I j :=
    integralBasisReal_dual_starRayBasis b I j hj
  have hpivot : integralBasisReal (integralDualBasis d) j =
      integralBasisReal (integralDualBasis b) j := by
    rw [hdual, starShearBasis_pivot]
  apply («Σ».selectedFan R hne hdisj).cartierPoint_eq_of_active_basis _ s d hset
  intro k
  have hbase : (dotProductEquiv ℝ (Fin n) (embed n (d k))) v =
      if k = j then -(∑ w ∈ (R i).negative, a w) else -a (b k) := by
    by_cases hkj : k = j
    · subst k
      rw [if_pos rfl, starRayBasis_pivot b I j hj, normal_pairing_sum]
      simp only [hv, Finset.sum_neg_distrib, hsum]
    · rw [if_neg hkj, starRayBasis_other b I j k hkj, hv k]
  rw [← hdual, ← hpivot, map_add, map_add, map_smul, map_sum, hbase]
  simp only [map_smul, LatticePolytope.normal_basis_dual_pairing,
    smul_eq_mul, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
    Finset.mem_univ, if_true]
  by_cases hkj : k = j
  · subst k
    rw [if_pos rfl, hdj, «Σ».selectedCenteredSupport_at_selected_ray R hne hdisj a c u i]
    simp only [ite_true]
    ring
  · rw [if_neg hkj, if_neg (Ne.symm hkj), hother k hkj]
    ring

end SmoothCompleteFan

end PaperVerification.ToricGeometry
end
end Source_ToricCartierBoxCoordinates
-- END ORIGINAL PaperVerification.ToricCartierBoxCoordinates


-- BEGIN ORIGINAL PaperVerification.ToricActivatedCorrections
section Source_ToricActivatedCorrections

-- original header: module

-- original header: public import PaperVerification.ToricObstructionSelection
-- original header: public import PaperVerification.ToricNefBoxGeometry

-- original header: @[expose] public section

/-!
# The exhaustive activated family and its actual ceiling corrections

Activation is defined by negative degree of the integral old support
function, over every contractible primitive collection.  The repair is an
integer ceiling divided by the actual least positive focus coefficient.
The degree budgets are derived from the original edge lengths.
-/

noncomputable section

namespace PaperVerification.ToricGeometry

open scoped BigOperators Classical

namespace SmoothCompleteFan

variable {n : ℕ} («Σ» : SmoothCompleteFan n)

abbrev ActivatedIndices (a : Lattice n → ℤ) :=
  «Σ».selectedPrimitiveCollections (fun Q => Q.degree (fun v => (a v : ℝ)) < 0)

def activatedRelation (a : Lattice n → ℤ) (i : «Σ».ActivatedIndices a) : «Σ».PrimitiveRelation :=
  «Σ».selectionRelation (fun Q => Q.degree (fun v => (a v : ℝ)) < 0) i

theorem activatedRelation_contractible (a : Lattice n → ℤ) (i : «Σ».ActivatedIndices a) :
    («Σ».activatedRelation a i).IsCombinatoriallyContractible :=
  «Σ».selectionRelation_contractible _ i

theorem activatedRelation_negative (a : Lattice n → ℤ) (i : «Σ».ActivatedIndices a) :
    («Σ».activatedRelation a i).degree (fun v => (a v : ℝ)) < 0 :=
  «Σ».selectionRelation_test _ i

theorem activatedRelation_exhaustive (a : Lattice n → ℤ) (Q : «Σ».PrimitiveRelation) :
    (∃ i : «Σ».ActivatedIndices a, Q.positive = («Σ».activatedRelation a i).positive) ↔
      Q.IsCombinatoriallyContractible ∧ Q.degree (fun v => (a v : ℝ)) < 0 := by
  apply «Σ».selectionRelation_exhaustive
  intro R S hpos
  rw [R.degree_unique S hpos]

theorem activatedRelation_unselected_nonneg (a : Lattice n → ℤ)
    (Q : «Σ».PrimitiveRelation) (hQ : Q.IsCombinatoriallyContractible)
    (hother : ∀ i : «Σ».ActivatedIndices a,
      Q.positive ≠ («Σ».activatedRelation a i).positive) :
    0 ≤ Q.degree (fun v => (a v : ℝ)) := by
  by_contra hh
  obtain ⟨i, hi⟩ := («Σ».activatedRelation_exhaustive a Q).mpr ⟨hQ, lt_of_not_ge hh⟩
  exact hother i hi

def activatedCorrection (a : Lattice n → ℤ)
    (hne : ∀ i : «Σ».ActivatedIndices a, («Σ».activatedRelation a i).negative.Nonempty)
    (i : «Σ».ActivatedIndices a) : ℤ :=
  Int.ceil (((-(«Σ».activatedRelation a i).integerDegree a : ℤ) : ℝ) /
    ((«Σ».activatedRelation a i).minimumCoefficient (hne i) : ℝ))

theorem activatedCorrection_bounds (a : Lattice n → ℤ)
    (hne : ∀ i : «Σ».ActivatedIndices a, («Σ».activatedRelation a i).negative.Nonempty)
    (i : «Σ».ActivatedIndices a) :
    1 ≤ «Σ».activatedCorrection a hne i ∧
      «Σ».activatedCorrection a hne i ≤ -(«Σ».activatedRelation a i).integerDegree a ∧
      0 ≤ («Σ».activatedRelation a i).integerDegree a +
        ((«Σ».activatedRelation a i).minimumCoefficient (hne i) : ℤ) *
          «Σ».activatedCorrection a hne i := by
  let Q := «Σ».activatedRelation a i
  have hneg := «Σ».activatedRelation_negative a i
  rw [← Q.integerDegree_cast] at hneg
  have hnegZ : Q.integerDegree a < 0 := by exact_mod_cast hneg
  have hδ : (0 : ℤ) < -Q.integerDegree a := by omega
  have hm : (1 : ℤ) ≤ Q.minimumCoefficient (hne i) := by
    exact_mod_cast (Q.minimumCoefficient_spec (hne i)).1
  obtain ⟨hpos, hupper, hrepair⟩ :=
    positive_ceil_correction (-Q.integerDegree a) (Q.minimumCoefficient (hne i)) hδ hm
  change 1 ≤ _ ∧ _ ≤ _ ∧ 0 ≤ _
  have hpos' : 1 ≤ «Σ».activatedCorrection a hne i := by
    simpa only [activatedCorrection, Int.cast_natCast] using hpos
  have hupper' : «Σ».activatedCorrection a hne i ≤ -Q.integerDegree a := by
    simpa only [activatedCorrection, Int.cast_natCast] using hupper
  have hrepair' : -Q.integerDegree a ≤
      (Q.minimumCoefficient (hne i) : ℤ) * «Σ».activatedCorrection a hne i := by
    simpa only [activatedCorrection, Int.cast_natCast] using hrepair
  dsimp only [Q] at hupper' hrepair'
  exact ⟨hpos', hupper', by omega⟩

theorem activatedCorrection_real_bounds (a : Lattice n → ℤ)
    (hne : ∀ i : «Σ».ActivatedIndices a, («Σ».activatedRelation a i).negative.Nonempty)
    (i : «Σ».ActivatedIndices a) :
    0 ≤ («Σ».activatedCorrection a hne i : ℝ) ∧
      («Σ».activatedCorrection a hne i : ℝ) ≤
        -(«Σ».activatedRelation a i).degree (fun v => (a v : ℝ)) ∧
      0 ≤ («Σ».activatedRelation a i).degree (fun v => (a v : ℝ)) +
        ((«Σ».activatedRelation a i).minimumCoefficient (hne i) : ℝ) *
          («Σ».activatedCorrection a hne i : ℝ) := by
  obtain ⟨hpos, hup, hrepair⟩ := «Σ».activatedCorrection_bounds a hne i
  have hposR : (1 : ℝ) ≤ «Σ».activatedCorrection a hne i := by exact_mod_cast hpos
  have hupR : («Σ».activatedCorrection a hne i : ℝ) ≤
      -((«Σ».activatedRelation a i).integerDegree a : ℝ) := by exact_mod_cast hup
  have hrepairR : (0 : ℝ) ≤ ((«Σ».activatedRelation a i).integerDegree a : ℝ) +
      ((«Σ».activatedRelation a i).minimumCoefficient (hne i) : ℝ) *
        («Σ».activatedCorrection a hne i : ℝ) := by exact_mod_cast hrepair
  rw [(«Σ».activatedRelation a i).integerDegree_cast] at hupR hrepairR
  exact ⟨zero_le_one.trans hposR, hupR, hrepairR⟩

def sideTwoOldSupport («_Σ» : SmoothCompleteFan n)
    (P : LatticePolytope n) (D : Finset (Lattice n)) : Lattice n → ℤ :=
  fun v => P.integralSupport v - if v ∈ D then 2 else 0

def innerUnitOldSupport («_Σ» : SmoothCompleteFan n)
    (P : LatticePolytope n) (D : Finset (Lattice n)) : Lattice n → ℤ :=
  fun v => P.integralSupport v - 1 - if v ∈ D then 1 else 0

theorem sideTwoOldSupport_cast (P : LatticePolytope n) (D : Finset (Lattice n)) :
    (fun v => («Σ».sideTwoOldSupport P D v : ℝ)) =
      fun v => (P.integralSupport v : ℝ) - 2 * (if v ∈ D then 1 else 0) := by
  funext v
  by_cases hv : v ∈ D <;> simp [sideTwoOldSupport, hv]

theorem innerUnitOldSupport_cast (P : LatticePolytope n) (D : Finset (Lattice n)) :
    (fun v => («Σ».innerUnitOldSupport P D v : ℝ)) =
      fun v => (P.integralSupport v : ℝ) - 1 - (if v ∈ D then 1 else 0) := by
  funext v
  by_cases hv : v ∈ D <;> simp [innerUnitOldSupport, hv]

theorem sideTwoOldSupport_degree (P : LatticePolytope n)
    (D : Finset (Lattice n)) (Q : «Σ».PrimitiveRelation) :
    Q.degree (fun v => («Σ».sideTwoOldSupport P D v : ℝ)) =
      Q.degree (fun v => (P.integralSupport v : ℝ)) -
        2 * (((D ∩ Q.positive).card : ℝ) - Q.negativeWeightOn D) := by
  rw [«Σ».sideTwoOldSupport_cast]
  have he : (fun v => (P.integralSupport v : ℝ) -
      2 * (if v ∈ D then 1 else 0)) =
      (fun v => (P.integralSupport v : ℝ)) -
        (2 : ℝ) • (fun v => if v ∈ D then 1 else 0) := by
    funext v
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  rw [he]
  rw [Q.degree_sub, Q.degree_smul, Q.degree_indicator, Finset.inter_comm Q.positive D]

theorem innerUnitOldSupport_degree (P : LatticePolytope n)
    (D : Finset (Lattice n)) (Q : «Σ».PrimitiveRelation) :
    Q.degree (fun v => («Σ».innerUnitOldSupport P D v : ℝ)) =
      Q.degree (fun v => (P.integralSupport v : ℝ)) -
        ((Q.fiberDimension : ℝ) + 1 - Q.negativeCoefficientSum) -
        (((D ∩ Q.positive).card : ℝ) - Q.negativeWeightOn D) := by
  rw [«Σ».innerUnitOldSupport_cast]
  change Q.degree ((fun v => (P.integralSupport v : ℝ) - 1) -
    (fun v => if v ∈ D then 1 else 0)) = _
  rw [Q.degree_sub, Q.degree_constant_subtraction, Q.degree_indicator,
    Finset.inter_comm Q.positive D, one_mul]

theorem selection_positive_card_le_fiberDimension
    {σ D : Finset (Lattice n)} (hσ : σ ∈ «Σ».cones) (hD : D ⊆ σ)
    (Q : «Σ».PrimitiveRelation) : (D ∩ Q.positive).card ≤ Q.fiberDimension := by
  rw [Finset.inter_comm D Q.positive]
  exact (Finset.card_le_card (Finset.inter_subset_inter_left hD)).trans
    (Q.positive_rays_in_cone_bound hσ)

/-- Every side-two activated class is one of the paper's original
obstructions, and has large fiber dimension. -/
theorem side_two_activated_obstruction
    (hpure : «Σ».IsPure) (P : LatticePolytope n) (hP : P.Smooth)
    (hfan : «Σ».realCones = P.normalFan) (hbound : P.EdgesAtLeast n)
    {σ D : Finset (Lattice n)} (hσ : σ ∈ «Σ».cones) (hD : D ⊆ σ)
    (i : «Σ».ActivatedIndices («Σ».sideTwoOldSupport P D)) :
    («Σ».activatedRelation («Σ».sideTwoOldSupport P D) i).degree
        (fun v => (P.integralSupport v : ℝ)) <
      2 * ((«Σ».activatedRelation («Σ».sideTwoOldSupport P D) i).fiberDimension : ℝ) ∧
    n < 2 * («Σ».activatedRelation («Σ».sideTwoOldSupport P D) i).fiberDimension := by
  let Q := «Σ».activatedRelation («Σ».sideTwoOldSupport P D) i
  have hQ := «Σ».activatedRelation_contractible («Σ».sideTwoOldSupport P D) i
  have hneg := «Σ».activatedRelation_negative («Σ».sideTwoOldSupport P D) i
  rw [«Σ».sideTwoOldSupport_degree] at hneg
  have hA : ((D ∩ Q.positive).card : ℝ) ≤ Q.fiberDimension := by
    exact_mod_cast «Σ».selection_positive_card_le_fiberDimension hσ hD Q
  have hNS := Q.negativeWeightOn_nonneg D
  have hd := P.contractible_degree_lower_bound hP «Σ» hpure hfan hbound Q hQ
  have hobs : Q.degree (fun v => (P.integralSupport v : ℝ)) <
      2 * (Q.fiberDimension : ℝ) := by linarith
  refine ⟨hobs, ?_⟩
  exact_mod_cast hd.trans_lt hobs

theorem side_two_activated_deficit_budget
    (hpure : «Σ».IsPure) (P : LatticePolytope n) (hP : P.Smooth)
    (hfan : «Σ».realCones = P.normalFan) (hbound : P.EdgesAtLeast n)
    (D : Finset (Lattice n)) (Q : «Σ».PrimitiveRelation)
    (hQ : Q.IsCombinatoriallyContractible) :
    -Q.degree (fun v => («Σ».sideTwoOldSupport P D v : ℝ)) ≤
      2 * ((D ∩ Q.positive).card : ℝ) - 2 * ((Q.negative ∩ D).card : ℝ) - n := by
  rw [«Σ».sideTwoOldSupport_degree]
  have hd := P.contractible_degree_lower_bound hP «Σ» hpure hfan hbound Q hQ
  have hNS := Q.card_negative_inter_le_weight D
  linarith

/-- Every inner-unit activated class satisfies exactly the original
adjoint obstruction (12), and has large fiber dimension. -/
theorem inner_unit_activated_obstruction
    (hpure : «Σ».IsPure) (P : LatticePolytope n) (hP : P.Smooth)
    (hfan : «Σ».realCones = P.normalFan) (hbound : P.EdgesAtLeast (n + 1))
    {σ D : Finset (Lattice n)} (hσ : σ ∈ «Σ».cones) (hD : D ⊆ σ)
    (i : «Σ».ActivatedIndices («Σ».innerUnitOldSupport P D)) :
    0 < 2 * ((«Σ».activatedRelation («Σ».innerUnitOldSupport P D) i).fiberDimension : ℝ) + 1 -
      («Σ».activatedRelation («Σ».innerUnitOldSupport P D) i).degree
        (fun v => (P.integralSupport v : ℝ)) -
      («Σ».activatedRelation («Σ».innerUnitOldSupport P D) i).negativeCoefficientSum ∧
    n < 2 * («Σ».activatedRelation («Σ».innerUnitOldSupport P D) i).fiberDimension := by
  let Q := «Σ».activatedRelation («Σ».innerUnitOldSupport P D) i
  have hQ := «Σ».activatedRelation_contractible («Σ».innerUnitOldSupport P D) i
  have hneg := «Σ».activatedRelation_negative («Σ».innerUnitOldSupport P D) i
  rw [«Σ».innerUnitOldSupport_degree] at hneg
  have hA : ((D ∩ Q.positive).card : ℝ) ≤ Q.fiberDimension := by
    exact_mod_cast «Σ».selection_positive_card_le_fiberDimension hσ hD Q
  have hNS := Q.negativeWeightOn_nonneg D
  have hC := Q.negativeCoefficientSum_nonneg
  have hd := P.contractible_degree_lower_bound hP «Σ» hpure hfan hbound Q hQ
  norm_num only [Nat.cast_add, Nat.cast_one] at hd
  have hobs : 0 < 2 * (Q.fiberDimension : ℝ) + 1 -
      Q.degree (fun v => (P.integralSupport v : ℝ)) - Q.negativeCoefficientSum := by linarith
  refine ⟨hobs, ?_⟩
  have hh : (n : ℝ) < 2 * (Q.fiberDimension : ℝ) := by linarith
  exact_mod_cast hh

theorem inner_unit_activated_deficit_budget
    (hpure : «Σ».IsPure) (P : LatticePolytope n) (hP : P.Smooth)
    (hfan : «Σ».realCones = P.normalFan) (hbound : P.EdgesAtLeast (n + 1))
    {σ D : Finset (Lattice n)} (hσ : σ ∈ «Σ».cones) (hD : D ⊆ σ)
    (Q : «Σ».PrimitiveRelation) (hQ : Q.IsCombinatoriallyContractible) :
    -Q.degree (fun v => («Σ».innerUnitOldSupport P D v : ℝ)) ≤
      2 * (Q.fiberDimension : ℝ) - n - Q.negative.card := by
  rw [«Σ».innerUnitOldSupport_degree]
  have hd := P.contractible_degree_lower_bound hP «Σ» hpure hfan hbound Q hQ
  have hA : ((D ∩ Q.positive).card : ℝ) ≤ Q.fiberDimension := by
    exact_mod_cast «Σ».selection_positive_card_le_fiberDimension hσ hD Q
  have hC := Q.card_negative_le_coefficientSum
  have hNS := Q.negativeWeightOn_nonneg D
  norm_num only [Nat.cast_add, Nat.cast_one] at hd
  linarith

end SmoothCompleteFan

end PaperVerification.ToricGeometry
end
end Source_ToricActivatedCorrections
-- END ORIGINAL PaperVerification.ToricActivatedCorrections


-- BEGIN ORIGINAL PaperVerification.ToricOutsideCorrections
section Source_ToricOutsideCorrections

-- original header: module

-- original header: public import PaperVerification.ToricActivatedCorrections

-- original header: @[expose] public section

/-!
# Canonical corrected supports at an outside cone

All activated classes and all correction coefficients are constructed from
the actual integral support. The conclusions contain no supplied
contractible-class degree bounds, correction family, or nefness premise.
-/

noncomputable section

namespace PaperVerification.ToricGeometry

open scoped BigOperators Classical

namespace SmoothCompleteFan

variable {n : ℕ} («Σ» : SmoothCompleteFan n)

theorem exists_outside_side_two_correction
    (hpure : «Σ».IsPure) (P : LatticePolytope n) (hP : P.Smooth)
    (hfan : «Σ».realCones = P.normalFan) (hbound : P.EdgesAtLeast n)
    (σ D : Finset (Lattice n)) (hσ : σ ∈ «Σ».cones) (hDσ : D ⊆ σ)
    (houtside : ∀ Q : «Σ».PrimitiveRelation, Q.IsCombinatoriallyContractible →
      Q.degree (fun v => (P.integralSupport v : ℝ)) < 2 * (Q.fiberDimension : ℝ) →
      ¬ Q.negative ⊆ σ) :
    ∃ (Γ : SmoothCompleteFan n) (F : Lattice n → ℝ),
      Γ.IsNef F ∧ «Σ».rays ⊆ Γ.rays ∧ σ ∈ Γ.cones ∧
      (∀ v ∈ σ, F v = (P.integralSupport v : ℝ) - 2 * (if v ∈ D then 1 else 0)) ∧
      (∀ v ∈ «Σ».rays, F v ≤ (P.integralSupport v : ℝ) - 2 * (if v ∈ D then 1 else 0)) := by
  let a := «Σ».sideTwoOldSupport P D
  let R := «Σ».activatedRelation a
  have hR (i : «Σ».ActivatedIndices a) : (R i).IsCombinatoriallyContractible :=
    «Σ».activatedRelation_contractible a i
  have hobs (i : «Σ».ActivatedIndices a) :
      (R i).degree (fun v => (P.integralSupport v : ℝ)) < 2 * ((R i).fiberDimension : ℝ) :=
    («Σ».side_two_activated_obstruction hpure P hP hfan hbound hσ hDσ i).1
  have hlarge (i : «Σ».ActivatedIndices a) : n < 2 * (R i).fiberDimension :=
    («Σ».side_two_activated_obstruction hpure P hP hfan hbound hσ hDσ i).2
  have hdisj : «Σ».PairwiseDisjointFoci (fun i => (R i).negative) :=
    «Σ».selectionRelation_disjoint_of_large hpure _ hlarge
  have hout (i : «Σ».ActivatedIndices a) : ¬ (R i).negative ⊆ σ :=
    houtside (R i) (hR i) (hobs i)
  have hne (i : «Σ».ActivatedIndices a) : (R i).negative.Nonempty := by
    apply Finset.nonempty_iff_ne_empty.mpr
    intro hh
    apply hout i
    rw [hh]
    exact Finset.empty_subset _
  let τ : «Σ».ActivatedIndices a → ℝ := fun i => («Σ».activatedCorrection a hne i : ℝ)
  let Γ := «Σ».selectedFan R hne hdisj
  let aR : Lattice n → ℝ := fun v => (a v : ℝ)
  have haR : aR = fun v => (P.integralSupport v : ℝ) - 2 * (if v ∈ D then 1 else 0) :=
    «Σ».sideTwoOldSupport_cast P D
  let F := simultaneousSupport (fun i => (R i).negative) aR τ
  have hτ0 (i : «Σ».ActivatedIndices a) : 0 ≤ τ i :=
    («Σ».activatedCorrection_real_bounds a hne i).1
  have hbudget (i : «Σ».ActivatedIndices a) : τ i ≤
      2 * ((D ∩ (R i).positive).card : ℝ) -
        2 * (((R i).negative ∩ D).card : ℝ) - n :=
    («Σ».activatedCorrection_real_bounds a hne i).2.1.trans
      («Σ».side_two_activated_deficit_budget hpure P hP hfan hbound D (R i) (hR i))
  have hfiber (i : «Σ».ActivatedIndices a) : τ i ≤ 2 * ((R i).fiberDimension : ℝ) - n := by
    have hh := hbudget i
    have hA : ((D ∩ (R i).positive).card : ℝ) ≤ (R i).fiberDimension := by
      exact_mod_cast «Σ».selection_positive_card_le_fiberDimension hσ hDσ (R i)
    have hk : (0 : ℝ) ≤ ((R i).negative ∩ D).card := Nat.cast_nonneg _
    linarith
  have hrepair (i : «Σ».ActivatedIndices a) : 0 ≤
      (R i).degree (fun v => (P.integralSupport v : ℝ) - 2 * (if v ∈ D then 1 else 0)) +
        ((R i).minimumCoefficient (hne i) : ℝ) * τ i := by
    have hh := («Σ».activatedCorrection_real_bounds a hne i).2.2
    change 0 ≤ (R i).degree aR + _ at hh
    rw [haR] at hh
    exact hh
  have hinactive (Q : «Σ».PrimitiveRelation) (hQ : Q.IsCombinatoriallyContractible)
      (hother : ∀ i : «Σ».ActivatedIndices a, Q.positive ≠ (R i).positive) :
      0 ≤ Q.degree (fun v => (P.integralSupport v : ℝ) - 2 * (if v ∈ D then 1 else 0)) := by
    have hh := «Σ».activatedRelation_unselected_nonneg a Q hQ hother
    change 0 ≤ Q.degree aR at hh
    rw [haR] at hh
    exact hh
  have hF : Γ.IsNef F := by
    change Γ.IsNef (simultaneousSupport (fun i => (R i).negative) aR τ)
    rw [haR]
    exact «Σ».outside_side_two_corrected_isNef R hR hne hdisj
      hpure P hP hfan hbound σ D hσ hDσ hout τ hτ0 hfiber hbudget hrepair hinactive
  refine ⟨Γ, F, hF, «Σ».old_rays_subset_selected R hne hdisj,
    «Σ».outside_cone_mem_selected R hne hdisj hσ hout, ?_, ?_⟩
  · intro v hv
    change simultaneousSupport (fun i => (R i).negative) aR τ v = _
    rw [«Σ».selected_support_eq_old_on_outside_cone R aR τ hσ hout hv]
    exact congrFun haR v
  · intro v hv
    have hh := «Σ».selected_support_le_old_on_rays R hne hdisj aR τ hτ0 hv
    rw [congrFun haR v] at hh
    exact hh

theorem exists_outside_inner_unit_correction
    (hpure : «Σ».IsPure) (P : LatticePolytope n) (hP : P.Smooth)
    (hfan : «Σ».realCones = P.normalFan) (hbound : P.EdgesAtLeast (n + 1))
    (σ D : Finset (Lattice n)) (hσ : σ ∈ «Σ».cones) (hDσ : D ⊆ σ)
    (houtside : ∀ Q : «Σ».PrimitiveRelation, Q.IsCombinatoriallyContractible →
      0 < 2 * (Q.fiberDimension : ℝ) + 1 -
        Q.degree (fun v => (P.integralSupport v : ℝ)) - Q.negativeCoefficientSum →
      ¬ Q.negative ⊆ σ) :
    ∃ (Γ : SmoothCompleteFan n) (F : Lattice n → ℝ),
      Γ.IsNef F ∧ «Σ».rays ⊆ Γ.rays ∧ σ ∈ Γ.cones ∧
      (∀ v ∈ σ, F v = (P.integralSupport v : ℝ) - 1 - (if v ∈ D then 1 else 0)) ∧
      (∀ v ∈ «Σ».rays, F v ≤ (P.integralSupport v : ℝ) - 1 - (if v ∈ D then 1 else 0)) := by
  let a := «Σ».innerUnitOldSupport P D
  let R := «Σ».activatedRelation a
  have hR (i : «Σ».ActivatedIndices a) : (R i).IsCombinatoriallyContractible :=
    «Σ».activatedRelation_contractible a i
  have hobs (i : «Σ».ActivatedIndices a) : 0 < 2 * ((R i).fiberDimension : ℝ) + 1 -
      (R i).degree (fun v => (P.integralSupport v : ℝ)) - (R i).negativeCoefficientSum :=
    («Σ».inner_unit_activated_obstruction hpure P hP hfan hbound hσ hDσ i).1
  have hlarge (i : «Σ».ActivatedIndices a) : n < 2 * (R i).fiberDimension :=
    («Σ».inner_unit_activated_obstruction hpure P hP hfan hbound hσ hDσ i).2
  have hdisj : «Σ».PairwiseDisjointFoci (fun i => (R i).negative) :=
    «Σ».selectionRelation_disjoint_of_large hpure _ hlarge
  have hout (i : «Σ».ActivatedIndices a) : ¬ (R i).negative ⊆ σ :=
    houtside (R i) (hR i) (hobs i)
  have hne (i : «Σ».ActivatedIndices a) : (R i).negative.Nonempty := by
    apply Finset.nonempty_iff_ne_empty.mpr
    intro hh
    apply hout i
    rw [hh]
    exact Finset.empty_subset _
  let τ : «Σ».ActivatedIndices a → ℝ := fun i => («Σ».activatedCorrection a hne i : ℝ)
  let Γ := «Σ».selectedFan R hne hdisj
  let aR : Lattice n → ℝ := fun v => (a v : ℝ)
  have haR : aR = fun v => (P.integralSupport v : ℝ) - 1 - (if v ∈ D then 1 else 0) :=
    «Σ».innerUnitOldSupport_cast P D
  let F := simultaneousSupport (fun i => (R i).negative) aR τ
  have hτ0 (i : «Σ».ActivatedIndices a) : 0 ≤ τ i :=
    («Σ».activatedCorrection_real_bounds a hne i).1
  have hupper (i : «Σ».ActivatedIndices a) : τ i ≤
      2 * ((R i).fiberDimension : ℝ) - n - (R i).negative.card :=
    («Σ».activatedCorrection_real_bounds a hne i).2.1.trans
      («Σ».inner_unit_activated_deficit_budget hpure P hP hfan hbound hσ hDσ (R i) (hR i))
  have hrepair (i : «Σ».ActivatedIndices a) : 0 ≤
      (R i).degree (fun v => (P.integralSupport v : ℝ) - 1 - (if v ∈ D then 1 else 0)) +
        ((R i).minimumCoefficient (hne i) : ℝ) * τ i := by
    have hh := («Σ».activatedCorrection_real_bounds a hne i).2.2
    change 0 ≤ (R i).degree aR + _ at hh
    rw [haR] at hh
    exact hh
  have hinactive (Q : «Σ».PrimitiveRelation) (hQ : Q.IsCombinatoriallyContractible)
      (hother : ∀ i : «Σ».ActivatedIndices a, Q.positive ≠ (R i).positive) :
      0 ≤ Q.degree (fun v => (P.integralSupport v : ℝ) - 1 - (if v ∈ D then 1 else 0)) := by
    have hh := «Σ».activatedRelation_unselected_nonneg a Q hQ hother
    change 0 ≤ Q.degree aR at hh
    rw [haR] at hh
    exact hh
  have hF : Γ.IsNef F := by
    change Γ.IsNef (simultaneousSupport (fun i => (R i).negative) aR τ)
    rw [haR]
    exact «Σ».outside_inner_unit_corrected_isNef R hR hne hdisj
      hpure P hP hfan hbound σ D hσ hDσ hout τ hτ0 hupper hrepair hinactive
  refine ⟨Γ, F, hF, «Σ».old_rays_subset_selected R hne hdisj,
    «Σ».outside_cone_mem_selected R hne hdisj hσ hout, ?_, ?_⟩
  · intro v hv
    change simultaneousSupport (fun i => (R i).negative) aR τ v = _
    rw [«Σ».selected_support_eq_old_on_outside_cone R aR τ hσ hout hv]
    exact congrFun haR v
  · intro v hv
    have hh := «Σ».selected_support_le_old_on_rays R hne hdisj aR τ hτ0 hv
    rw [congrFun haR v] at hh
    exact hh

end SmoothCompleteFan

end PaperVerification.ToricGeometry
end
end Source_ToricOutsideCorrections
-- END ORIGINAL PaperVerification.ToricOutsideCorrections


-- BEGIN ORIGINAL PaperVerification.ToricOutsideBoxes
section Source_ToricOutsideBoxes

-- original header: module

-- original header: public import PaperVerification.ToricOutsideCorrections

-- original header: @[expose] public section

/-!
# The original side-two boxes and the inner unit boxes

These are geometric containment statements in the original real polytope
and its actual topological interior. Every activated class and correction
used in their proofs is the exhaustive canonical construction.
-/

noncomputable section

namespace PaperVerification.ToricGeometry

open Set
open scoped BigOperators Classical

namespace LatticePolytope

variable {n : ℕ} (P : LatticePolytope n)

theorem normal_basis_vertex_active («Σ» : SmoothCompleteFan n)
    (v : Ambient n) (hv : v ∈ P.carrier)
    (d : Module.Basis (Fin n) ℤ (Lattice n))
    (hcone : P.normalCone v =
      (latticeRayCone (Finset.univ.image d) : Set (Ambient n))) (i : Fin n) :
    (dotProductEquiv ℝ (Fin n) (embed n (d i))) v = -(P.integralSupport (d i) : ℝ) := by
  have hnormal : embed n (d i) ∈ P.normalCone v := by
    rw [hcone]
    exact latticeRayCone_generator _ (Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩)
  have hh := (P.integralSupport_spec (d i) v hv).2.mpr hnormal
  linarith

/-- Proposition 5.2, with actual polytope containment and all activated
classes constructed in the proof. -/
theorem outside_side_two_box
    («Σ» : SmoothCompleteFan n) (hpure : «Σ».IsPure) (hP : P.Smooth)
    (hfan : «Σ».realCones = P.normalFan) (hbound : P.EdgesAtLeast n)
    (v : Ambient n) (hv : v ∈ P.carrier)
    (d : Module.Basis (Fin n) ℤ (Lattice n))
    (hd : Finset.univ.image d ∈ «Σ».cones)
    (hcone : P.normalCone v =
      (latticeRayCone (Finset.univ.image d) : Set (Ambient n)))
    (houtside : ∀ Q : «Σ».PrimitiveRelation, Q.IsCombinatoriallyContractible →
      Q.degree (fun w => (P.integralSupport w : ℝ)) < 2 * (Q.fiberDimension : ℝ) →
      ¬ Q.negative ⊆ Finset.univ.image d)
    (t : Fin n → ℝ) (ht : ∀ i, 0 ≤ t i ∧ t i ≤ 2) :
    v + ∑ i, t i • integralBasisReal (integralDualBasis d) i ∈ P.carrier := by
  apply P.corner_box_mem_of_vertices v _ 2 (by norm_num) ?_ t ht
  intro I
  let D := I.image d
  have hD : D ⊆ Finset.univ.image d := Finset.image_subset_image (Finset.subset_univ I)
  obtain ⟨Γ, F, hF, hrays, hΓd, hcoeff, hle⟩ :=
    «Σ».exists_outside_side_two_correction hpure P hP hfan hbound
      (Finset.univ.image d) D hd hD houtside
  have hmem := «Σ».box_corner_mem_of_refinement_nef Γ hrays
    (fun w => (P.integralSupport w : ℝ)) F hF d hΓd v
    (P.normal_basis_vertex_active «Σ» v hv d hcone) I 2
    (by
      intro i
      have hh := hcoeff (d i) (Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩)
      have hiD : d i ∈ D ↔ i ∈ I := by simp only [D, Finset.mem_image, d.injective.eq_iff]; simp
      simpa only [hiD] using hh)
    (by
      intro w hw
      have hh := hle w hw
      have hnonneg : 0 ≤ 2 * (if w ∈ D then (1 : ℝ) else 0) := by split_ifs <;> norm_num
      linarith)
  rwa [P.fanPolytope_integralSupport_eq «Σ» hfan] at hmem

/-- Section 7.2's inner unit box lies in the actual topological interior,
not merely in a symbolic adjoint polytope. -/
theorem outside_inner_unit_box
    («Σ» : SmoothCompleteFan n) (hpure : «Σ».IsPure) (hP : P.Smooth)
    (hfan : «Σ».realCones = P.normalFan) (hbound : P.EdgesAtLeast (n + 1))
    (v : Ambient n) (hv : v ∈ P.carrier)
    (d : Module.Basis (Fin n) ℤ (Lattice n))
    (hd : Finset.univ.image d ∈ «Σ».cones)
    (hcone : P.normalCone v =
      (latticeRayCone (Finset.univ.image d) : Set (Ambient n)))
    (houtside : ∀ Q : «Σ».PrimitiveRelation, Q.IsCombinatoriallyContractible →
      0 < 2 * (Q.fiberDimension : ℝ) + 1 -
        Q.degree (fun w => (P.integralSupport w : ℝ)) - Q.negativeCoefficientSum →
      ¬ Q.negative ⊆ Finset.univ.image d)
    (t : Fin n → ℝ) (ht : ∀ i, 0 ≤ t i ∧ t i ≤ 1) :
    (v + ∑ i, integralBasisReal (integralDualBasis d) i) +
      ∑ i, t i • integralBasisReal (integralDualBasis d) i ∈ interior P.carrier := by
  let a : Lattice n → ℝ := fun w => (P.integralSupport w : ℝ)
  let a' : Lattice n → ℝ := fun w => a w - 1
  let v' := v + ∑ i, integralBasisReal (integralDualBasis d) i
  have hv' (i : Fin n) :
      (dotProductEquiv ℝ (Fin n) (embed n (d i))) v' = -a' (d i) := by
    rw [show v' = v + ∑ j, integralBasisReal (integralDualBasis d) j from rfl,
      map_add, map_sum, P.normal_basis_vertex_active «Σ» v hv d hcone i]
    simp only [normal_basis_dual_pairing, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    dsimp only [a', a]
    ring
  have hvertices (I : Finset (Fin n)) :
      v' + (1 : ℝ) • (∑ i ∈ I, integralBasisReal (integralDualBasis d) i) ∈
        «Σ».fanPolytope a' := by
    let D := I.image d
    have hD : D ⊆ Finset.univ.image d := Finset.image_subset_image (Finset.subset_univ I)
    obtain ⟨Γ, F, hF, hrays, hΓd, hcoeff, hle⟩ :=
      «Σ».exists_outside_inner_unit_correction hpure P hP hfan hbound
        (Finset.univ.image d) D hd hD houtside
    apply «Σ».box_corner_mem_of_refinement_nef Γ hrays a' F hF d hΓd v' hv' I 1
    · intro i
      have hh := hcoeff (d i) (Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩)
      have hiD : d i ∈ D ↔ i ∈ I := by simp only [D, Finset.mem_image, d.injective.eq_iff]; simp
      simpa only [a', a, hiD, one_mul] using hh
    · intro w hw
      have hh := hle w hw
      have hnonneg : 0 ≤ (if w ∈ D then (1 : ℝ) else 0) := by split_ifs <;> norm_num
      change F w ≤ (P.integralSupport w : ℝ) - 1
      linarith
  have hbox := «Σ».box_mem_fanPolytope_of_vertices a' v' _ 1 zero_le_one hvertices t ht
  have hinterior := «Σ».fanPolytope_sub_pos_subset_interior a 1 zero_lt_one hbox
  rwa [P.fanPolytope_integralSupport_eq «Σ» hfan] at hinterior

/-- All ordinary unit boxes are contained under the original edge bound,
with the exact basis from any full normal cone. -/
theorem unit_box_of_edge_bound
    («Σ» : SmoothCompleteFan n) (hpure : «Σ».IsPure) (hP : P.Smooth)
    (hfan : «Σ».realCones = P.normalFan) {bound : ℕ}
    (hbound : P.EdgesAtLeast bound) (hn : n ≤ bound)
    (v : Ambient n) (hv : v ∈ P.carrier)
    (d : Module.Basis (Fin n) ℤ (Lattice n))
    (hd : Finset.univ.image d ∈ «Σ».cones)
    (hcone : P.normalCone v =
      (latticeRayCone (Finset.univ.image d) : Set (Ambient n)))
    (t : Fin n → ℝ) (ht : ∀ i, 0 ≤ t i ∧ t i ≤ 1) :
    v + ∑ i, t i • integralBasisReal (integralDualBasis d) i ∈ P.carrier := by
  apply P.corner_box_of_contractible_degrees «Σ» hpure hfan v hv d hd hcone 1 zero_le_one ?_ t ht
  intro Q hQ
  have hdQ := P.contractible_degree_lower_bound hP «Σ» hpure hfan hbound Q hQ
  have hdim := Q.contractible_dimension_bound hQ
  have hr : Q.fiberDimension ≤ bound := by omega
  have hrR : (Q.fiberDimension : ℝ) ≤ bound := by exact_mod_cast hr
  simpa only [one_mul] using hrR.trans hdQ

end LatticePolytope

end PaperVerification.ToricGeometry
end
end Source_ToricOutsideBoxes
-- END ORIGINAL PaperVerification.ToricOutsideBoxes


-- BEGIN ORIGINAL PaperVerification.ToricBundleFanPrimitive
section Source_ToricBundleFanPrimitive

-- original header: module

-- original header: public import PaperVerification.ToricBundleFan


-- original header: @[expose] public section
/-!
# Other primitive collections in a projective bundle fan

The exact fiber/base cone correspondence forces every primitive collection
other than the fiber simplex to be disjoint from that simplex.  Projection
therefore bounds its cardinality by the base dimension plus one.
-/

noncomputable section

namespace PaperVerification.ToricGeometry.SmoothCompleteFan.PrimitiveRelation

open scoped BigOperators Classical

variable {n : ℕ} {«Σ» : SmoothCompleteFan n} (R : «Σ».PrimitiveRelation)

theorem other_primitive_disjoint_fiber (hR : R.IsCombinatoriallyContractible)
    (hN : R.negative = ∅) {S : Finset (Lattice n)}
    (hS : «Σ».IsPrimitiveCollection S) (hne : S ≠ R.positive) :
    Disjoint S R.positive := by
  have hPnot : ¬ R.positive ⊆ S := by
    intro hPS
    have hproper : R.positive ⊂ S := Finset.ssubset_iff_subset_ne.mpr ⟨hPS, Ne.symm hne⟩
    exact R.primitive.2.1 (hS.2.2 R.positive hproper)
  have hJ : S ∩ R.positive ≠ R.positive := by
    intro he
    exact hPnot (he ▸ Finset.inter_subset_left)
  have hdisj : Disjoint (S \ R.positive) R.positive :=
    Finset.disjoint_left.mpr (fun v hv hvP => (Finset.mem_sdiff.mp hv).2 hvP)
  by_contra hnot
  have hproper : S \ R.positive ⊂ S := by
    refine Finset.ssubset_iff_subset_ne.mpr ⟨Finset.sdiff_subset, ?_⟩
    intro he
    exact hnot (he ▸ hdisj)
  have hD := hS.2.2 (S \ R.positive) hproper
  have hcone := (R.cone_union_fiber_iff hR hN Finset.inter_subset_right hdisj).mpr
    ⟨hJ, hD⟩
  have hpart : (S ∩ R.positive) ∪ (S \ R.positive) = S := by
    ext v
    simp only [Finset.mem_union, Finset.mem_inter, Finset.mem_sdiff]
    tauto
  exact hS.2.1 (hpart ▸ hcone)

namespace BundleCoordinates

variable {R} (c : R.BundleCoordinates)

theorem other_primitive_card_le (hR : R.IsCombinatoriallyContractible)
    (hN : R.negative = ∅) {S : Finset (Lattice n)}
    (hS : «Σ».IsPrimitiveCollection S) (hne : S ≠ R.positive) :
    S.card ≤ (n - c.fiberIndices.card) + 1 := by
  have hdisj := R.other_primitive_disjoint_fiber hR hN hS hne
  obtain ⟨v, hv⟩ := «Σ».primitiveCollection_nonempty hS
  have hproper : S.erase v ⊂ S := Finset.erase_ssubset hv
  have hcone := hS.2.2 (S.erase v) hproper
  have hdrays : S.erase v ⊆ «Σ».rays := (Finset.erase_subset v S).trans hS.1
  have hdP : Disjoint (S.erase v) R.positive := hdisj.mono_left (Finset.erase_subset v S)
  have hbase := (c.nonfiber_cone_iff_projected_cone hR hN hdrays hdP).mp hcone
  have hsize := c.baseFan.card_cone_le hbase
  have hinj : Set.InjOn c.quotientLattice (S.erase v : Set (Lattice n)) := by
    intro x hx y hy hxy
    exact c.quotient_injective_nonfiber hR hN
      (Finset.mem_sdiff.mpr ⟨hdrays hx, fun hxP => Finset.disjoint_left.mp hdP hx hxP⟩)
      (Finset.mem_sdiff.mpr ⟨hdrays hy, fun hyP => Finset.disjoint_left.mp hdP hy hyP⟩) hxy
  rw [Finset.card_image_of_injOn hinj, Finset.card_erase_of_mem hv] at hsize
  have hnonempty : 0 < S.card := Finset.card_pos.mpr ⟨v, hv⟩
  omega

end BundleCoordinates

end PaperVerification.ToricGeometry.SmoothCompleteFan.PrimitiveRelation
end
end Source_ToricBundleFanPrimitive
-- END ORIGINAL PaperVerification.ToricBundleFanPrimitive


-- BEGIN ORIGINAL PaperVerification.ToricFaceDegreeBounds
section Source_ToricFaceDegreeBounds

-- original header: module

-- original header: public import PaperVerification.ToricQuotientFacePolytopes
-- original header: public import PaperVerification.ToricNefBoxes
-- original header: public import PaperVerification.ToricBundleFanPrimitive

-- original header: @[expose] public section

/-!
# Real displaced face degrees and tangent boxes

Restricting the genuine nef proportional remainder proves the edge-degree
reserve for arbitrary real heights, without pretending a nonintegral slice
is a lattice polytope. The fiber relation and the proved bound on all other
primitive collections then supply whole tangent boxes, including nef endpoints.
-/

noncomputable section

namespace PaperVerification.ToricGeometry

open Set
open scoped BigOperators Classical

variable {n : ℕ}

theorem quotientFaceOrigin_sub (a c : Lattice n → ℝ)
    (b : Module.Basis (Fin n) ℤ (Lattice n)) (I : Finset (Fin n)) :
    quotientFaceOrigin (a - c) b I = quotientFaceOrigin a b I - quotientFaceOrigin c b I := by
  simp only [quotientFaceOrigin, Pi.sub_apply, sub_smul, Finset.sum_sub_distrib, neg_sub]
  abel

theorem quotientFaceOrigin_smul (t : ℝ) (a : Lattice n → ℝ)
    (b : Module.Basis (Fin n) ℤ (Lattice n)) (I : Finset (Fin n)) :
    quotientFaceOrigin (t • a) b I = t • quotientFaceOrigin a b I := by
  simp only [quotientFaceOrigin, Pi.smul_apply, smul_eq_mul, mul_smul,
    ← Finset.smul_sum, smul_neg]

namespace SmoothCompleteFan

variable («Σ» : SmoothCompleteFan n)
    (b : Module.Basis (Fin n) ℤ (Lattice n)) (I : Finset (Fin n))
    (hF : I.image b ∈ «Σ».cones)

theorem faceSupport_sub (a c : Lattice n → ℝ) :
    «Σ».faceSupport b I hF (a - c) = «Σ».faceSupport b I hF a - «Σ».faceSupport b I hF c := by
  funext u
  by_cases hu : u ∈ («Σ».completeQuotientStarFan b I hF).rays
  · simp only [faceSupport, dif_pos hu, Pi.sub_apply, quotientFaceOrigin_sub, map_sub]
    ring
  · simp only [faceSupport, dif_neg hu, Pi.sub_apply, sub_zero]

theorem faceSupport_smul (t : ℝ) (a : Lattice n → ℝ) :
    «Σ».faceSupport b I hF (t • a) = t • «Σ».faceSupport b I hF a := by
  funext u
  by_cases hu : u ∈ («Σ».completeQuotientStarFan b I hF).rays
  · simp only [faceSupport, dif_pos hu, Pi.smul_apply, quotientFaceOrigin_smul,
      map_smul, smul_eq_mul]
    ring
  · simp only [faceSupport, dif_neg hu, Pi.smul_apply, smul_zero]

/-- Original integral face degrees inherit the literal ambient edge bound. -/
theorem faceSupport_contractible_degree_lower_bound_of_edges (hpure : «Σ».IsPure)
    (a : Lattice n → ℤ) (ha : «Σ».IsStrictSupport (fun u => (a u : ℝ)))
    {e : ℕ} (hedges : («Σ».supportLatticePolytope hpure a ha).EdgesAtLeast e)
    (R : («Σ».completeQuotientStarFan b I hF).PrimitiveRelation)
    (hR : R.IsCombinatoriallyContractible) :
    (e : ℝ) ≤ R.degree («Σ».faceSupport b I hF (fun u => (a u : ℝ))) := by
  let Ψ := «Σ».completeQuotientStarFan b I hF
  let c := «Σ».faceSupportLattice b I hF a
  have hpureΨ : Ψ.IsPure := «Σ».completeQuotientStarFan_isPure hpure b I hF
  have hc : Ψ.IsStrictSupport (fun u => (c u : ℝ)) := by
    rw [show (fun u => (c u : ℝ)) = «Σ».faceSupport b I hF (fun u => (a u : ℝ)) from
      «Σ».faceSupportLattice_cast b I hF a]
    exact «Σ».faceSupport_isStrictSupport b I hF _ ha
  let P := «Σ».supportLatticePolytope hpure a ha
  let Q := Ψ.supportLatticePolytope hpureΨ c hc
  have himage : (quotientFaceIntegralChart a b I).realMap '' Q.carrier =
      «Σ».supportFace (fun u => (a u : ℝ)) (I.image b) := by
    rw [Ψ.supportLatticePolytope_carrier]
    exact «Σ».quotientFaceIntegralChart_image_fanPolytope b I hF hpure a
      (IsStrictSupport.isNef «Σ» ha)
  have hface : IsExtreme ℝ P.carrier
      («Σ».supportFace (fun u => (a u : ℝ)) (I.image b)) := by
    rw [«Σ».supportLatticePolytope_carrier]
    exact «Σ».supportFace_isExtreme _ _ (fun u hu => «Σ».ray_mem_of_mem_cone hF hu)
  have hQedges := P.edgesAtLeast_face_chart hedges _ hface Q
    (quotientFaceIntegralChart a b I) himage
  have hd := Ψ.support_contractible_degree_lower_bound_of_edges hpureΨ c hc hQedges R hR
  rw [show (fun u => (c u : ℝ)) = «Σ».faceSupport b I hF (fun u => (a u : ℝ)) from
    «Σ».faceSupportLattice_cast b I hF a] at hd
  exact hd

/-- Every contracted face degree loses at most the total displacement,
also at arbitrary real heights and at the nef endpoint. -/
theorem displaced_faceSupport_degree_lower_bound (hpure : «Σ».IsPure)
    (a : Lattice n → ℤ) (ha : «Σ».IsStrictSupport (fun u => (a u : ℝ)))
    {e : ℕ} (he : 0 < e)
    (hedges : («Σ».supportLatticePolytope hpure a ha).EdgesAtLeast e)
    (h : Lattice n → ℝ) (hh : ∀ u ∈ I.image b, 0 ≤ h u)
    (hbudget : (∑ u ∈ I.image b, h u) ≤ e)
    (R : («Σ».completeQuotientStarFan b I hF).PrimitiveRelation)
    (hR : R.IsCombinatoriallyContractible) :
    (e : ℝ) - ∑ u ∈ I.image b, h u ≤ R.degree
      («Σ».faceSupport b I hF (displacedSupport (fun u => (a u : ℝ)) (I.image b) h)) := by
  let H := ∑ u ∈ I.image b, h u
  let c : ℝ := 1 - H / e
  have heR : (0 : ℝ) < e := by exact_mod_cast he
  have hc : 0 ≤ c := sub_nonneg.mpr ((div_le_one heR).mpr hbudget)
  have hnef := «Σ».displacedSupport_nef_difference hpure a ha e heR
    («Σ».support_extremal_degree_lower_bound_of_edges hpure a ha hedges)
    (I.image b) h hh
  have hrestricted := «Σ».faceSupport_isNef b I hF _ hnef
  rw [«Σ».faceSupport_sub, «Σ».faceSupport_smul] at hrestricted
  have hd := R.degree_nonneg_of_nef hrestricted
  rw [R.degree_sub, R.degree_smul] at hd
  have hbase := «Σ».faceSupport_contractible_degree_lower_bound_of_edges b I hF hpure
    a ha hedges R hR
  have hm := mul_le_mul_of_nonneg_left hbase hc
  have hcvalue : c * e = (e : ℝ) - H := by
    dsimp only [c]
    rw [sub_mul, one_mul, div_mul_cancel₀ _ heR.ne']
  change 0 ≤ R.degree _ - c * R.degree _ at hd
  rw [hcvalue] at hm
  change (e : ℝ) - H ≤ _
  linarith

end SmoothCompleteFan

namespace SmoothCompleteFan.PrimitiveRelation.BundleCoordinates

variable {«Σ» : SmoothCompleteFan n} {R : «Σ».PrimitiveRelation} (c : R.BundleCoordinates)

/-- Every actual contractible primitive degree satisfies the tangent box
criterion from the fiber degree and the actual base-dimension floor. -/
theorem all_contractible_degrees_of_fiber_and_base
    (hR : R.IsCombinatoriallyContractible) (hN : R.negative = ∅)
    (a : Lattice n → ℝ) (side : ℝ) (hside : 0 ≤ side)
    (hfiber : side * R.fiberDimension ≤ R.degree a)
    (hbase : ∀ S : «Σ».PrimitiveRelation, S.IsCombinatoriallyContractible →
      S.positive ≠ R.positive → side * ((n - c.fiberIndices.card : ℕ) : ℝ) ≤ S.degree a) :
    ∀ S : «Σ».PrimitiveRelation, S.IsCombinatoriallyContractible →
      side * S.fiberDimension ≤ S.degree a := by
  intro S hS
  by_cases hSR : S.positive = R.positive
  · have hdim : S.fiberDimension = R.fiberDimension := by simp only [PrimitiveRelation.fiberDimension, hSR]
    rw [hdim, S.degree_unique R hSR]
    exact hfiber
  · have hcard := c.other_primitive_card_le hR hN S.primitive hSR
    have hdim : S.fiberDimension ≤ n - c.fiberIndices.card := by
      unfold PrimitiveRelation.fiberDimension
      omega
    have hdimR : (S.fiberDimension : ℝ) ≤ ((n - c.fiberIndices.card : ℕ) : ℝ) := by exact_mod_cast hdim
    exact (mul_le_mul_of_nonneg_left hdimR hside).trans (hbase S hS hSR)


/-- A fiber degree and the actual nonfiber degree floor imply every
corner box on the genuine bundle fan. Degenerate nef supports are allowed. -/
theorem corner_box_of_fiber_and_base_degrees
    (hR : R.IsCombinatoriallyContractible) (hN : R.negative = ∅) (hpure : «Σ».IsPure)
    (H : Lattice n → ℤ) (hH : «Σ».IsStrictSupport (fun u => (H u : ℝ)))
    (a : Lattice n → ℝ) (side : ℝ) (hside : 0 ≤ side)
    (hfiber : side * R.fiberDimension ≤ R.degree a)
    (hbase : ∀ S : «Σ».PrimitiveRelation, S.IsCombinatoriallyContractible →
      S.positive ≠ R.positive → side * ((n - c.fiberIndices.card : ℕ) : ℝ) ≤ S.degree a)
    (s : «Σ».fullCones) (t : Fin n → ℝ) (ht : ∀ i, 0 ≤ t i ∧ t i ≤ side) :
    «Σ».cartierPoint a s + ∑ i, t i • «Σ».cartierBasis s i ∈ «Σ».fanPolytope a :=
  «Σ».corner_box_mem_fanPolytope hpure H hH a side hside
    (c.all_contractible_degrees_of_fiber_and_base hR hN a side hside hfiber hbase) s t ht

/-- The exact canonical tangent degree criterion for every actual
contractible primitive relation. -/
theorem all_adjoint_contractible_degrees_of_fiber_and_base
    (hR : R.IsCombinatoriallyContractible) (hN : R.negative = ∅)
    (a : Lattice n → ℝ)
    (hfiber : (2 * R.fiberDimension + 1 : ℕ) ≤ R.degree a)
    (hbase : ∀ S : «Σ».PrimitiveRelation, S.IsCombinatoriallyContractible →
      S.positive ≠ R.positive → (2 * (n - c.fiberIndices.card) + 1 : ℕ) ≤ S.degree a) :
    ∀ S : «Σ».PrimitiveRelation, S.IsCombinatoriallyContractible →
      (S.fiberDimension : ℝ) ≤ S.degree (fun u => a u - 1) := by
  intro S hS
  have hpositive : 0 < S.positive.card := Finset.card_pos.mpr («Σ».primitiveCollection_nonempty S.primitive)
  have hdim : S.positive.card = S.fiberDimension + 1 := by
    unfold PrimitiveRelation.fiberDimension
    omega
  have hdeg : S.degree (fun u => a u - 1) =
      S.degree a - S.positive.card + ∑ v ∈ S.negative, (S.coefficient v : ℝ) := by
    simp only [PrimitiveRelation.degree, Finset.sum_sub_distrib, mul_sub, mul_one,
      Finset.sum_const, nsmul_eq_mul, mul_one]
    ring
  have hneg : 0 ≤ ∑ v ∈ S.negative, (S.coefficient v : ℝ) :=
    Finset.sum_nonneg (fun v hv => Nat.cast_nonneg _)
  rw [hdeg]
  by_cases hSR : S.positive = R.positive
  · have hdimSR : S.fiberDimension = R.fiberDimension := by
      simp only [PrimitiveRelation.fiberDimension, hSR]
    have hdegree := S.degree_unique R hSR a
    have hf : (2 : ℝ) * S.fiberDimension + 1 ≤ S.degree a := by
      simpa only [hdimSR, hdegree, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one] using hfiber
    rw [hdim, Nat.cast_add, Nat.cast_one]
    linarith
  · have hcard := c.other_primitive_card_le hR hN S.primitive hSR
    have hcardR : (S.positive.card : ℝ) ≤ (n - c.fiberIndices.card : ℕ) + 1 := by exact_mod_cast hcard
    have hb := hbase S hS hSR
    have hbR : (2 : ℝ) * (n - c.fiberIndices.card : ℕ) + 1 ≤ S.degree a := by
      simpa only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one] using hb
    have hdimR : (S.positive.card : ℝ) = (S.fiberDimension : ℝ) + 1 := by exact_mod_cast hdim
    linarith

/-- The canonical unit-box case: the fiber parent has degree at least
`2r+1`, and every other parent degree is at least `2b+1`. -/
theorem adjoint_unit_box_of_fiber_and_base_degrees
    (hR : R.IsCombinatoriallyContractible) (hN : R.negative = ∅) (hpure : «Σ».IsPure)
    (H : Lattice n → ℤ) (hH : «Σ».IsStrictSupport (fun u => (H u : ℝ)))
    (a : Lattice n → ℝ)
    (hfiber : (2 * R.fiberDimension + 1 : ℕ) ≤ R.degree a)
    (hbase : ∀ S : «Σ».PrimitiveRelation, S.IsCombinatoriallyContractible →
      S.positive ≠ R.positive → (2 * (n - c.fiberIndices.card) + 1 : ℕ) ≤ S.degree a)
    (s : «Σ».fullCones) (t : Fin n → ℝ) (ht : ∀ i, 0 ≤ t i ∧ t i ≤ 1) :
    «Σ».cartierPoint (fun u => a u - 1) s + ∑ i, t i • «Σ».cartierBasis s i ∈
      «Σ».fanPolytope (fun u => a u - 1) := by
  apply «Σ».corner_box_mem_fanPolytope hpure H hH (fun u => a u - 1) 1 (by norm_num) ?_ s t ht
  intro S hS
  simpa only [one_mul] using
    c.all_adjoint_contractible_degrees_of_fiber_and_base hR hN a hfiber hbase S hS

end SmoothCompleteFan.PrimitiveRelation.BundleCoordinates

end PaperVerification.ToricGeometry
end
end Source_ToricFaceDegreeBounds
-- END ORIGINAL PaperVerification.ToricFaceDegreeBounds


-- BEGIN ORIGINAL PaperVerification.ToricFocusQuotientRelation
section Source_ToricFocusQuotientRelation

-- original header: module

-- original header: public import PaperVerification.ToricQuotientFaceSupport
-- original header: public import PaperVerification.ToricPrimitiveOverlap

-- original header: @[expose] public section

/-!
# The actual projective-fiber relation on a contracted face

Quotienting the focus of a combinatorially contractible primitive relation
produces an actual primitive relation with empty focus in the saturated
quotient-star fan. Its replacement property, number of positive rays, and
support degree are proved from the original fan, rather than supplied as
bundle assumptions.
-/

noncomputable section

namespace PaperVerification.ToricGeometry.SmoothCompleteFan.PrimitiveRelation

open Set
open scoped BigOperators Classical

variable {n : ℕ} {«Σ» : SmoothCompleteFan n} (R : «Σ».PrimitiveRelation)
    (hR : R.IsCombinatoriallyContractible)
    (b : Module.Basis (Fin n) ℤ (Lattice n)) (I : Finset (Fin n))
    (hI : I.image b = R.negative)

include hR in
theorem positive_lies_in_focus_star {v : Lattice n} (hv : v ∈ R.positive) :
    ∃ s ∈ «Σ».cones, R.negative ⊆ s ∧ v ∈ s \ R.negative := by
  have hcard := («Σ».primitiveCollection_card_bounds R.primitive).1
  obtain ⟨u, hu, huv⟩ := Finset.exists_mem_ne (by omega : 1 < R.positive.card) v
  refine ⟨R.positive.erase u ∪ R.negative, R.contractible_core_cone hR hu,
    Finset.subset_union_right, ?_⟩
  exact Finset.mem_sdiff.mpr
    ⟨Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨huv.symm, hv⟩),
      fun hvN => Finset.disjoint_left.mp R.disjoint hv hvN⟩

include hR hI in
theorem focusQuotient_injective_positive :
    Set.InjOn (coneQuotientLattice b I) (R.positive : Set (Lattice n)) := by
  intro v hv w hw he
  obtain ⟨s, hs, hNs, hvs⟩ := R.positive_lies_in_focus_star hR hv
  obtain ⟨t, ht, hNt, hwt⟩ := R.positive_lies_in_focus_star hR hw
  rw [← hI] at hNs hvs hNt hwt
  exact «Σ».coneQuotient_injective_star_rays b I hs ht hNs hNt hvs hwt he

include hR in
theorem focusQuotient_positive_ray {v : Lattice n} (hv : v ∈ R.positive) :
    coneQuotientLattice b I v ∈
      («Σ».completeQuotientStarFan b I (hI.symm ▸ R.negative_cone)).rays := by
  obtain ⟨s, hs, hNs, hvs⟩ := R.positive_lies_in_focus_star hR hv
  rw [← hI] at hNs hvs
  exact «Σ».projected_starRay_mem b I _ hs hNs hvs

include hR in
/-- The projected positive rays form a genuine primitive collection.
Minimality and failure to be a cone are both established in the quotient fan. -/
theorem focusQuotient_positive_primitive :
    («Σ».completeQuotientStarFan b I (hI.symm ▸ R.negative_cone)).IsPrimitiveCollection
      (R.positive.image (coneQuotientLattice b I)) := by
  let Ψ := «Σ».completeQuotientStarFan b I (hI.symm ▸ R.negative_cone)
  let P := R.positive.image (coneQuotientLattice b I)
  refine ⟨?_, ?_, ?_⟩
  · intro u hu
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hu
    exact R.focusQuotient_positive_ray hR b I hI hv
  · intro hP
    obtain ⟨s, hs, hIs, hPs⟩ := («Σ».mem_quotientStarCones b I P).mp hP
    have hsub : R.positive ⊆ s := by
      intro v hv
      have hvP : coneQuotientLattice b I v ∈ P := Finset.mem_image.mpr ⟨v, hv, rfl⟩
      rw [hPs] at hvP
      obtain ⟨w, hw, he⟩ := Finset.mem_image.mp hvP
      obtain ⟨t, ht, hNt, hvt⟩ := R.positive_lies_in_focus_star hR hv
      rw [← hI] at hNt hvt
      have hwv := «Σ».coneQuotient_injective_star_rays b I hs ht hIs hNt hw hvt he
      exact hwv ▸ (Finset.mem_sdiff.mp hw).1
    exact R.primitive.2.1 («Σ».downward s hs R.positive hsub)
  · intro Q hQ
    have hQP := (Finset.ssubset_iff_subset_ne.mp hQ).1
    have hnot : ¬ P ⊆ Q := by
      intro hPQ
      exact (ne_of_lt hQ) (Finset.Subset.antisymm hQP hPQ)
    obtain ⟨u, huP, huQ⟩ := Finset.not_subset.mp hnot
    obtain ⟨v, hv, hvu⟩ := Finset.mem_image.mp huP
    let C := R.positive.erase v ∪ R.negative
    have hC : C ∈ «Σ».cones := R.contractible_core_cone hR hv
    have hIC : I.image b ⊆ C := by
      rw [hI]
      exact Finset.subset_union_right
    let D := (C \ I.image b).image (coneQuotientLattice b I)
    have hD : D ∈ Ψ.cones := («Σ».mem_quotientStarCones b I D).mpr ⟨C, hC, hIC, rfl⟩
    apply Ψ.downward D hD Q
    intro w hw
    obtain ⟨z, hz, hzw⟩ := Finset.mem_image.mp (hQP hw)
    have hzv : z ≠ v := by
      intro he
      apply huQ
      have hwu : w = u := hzw.symm.trans (he ▸ hvu)
      exact hwu ▸ hw
    refine Finset.mem_image.mpr ⟨z, Finset.mem_sdiff.mpr ⟨?_, ?_⟩, hzw⟩
    · exact Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨hzv, hz⟩)
    · rw [hI]
      exact fun hzN => Finset.disjoint_left.mp R.disjoint hz hzN

/-- The literal primitive relation on the quotient-star fan. Its focus is
empty because the original positive sum belongs to the removed normal span. -/
def focusQuotientRelation :
    («Σ».completeQuotientStarFan b I (hI.symm ▸ R.negative_cone)).PrimitiveRelation where
  positive := R.positive.image (coneQuotientLattice b I)
  negative := ∅
  coefficient := fun _ => 0
  primitive := R.focusQuotient_positive_primitive hR b I hI
  negative_cone := («Σ».completeQuotientStarFan b I (hI.symm ▸ R.negative_cone)).empty_mem
  coefficient_pos := by simp
  equation := by
    rw [Finset.sum_empty, Finset.sum_image]
    · rw [← map_sum, R.equation, map_sum]
      apply Finset.sum_eq_zero
      intro v hv
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp (hI.symm ▸ hv)
      rw [map_smul, coneQuotientLattice_of_mem b I
        (Finset.mem_image.mpr ⟨i, hi, rfl⟩), smul_zero]
    · exact R.focusQuotient_injective_positive hR b I hI

theorem focusQuotientRelation_negative :
    (R.focusQuotientRelation hR b I hI).negative = ∅ := rfl

theorem focusQuotientRelation_fiberDimension :
    (R.focusQuotientRelation hR b I hI).fiberDimension = R.fiberDimension := by
  unfold fiberDimension
  change (R.positive.image (coneQuotientLattice b I)).card - 1 = R.positive.card - 1
  rw [Finset.card_image_of_injOn (R.focusQuotient_injective_positive hR b I hI)]

/-- The full replacement condition descends to the actual quotient fan. -/
theorem focusQuotientRelation_contractible :
    (R.focusQuotientRelation hR b I hI).IsCombinatoriallyContractible := by
  let Ψ := «Σ».completeQuotientStarFan b I (hI.symm ▸ R.negative_cone)
  intro ν hν hdisj hNν u hu
  change u ∈ R.positive.image (coneQuotientLattice b I) at hu
  obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hu
  obtain ⟨s, hs, hIs, hνs⟩ := («Σ».mem_quotientStarCones b I ν).mp hν
  have hNs : R.negative ⊆ s := hI ▸ hIs
  have hvN : v ∉ R.negative := fun hvN => Finset.disjoint_left.mp R.disjoint hv hvN
  have hvs : v ∉ s := by
    intro hvs
    have hvν : coneQuotientLattice b I v ∈ ν := by
      rw [hνs]
      exact Finset.mem_image.mpr ⟨v, Finset.mem_sdiff.mpr ⟨hvs, hI.symm ▸ hvN⟩, rfl⟩
    apply Finset.disjoint_left.mp hdisj hvν
    exact Finset.mem_union_left _ (Finset.mem_image.mpr ⟨v, hv, rfl⟩)
  let C := R.positive.erase v ∪ s
  have hC : C ∈ «Σ».cones := R.fill_cone_with_positive_except hR hs hNs hv hvs
  have hIC : I.image b ⊆ C := hIs.trans Finset.subset_union_right
  let D := (C \ I.image b).image (coneQuotientLattice b I)
  have hD : D ∈ Ψ.cones := («Σ».mem_quotientStarCones b I D).mpr ⟨C, hC, hIC, rfl⟩
  apply Ψ.downward D hD
  intro w hw
  change w ∈ (R.positive.image (coneQuotientLattice b I)).erase
      (coneQuotientLattice b I v) ∪ ∅ ∪ ν at hw
  rcases Finset.mem_union.mp hw with hwP | hwν
  · have hwP := Finset.mem_union.mp hwP
    rcases hwP with hwP | hwempty
    · obtain ⟨hwne, hwP⟩ := Finset.mem_erase.mp hwP
      obtain ⟨z, hz, hzw⟩ := Finset.mem_image.mp hwP
      have hzv : z ≠ v := fun he => hwne (hzw.symm.trans (congrArg _ he))
      refine Finset.mem_image.mpr ⟨z, Finset.mem_sdiff.mpr ⟨?_, ?_⟩, hzw⟩
      · exact Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨hzv, hz⟩)
      · rw [hI]
        exact fun hzN => Finset.disjoint_left.mp R.disjoint hz hzN
    · simp at hwempty
  · rw [hνs] at hwν
    obtain ⟨z, hz, hzw⟩ := Finset.mem_image.mp hwν
    exact Finset.mem_image.mpr ⟨z, Finset.mem_sdiff.mpr
      ⟨Finset.mem_union_right _ (Finset.mem_sdiff.mp hz).1,
        (Finset.mem_sdiff.mp hz).2⟩, hzw⟩

/-- Restriction preserves the actual degree of the contracted class.
The affine-origin correction cancels the original negative coefficients. -/
theorem focusQuotientRelation_degree (a : Lattice n → ℝ) :
    (R.focusQuotientRelation hR b I hI).degree
      («Σ».faceSupport b I (hI.symm ▸ R.negative_cone) a) = R.degree a := by
  let o := quotientFaceOrigin a b I
  let f : Ambient n →ₗ[ℝ] ℝ := dotProductEquiv ℝ (Fin n) o
  have hp (v : Lattice n) (hv : v ∈ R.positive) :
      «Σ».faceSupport b I (hI.symm ▸ R.negative_cone) a (coneQuotientLattice b I v) =
        a v + f (embed n v) := by
    obtain ⟨s, hs, hNs, hvs⟩ := R.positive_lies_in_focus_star hR hv
    rw [← hI] at hNs hvs
    rw [«Σ».faceSupport_projected b I _ a hs hNs hvs]
    congr 1
    simpa [f, o, dotProductEquiv] using
      (dotProduct_comm (embed n v) (quotientFaceOrigin a b I))
  have hnegative (v : Lattice n) (hv : v ∈ R.negative) : f (embed n v) = -a v := by
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp (hI.symm ▸ hv)
    change (dotProductEquiv ℝ (Fin n) o) (embed n (b i)) = _
    rw [show (dotProductEquiv ℝ (Fin n) o) (embed n (b i)) =
        (dotProductEquiv ℝ (Fin n) (embed n (b i))) o from by
          simpa [dotProductEquiv] using (dotProduct_comm o (embed n (b i))),
      normal_pairing_eq_dual_coordinate, quotientFaceOrigin_coordinate, if_pos hi]
  have hsum : (∑ v ∈ R.positive, f (embed n v)) =
      -(∑ v ∈ R.negative, (R.coefficient v : ℝ) * a v) := by
    rw [← map_sum, ← map_sum, R.equation, map_sum, map_sum]
    simp only [embed_int_smul, Int.cast_natCast, map_smul, smul_eq_mul]
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro v hv
    rw [hnegative v hv, mul_neg]
  change (∑ u ∈ R.positive.image (coneQuotientLattice b I),
      «Σ».faceSupport b I (hI.symm ▸ R.negative_cone) a u) - 0 = _
  rw [sub_zero, Finset.sum_image]
  · rw [Finset.sum_congr rfl hp, Finset.sum_add_distrib, hsum]
    rfl
  · exact R.focusQuotient_injective_positive hR b I hI

end PaperVerification.ToricGeometry.SmoothCompleteFan.PrimitiveRelation
end
end Source_ToricFocusQuotientRelation
-- END ORIGINAL PaperVerification.ToricFocusQuotientRelation


-- BEGIN ORIGINAL PaperVerification.ToricFocusHeightDegrees
section Source_ToricFocusHeightDegrees

-- original header: module

-- original header: public import PaperVerification.ToricFaceDegreeBounds
-- original header: public import PaperVerification.ToricFocusQuotientRelation
-- original header: public import PaperVerification.ToricSelectedDegreeEstimates

-- original header: @[expose] public section

/-!
# Exact fiber degrees of arbitrary real normal-height slices

On the selected focus, each subtracted facet coefficient contributes with
its actual positive primitive-relation coefficient. The lower estimate
retains a baseline height, which is zero for ordinary boxes and one for
inner boxes. All coefficients are read from the genuine lattice relation.
-/

noncomputable section

namespace PaperVerification.ToricGeometry.SmoothCompleteFan.PrimitiveRelation

open scoped BigOperators Classical

variable {n : ℕ} {«Σ» : SmoothCompleteFan n} (R : «Σ».PrimitiveRelation)

theorem degree_displaced_focus (a : Lattice n → ℝ) (h : Lattice n → ℝ) :
    R.degree (displacedSupport a R.negative h) =
      R.degree a + ∑ u ∈ R.negative, (R.coefficient u : ℝ) * h u := by
  rw [displacedSupport, R.degree_sub]
  have hp : (∑ u ∈ R.positive, facetWeight R.negative h u) = 0 := by
    apply Finset.sum_eq_zero
    intro u hu
    have hn : u ∉ R.negative := fun hh => Finset.disjoint_left.mp R.disjoint hu hh
    simp only [facetWeight, if_neg hn]
  have hn : (∑ u ∈ R.negative, (R.coefficient u : ℝ) * facetWeight R.negative h u) =
      ∑ u ∈ R.negative, (R.coefficient u : ℝ) * h u := by
    apply Finset.sum_congr rfl
    intro u hu
    simp only [facetWeight, if_pos hu]
  simp only [degree, hp, hn]
  ring

theorem weighted_focus_height_lower
    (hne : R.negative.Nonempty) (base : ℝ) (h : Lattice n → ℝ)
    (hh : ∀ u ∈ R.negative, base ≤ h u) :
    base * R.negativeCoefficientSum + (R.minimumCoefficient hne : ℝ) *
      ((∑ u ∈ R.negative, h u) - base * R.negative.card) ≤
      ∑ u ∈ R.negative, (R.coefficient u : ℝ) * h u := by
  have hterm (u : Lattice n) (hu : u ∈ R.negative) :
      base * (R.coefficient u : ℝ) + (R.minimumCoefficient hne : ℝ) * (h u - base) ≤
        (R.coefficient u : ℝ) * h u := by
    have hm : (R.minimumCoefficient hne : ℝ) ≤ R.coefficient u := by
      exact_mod_cast (R.minimumCoefficient_spec hne).2.2 u hu
    nlinarith [mul_nonneg (sub_nonneg.mpr hm) (sub_nonneg.mpr (hh u hu))]
  have hsum := Finset.sum_le_sum hterm
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_sub_distrib,
    Finset.sum_const, nsmul_eq_mul, negativeCoefficientSum] at hsum ⊢
  nlinarith

theorem degree_displaced_focus_lower
    (hne : R.negative.Nonempty) (a : Lattice n → ℝ)
    (base : ℝ) (h : Lattice n → ℝ) (hh : ∀ u ∈ R.negative, base ≤ h u) :
    R.degree a + base * R.negativeCoefficientSum + (R.minimumCoefficient hne : ℝ) *
      ((∑ u ∈ R.negative, h u) - base * R.negative.card) ≤
      R.degree (displacedSupport a R.negative h) := by
  rw [R.degree_displaced_focus]
  have hw := R.weighted_focus_height_lower hne base h hh
  linarith

end PaperVerification.ToricGeometry.SmoothCompleteFan.PrimitiveRelation
end
end Source_ToricFocusHeightDegrees
-- END ORIGINAL PaperVerification.ToricFocusHeightDegrees


-- BEGIN ORIGINAL PaperVerification.ToricSliceBoxCoordinates
section Source_ToricSliceBoxCoordinates

-- original header: module

-- original header: public import PaperVerification.ToricQuotientFaceSupport
-- original header: public import PaperVerification.ToricDisplacedSupport
-- original header: public import PaperVerification.ToricStarBoxCoordinates
-- original header: public import PaperVerification.ToricNefBoxGeometry

-- original header: @[expose] public section

/-!
# Exact box coordinates in the saturated quotient slice

In a full old normal basis the complementary projected rays are the
standard integral basis.  The quotient tangent coordinates of a sheared
box are its unchanged tangent box coordinates.  These are identities of
actual vectors and affine maps, for arbitrary real normal heights.
-/

noncomputable section

namespace PaperVerification.ToricGeometry

open Set
open scoped BigOperators Classical

variable {n : ℕ}

theorem integralDualBasis_standard :
    integralDualBasis (Pi.basisFun ℤ (Fin n)) = Pi.basisFun ℤ (Fin n) := by
  apply DFunLike.ext
  intro i
  funext k
  have hh := integralDualBasis_pairing (Pi.basisFun ℤ (Fin n)) i (Pi.basisFun ℤ (Fin n) k)
  simpa [Pi.basisFun_apply, Pi.single_apply, Module.Basis.repr_self_apply, eq_comm] using hh

theorem integralBasisReal_standard_apply (i : Fin n) :
    integralBasisReal (Pi.basisFun ℤ (Fin n)) i = Pi.basisFun ℝ (Fin n) i := by
  rw [integralBasisReal_apply]
  funext k
  simp [Pi.basisFun_apply, Pi.single_apply, embed]

theorem standard_normal_pairing (i : Fin n) (x : Ambient n) :
    (dotProductEquiv ℝ (Fin n) (embed n (Pi.basisFun ℤ (Fin n) i))) x = x i := by
  simp [dotProductEquiv, dotProduct, Pi.basisFun_apply, Pi.single_apply, embed]

theorem coneQuotientLattice_complementary_basis
    (b : Module.Basis (Fin n) ℤ (Lattice n)) (I : Finset (Fin n))
    (j : Fin (n - I.card)) :
    coneQuotientLattice b I (b (complementaryEmbedding I j)) =
      Pi.basisFun ℤ (Fin (n - I.card)) j := by
  funext k
  change b.repr (b (complementaryEmbedding I j)) (complementaryEmbedding I k) = _
  simp only [Module.Basis.repr_self_apply, (complementaryEmbedding I).injective.eq_iff,
    Pi.basisFun_apply, Pi.single_apply]
  split_ifs <;> simp_all

theorem quotientFaceMap_complementary_coordinate (a : Lattice n → ℝ)
    (b : Module.Basis (Fin n) ℤ (Lattice n)) (I : Finset (Fin n))
    (x : Ambient (n - I.card)) (j : Fin (n - I.card)) :
    (dotProductEquiv ℝ (Fin n) (embed n (b (complementaryEmbedding I j))))
      (quotientFaceMap a b I x) = x j := by
  rw [normal_pairing_eq_dual_coordinate, quotientFaceMap_apply,
    map_add, Finsupp.add_apply, quotientFaceOrigin_coordinate]
  have hj : complementaryEmbedding I j ∉ I :=
    (mem_range_complementaryEmbedding_iff I _).mp ⟨j, rfl⟩
  rw [if_neg hj, zero_add]
  exact selectedBasisMap_coordinate (integralBasisReal (integralDualBasis b))
    (complementaryEmbedding I) x j

def normalHeight (δ : Ambient n) : Lattice n → ℝ :=
  fun u => (dotProductEquiv ℝ (Fin n) (embed n u)) δ

theorem normalHeight_basis (δ : Ambient n)
    (b : Module.Basis (Fin n) ℤ (Lattice n)) (i : Fin n) :
    normalHeight δ (b i) = (integralBasisReal (integralDualBasis b)).coord i δ :=
  normal_pairing_eq_dual_coordinate b i δ

theorem normalHeight_sum_image (δ : Ambient n)
    (b : Module.Basis (Fin n) ℤ (Lattice n)) (I : Finset (Fin n)) :
    (∑ u ∈ I.image b, normalHeight δ u) =
      ∑ i ∈ I, (integralBasisReal (integralDualBasis b)).coord i δ := by
  rw [Finset.sum_image]
  · exact Finset.sum_congr rfl (fun i hi => normalHeight_basis δ b i)
  · exact fun i _ j _ hij => b.injective hij

def tangentSliceCoordinates (a : Lattice n → ℝ)
    (b : Module.Basis (Fin n) ℤ (Lattice n)) (I : Finset (Fin n))
    (δ : Ambient n) : Ambient (n - I.card) :=
  fun j => -a (b (complementaryEmbedding I j)) + normalHeight δ (b (complementaryEmbedding I j))

/-- A displacement with its actual old normal heights has exactly these
affine tangent coordinates in the saturated face chart. -/
theorem quotientFaceMap_tangentSliceCoordinates
    (a : Lattice n → ℝ) (b : Module.Basis (Fin n) ℤ (Lattice n))
    (I : Finset (Fin n)) (v δ : Ambient n)
    (hv : ∀ i, (dotProductEquiv ℝ (Fin n) (embed n (b i))) v = -a (b i)) :
    quotientFaceMap (displacedSupport a (I.image b) (normalHeight δ)) b I
      (tangentSliceCoordinates a b I δ) = v + δ := by
  apply (integralBasisReal (integralDualBasis b)).ext_elem
  intro i
  rw [← normal_pairing_eq_dual_coordinate, ← normal_pairing_eq_dual_coordinate]
  by_cases hi : i ∈ I
  · rw [quotientFaceMap_active _ b I _ i hi, map_add, hv i]
    have hbi : b i ∈ I.image b := Finset.mem_image.mpr ⟨i, hi, rfl⟩
    simp only [displacedSupport, Pi.sub_apply, facetWeight, if_pos hbi, normalHeight]
    ring
  · obtain ⟨j, hj⟩ := (mem_range_complementaryEmbedding_iff I i).mpr hi
    rw [← hj, quotientFaceMap_complementary_coordinate, map_add, hv]
    rfl

/-- The shear changes no tangent coordinate, including its base shift. -/
theorem tangentSliceCoordinates_shifted_star_box
    (a : Lattice n → ℝ) (b : Module.Basis (Fin n) ℤ (Lattice n))
    (I : Finset (Fin n)) (j : Fin n) (hj : j ∈ I)
    (t : ℝ) («λ» : Fin n → ℝ) :
    tangentSliceCoordinates a b I
      (t • integralBasisReal (integralDualBasis b) j +
        ∑ k, «λ» k • starShearBasis (integralBasisReal (integralDualBasis b)) I j k) =
      fun k => -a (b (complementaryEmbedding I k)) + «λ» (complementaryEmbedding I k) := by
  funext k
  have hk : complementaryEmbedding I k ∉ I :=
    (mem_range_complementaryEmbedding_iff I _).mp ⟨k, rfl⟩
  have hkj : complementaryEmbedding I k ≠ j := fun hh => hk (hh.symm ▸ hj)
  simp only [tangentSliceCoordinates, normalHeight, normal_pairing_eq_dual_coordinate]
  rw [show (integralBasisReal (integralDualBasis b)).repr _ (complementaryEmbedding I k) =
      (integralBasisReal (integralDualBasis b)).coord (complementaryEmbedding I k) _ from rfl,
    coord_shifted_star_box, if_neg hkj, add_zero]

/-- Inner unit boxes start at old normal height at least one. The upper
normal budget is exactly `t+2`, with no rounding of real coordinates. -/
theorem shifted_inner_star_box_normal_heights
    (B : Module.Basis (Fin n) ℝ (Ambient n)) (I : Finset (Fin n))
    (j : Fin n) (hj : j ∈ I) (t : ℝ)
    (ht : 2 * (I.card - 1 : ℕ) ≤ t)
    («λ» : Fin n → ℝ) («hλ» : ∀ i, 0 ≤ «λ» i ∧ «λ» i ≤ 1) :
    let δ := t • B j + ∑ k, (1 + «λ» k) • starShearBasis B I j k
    (∀ i ∈ I, 1 ≤ B.coord i δ) ∧
      t + 1 ≤ ∑ i ∈ I, B.coord i δ ∧
      (∑ i ∈ I, B.coord i δ) ≤ t + 2 := by
  dsimp only
  have hsum : (∑ k ∈ I.erase j, (1 + «λ» k)) ≤ 2 * (I.card - 1 : ℕ) := by
    calc
      (∑ k ∈ I.erase j, (1 + «λ» k)) ≤ ∑ _k ∈ I.erase j, (2 : ℝ) :=
        Finset.sum_le_sum (fun k hk => by have hh := («hλ» k).2; linarith)
      _ = 2 * (I.card - 1 : ℕ) := by
        simp only [Finset.sum_const, nsmul_eq_mul, Finset.card_erase_of_mem hj]
        ring
  refine ⟨?_, ?_, ?_⟩
  · intro i hi
    rw [coord_shifted_star_box]
    by_cases hij : i = j
    · rw [if_pos hij]
      have hh := («hλ» i).1
      linarith
    · rw [if_neg hij, add_zero]
      exact le_add_of_nonneg_right («hλ» i).1
  · rw [sum_normal_coords_shifted_star_box B I j hj]
    have hh := («hλ» j).1
    linarith
  · rw [sum_normal_coords_shifted_star_box B I j hj]
    have hh := («hλ» j).2
    linarith

namespace SmoothCompleteFan

variable («Σ» : SmoothCompleteFan n)

theorem quotient_of_full_basis_standard_cone
    (b : Module.Basis (Fin n) ℤ (Lattice n)) (I : Finset (Fin n))
    (hfull : Finset.univ.image b ∈ «Σ».cones) :
    let hF := «Σ».downward _ hfull (I.image b) (Finset.image_subset_image (Finset.subset_univ I))
    Finset.univ.image (Pi.basisFun ℤ (Fin (n - I.card))) ∈
      («Σ».completeQuotientStarFan b I hF).cones := by
  dsimp only
  apply («Σ».mem_quotientStarCones b I _).mpr
  refine ⟨Finset.univ.image b, hfull,
    Finset.image_subset_image (Finset.subset_univ I), ?_⟩
  ext u
  constructor
  · intro hu
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hu
    refine Finset.mem_image.mpr ⟨b (complementaryEmbedding I j), ?_,
      coneQuotientLattice_complementary_basis b I j⟩
    apply Finset.mem_sdiff.mpr
    refine ⟨Finset.mem_image.mpr ⟨_, Finset.mem_univ _, rfl⟩, ?_⟩
    intro hh
    obtain ⟨k, hk, he⟩ := Finset.mem_image.mp hh
    have hkj := b.injective he
    exact ((mem_range_complementaryEmbedding_iff I _).mp ⟨j, rfl⟩) (hkj ▸ hk)
  · intro hu
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hu
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp (Finset.mem_sdiff.mp hv).1
    have hiI : i ∉ I := fun hh => (Finset.mem_sdiff.mp hv).2
      (Finset.mem_image.mpr ⟨i, hh, rfl⟩)
    obtain ⟨j, hj⟩ := (mem_range_complementaryEmbedding_iff I i).mpr hiI
    rw [← hj, coneQuotientLattice_complementary_basis]
    exact Finset.mem_image.mpr ⟨j, Finset.mem_univ j, rfl⟩

theorem faceSupport_displaced_standard_coordinate
    (b : Module.Basis (Fin n) ℤ (Lattice n)) (I : Finset (Fin n))
    (hfull : Finset.univ.image b ∈ «Σ».cones) (hF : I.image b ∈ «Σ».cones)
    (a : Lattice n → ℝ) (h : Lattice n → ℝ) (j : Fin (n - I.card)) :
    «Σ».faceSupport b I hF (displacedSupport a (I.image b) h)
      (Pi.basisFun ℤ (Fin (n - I.card)) j) = a (b (complementaryEmbedding I j)) := by
  have hj : complementaryEmbedding I j ∉ I :=
    (mem_range_complementaryEmbedding_iff I _).mp ⟨j, rfl⟩
  have hvN : b (complementaryEmbedding I j) ∉ I.image b := by
    intro hh
    obtain ⟨k, hk, he⟩ := Finset.mem_image.mp hh
    exact hj (b.injective he ▸ hk)
  have hv : b (complementaryEmbedding I j) ∈ (Finset.univ.image b) \ I.image b :=
    Finset.mem_sdiff.mpr ⟨Finset.mem_image.mpr ⟨_, Finset.mem_univ _, rfl⟩, hvN⟩
  rw [← coneQuotientLattice_complementary_basis b I j,
    «Σ».faceSupport_projected b I hF _ hfull
      (Finset.image_subset_image (Finset.subset_univ I)) hv,
    normal_pairing_eq_dual_coordinate, quotientFaceOrigin_coordinate, if_neg hj, add_zero]
  simp only [displacedSupport, Pi.sub_apply, facetWeight, if_neg hvN, sub_zero]

/-- A corner-box criterion in explicitly chosen primitive normal
coordinates, without any dependence on a chosen enumeration of the full
cone by `fullConeBasis`. -/
theorem corner_box_at_normal_basis
    (hpure : «Σ».IsPure) (H : Lattice n → ℤ)
    (hH : «Σ».IsStrictSupport (fun u => (H u : ℝ)))
    (a : Lattice n → ℝ) (side : ℝ) (hside : 0 ≤ side)
    (hdegree : ∀ Q : «Σ».PrimitiveRelation, Q.IsCombinatoriallyContractible →
      side * Q.fiberDimension ≤ Q.degree a)
    (b : Module.Basis (Fin n) ℤ (Lattice n)) (hb : Finset.univ.image b ∈ «Σ».cones)
    (v : Ambient n) (hv : ∀ i,
      (dotProductEquiv ℝ (Fin n) (embed n (b i))) v = -a (b i))
    (t : Fin n → ℝ) (ht : ∀ i, 0 ≤ t i ∧ t i ≤ side) :
    v + ∑ i, t i • integralBasisReal (integralDualBasis b) i ∈ «Σ».fanPolytope a := by
  apply «Σ».box_mem_fanPolytope_of_vertices a v _ side hside ?_ t ht
  intro I
  let F := a - side • (fun u => if u ∈ I.image b then 1 else 0)
  have hF : «Σ».IsNef F := «Σ».nef_sub_cone_selection_of_contractible_degrees hpure H hH
    a side hside hdegree hb (Finset.image_subset_image (Finset.subset_univ I))
  apply «Σ».box_corner_mem_of_refinement_nef «Σ» (Finset.Subset.refl _) a F hF b hb v hv I side
  · intro i
    simp only [F, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Finset.mem_image, b.injective.eq_iff]
    simp
  · intro u hu
    change a u - side * (if u ∈ I.image b then 1 else 0) ≤ a u
    split_ifs <;> nlinarith

theorem coordinate_box_mem_fanPolytope
    (hpure : «Σ».IsPure) (H : Lattice n → ℤ)
    (hH : «Σ».IsStrictSupport (fun u => (H u : ℝ)))
    (a : Lattice n → ℝ) (side : ℝ) (hside : 0 ≤ side)
    (hdegree : ∀ Q : «Σ».PrimitiveRelation, Q.IsCombinatoriallyContractible →
      side * Q.fiberDimension ≤ Q.degree a)
    (hstandard : Finset.univ.image (Pi.basisFun ℤ (Fin n)) ∈ «Σ».cones)
    (t : Fin n → ℝ) (ht : ∀ i, 0 ≤ t i ∧ t i ≤ side) :
    (fun i => -a (Pi.basisFun ℤ (Fin n) i) + t i) ∈ «Σ».fanPolytope a := by
  have hh := «Σ».corner_box_at_normal_basis hpure H hH a side hside hdegree
    (Pi.basisFun ℤ (Fin n)) hstandard
    (fun i => -a (Pi.basisFun ℤ (Fin n) i)) (by intro i; rw [standard_normal_pairing]) t ht
  rw [integralDualBasis_standard] at hh
  simp only [integralBasisReal_standard_apply] at hh
  have he : (∑ i, t i • Pi.basisFun ℝ (Fin n) i) = t := by
    funext k
    simp [Pi.basisFun_apply, Pi.single_apply]
  rw [he] at hh
  exact hh

end SmoothCompleteFan

end PaperVerification.ToricGeometry
end
end Source_ToricSliceBoxCoordinates
-- END ORIGINAL PaperVerification.ToricSliceBoxCoordinates


-- BEGIN ORIGINAL PaperVerification.ToricFocusSliceBoxes
section Source_ToricFocusSliceBoxes

-- original header: module

-- original header: public import PaperVerification.ToricFocusHeightDegrees
-- original header: public import PaperVerification.ToricSliceBoxCoordinates
-- original header: public import PaperVerification.ToricCanonicalSlices

-- original header: @[expose] public section

/-!
# Whole tangent boxes in actual normal-height slices

The quotient-star relation is constructed from the original focus. Its
nonfiber primitive collections have the proved base-dimensional bound.
The actual displaced edge reserve and the scalar fiber degree therefore
supply every point of the ordinary or canonical tangent box.
-/

noncomputable section

namespace PaperVerification.ToricGeometry

open Set
open scoped BigOperators Classical

namespace SmoothCompleteFan.PrimitiveRelation

variable {n : ℕ} {«Σ» : SmoothCompleteFan n} (R : «Σ».PrimitiveRelation)

theorem focus_bundle_base_dimension (hR : R.IsCombinatoriallyContractible)
    (b : Module.Basis (Fin n) ℤ (Lattice n)) (I : Finset (Fin n))
    (hI : I.image b = R.negative)
    (c : (R.focusQuotientRelation hR b I hI).BundleCoordinates) :
    (n - I.card) - c.fiberIndices.card = n - R.fiberDimension - R.negative.card := by
  rw [c.fiberIndices_card, R.focusQuotientRelation_fiberDimension hR b I hI]
  have hcard : I.card = R.negative.card := by
    rw [← hI, Finset.card_image_of_injective _ b.injective]
  omega

end SmoothCompleteFan.PrimitiveRelation

namespace SmoothCompleteFan

variable {n : ℕ} («Σ» : SmoothCompleteFan n)

theorem focus_slice_box_mem
    (hpure : «Σ».IsPure) (a : Lattice n → ℤ)
    (ha : «Σ».IsStrictSupport (fun u => (a u : ℝ)))
    {e : ℕ} (he : 0 < e)
    (hedges : («Σ».supportLatticePolytope hpure a ha).EdgesAtLeast e)
    (R : «Σ».PrimitiveRelation) (hR : R.IsCombinatoriallyContractible)
    (b : Module.Basis (Fin n) ℤ (Lattice n)) (I : Finset (Fin n))
    (hI : I.image b = R.negative) (hfull : Finset.univ.image b ∈ «Σ».cones)
    (v δ : Ambient n)
    (hv : ∀ i, (dotProductEquiv ℝ (Fin n) (embed n (b i))) v = -(a (b i) : ℝ))
    (side : ℝ) (hside : 0 ≤ side)
    (hh : ∀ u ∈ R.negative, 0 ≤ normalHeight δ u)
    (htangent : ∀ j : Fin (n - I.card),
      0 ≤ normalHeight δ (b (complementaryEmbedding I j)) ∧
        normalHeight δ (b (complementaryEmbedding I j)) ≤ side)
    (hbudget : (∑ u ∈ R.negative, normalHeight δ u) +
      side * ((n - R.fiberDimension - R.negative.card : ℕ) : ℝ) ≤ e)
    (hfiber : side * R.fiberDimension ≤
      R.degree (displacedSupport (fun u => (a u : ℝ)) R.negative (normalHeight δ))) :
    v + δ ∈ «Σ».fanPolytope (fun u => (a u : ℝ)) := by
  let hF : I.image b ∈ «Σ».cones := hI.symm ▸ R.negative_cone
  let Ψ := «Σ».completeQuotientStarFan b I hF
  let D := displacedSupport (fun u => (a u : ℝ)) (I.image b) (normalHeight δ)
  let C := «Σ».faceSupport b I hF D
  let R' := R.focusQuotientRelation hR b I hI
  let c := R'.bundleCoordinates
  have hR' : R'.IsCombinatoriallyContractible := R.focusQuotientRelation_contractible hR b I hI
  have hN' : R'.negative = ∅ := rfl
  have hr' : R'.fiberDimension = R.fiberDimension := R.focusQuotientRelation_fiberDimension hR b I hI
  have hb : (n - I.card) - c.fiberIndices.card = n - R.fiberDimension - R.negative.card :=
    R.focus_bundle_base_dimension hR b I hI c
  have hhI : ∀ u ∈ I.image b, 0 ≤ normalHeight δ u := fun u hu => hh u (hI ▸ hu)
  have hsumBudget : (∑ u ∈ I.image b, normalHeight δ u) ≤ (e : ℝ) := by
    have hn : (0 : ℝ) ≤ (n - R.fiberDimension - R.negative.card : ℕ) := Nat.cast_nonneg _
    rw [hI]
    nlinarith [mul_nonneg hside hn]
  have hD : «Σ».IsNef D := «Σ».displacedSupport_isNef_of_edges hpure a ha hedges
    (I.image b) (normalHeight δ) hhI hsumBudget
  have hΨpure : Ψ.IsPure := «Σ».completeQuotientStarFan_isPure hpure b I hF
  let H := «Σ».faceSupportLattice b I hF a
  have hH : Ψ.IsStrictSupport (fun u => (H u : ℝ)) := by
    rw [show (fun u => (H u : ℝ)) = «Σ».faceSupport b I hF (fun u => (a u : ℝ)) from
      «Σ».faceSupportLattice_cast b I hF a]
    exact «Σ».faceSupport_isStrictSupport b I hF _ ha
  have hfiber' : side * R'.fiberDimension ≤ R'.degree C := by
    rw [hr', R.focusQuotientRelation_degree hR b I hI]
    simpa only [D, hI] using hfiber
  have hbase (Q : Ψ.PrimitiveRelation) (hQ : Q.IsCombinatoriallyContractible)
      (hQne : Q.positive ≠ R'.positive) :
      side * (((n - I.card) - c.fiberIndices.card : ℕ) : ℝ) ≤ Q.degree C := by
    rw [hb]
    have hlower := «Σ».displaced_faceSupport_degree_lower_bound b I hF hpure
      a ha he hedges (normalHeight δ) hhI hsumBudget Q hQ
    change (e : ℝ) - (∑ u ∈ I.image b, normalHeight δ u) ≤ Q.degree C at hlower
    rw [hI] at hlower
    linarith
  have hdegrees := c.all_contractible_degrees_of_fiber_and_base hR' hN' C side hside hfiber' hbase
  have hstandard : Finset.univ.image (Pi.basisFun ℤ (Fin (n - I.card))) ∈ Ψ.cones :=
    «Σ».quotient_of_full_basis_standard_cone b I hfull
  have hcoords := Ψ.coordinate_box_mem_fanPolytope hΨpure H hH C side hside hdegrees hstandard
    (fun j => normalHeight δ (b (complementaryEmbedding I j))) htangent
  have hpoint : (fun j => -C (Pi.basisFun ℤ (Fin (n - I.card)) j) +
      normalHeight δ (b (complementaryEmbedding I j))) = tangentSliceCoordinates (fun u => (a u : ℝ)) b I δ := by
    funext j
    rw [show C (Pi.basisFun ℤ (Fin (n - I.card)) j) = a (b (complementaryEmbedding I j)) from
      «Σ».faceSupport_displaced_standard_coordinate b I hfull hF _ _ j]
    rfl
  rw [hpoint] at hcoords
  have hface : quotientFaceMap D b I (tangentSliceCoordinates (fun u => (a u : ℝ)) b I δ) ∈
      «Σ».supportFace D (I.image b) := by
    rw [← «Σ».quotientFaceMap_image_fanPolytope b I hF hpure D hD]
    exact ⟨_, hcoords, rfl⟩
  rw [quotientFaceMap_tangentSliceCoordinates _ b I v δ hv] at hface
  rw [«Σ».displaced_supportFace_eq_slice _ _ _ hhI] at hface
  exact hface.1

theorem focus_inner_slice_box_mem
    (hpure : «Σ».IsPure) (a : Lattice n → ℤ)
    (ha : «Σ».IsStrictSupport (fun u => (a u : ℝ)))
    {e : ℕ} (he : 0 < e)
    (hedges : («Σ».supportLatticePolytope hpure a ha).EdgesAtLeast e)
    (R : «Σ».PrimitiveRelation) (hR : R.IsCombinatoriallyContractible)
    (b : Module.Basis (Fin n) ℤ (Lattice n)) (I : Finset (Fin n))
    (hI : I.image b = R.negative) (hfull : Finset.univ.image b ∈ «Σ».cones)
    (v δ : Ambient n)
    (hv : ∀ i, (dotProductEquiv ℝ (Fin n) (embed n (b i))) v = -(a (b i) : ℝ))
    (hh : ∀ u ∈ R.negative, 1 ≤ normalHeight δ u)
    (htangent : ∀ j : Fin (n - I.card),
      1 ≤ normalHeight δ (b (complementaryEmbedding I j)) ∧
        normalHeight δ (b (complementaryEmbedding I j)) ≤ 2)
    (hbudget : (∑ u ∈ R.negative, normalHeight δ u) +
      (2 * (n - R.fiberDimension - R.negative.card : ℕ) + 1 : ℕ) ≤ e)
    (hfiber : (2 * R.fiberDimension + 1 : ℕ) ≤
      R.degree (displacedSupport (fun u => (a u : ℝ)) R.negative (normalHeight δ))) :
    v + δ ∈ interior («Σ».fanPolytope (fun u => (a u : ℝ))) := by
  let hF : I.image b ∈ «Σ».cones := hI.symm ▸ R.negative_cone
  let Ψ := «Σ».completeQuotientStarFan b I hF
  let D := displacedSupport (fun u => (a u : ℝ)) (I.image b) (normalHeight δ)
  let C := «Σ».faceSupport b I hF D
  let R' := R.focusQuotientRelation hR b I hI
  let c := R'.bundleCoordinates
  have hR' : R'.IsCombinatoriallyContractible := R.focusQuotientRelation_contractible hR b I hI
  have hN' : R'.negative = ∅ := rfl
  have hr' : R'.fiberDimension = R.fiberDimension := R.focusQuotientRelation_fiberDimension hR b I hI
  have hb : (n - I.card) - c.fiberIndices.card = n - R.fiberDimension - R.negative.card :=
    R.focus_bundle_base_dimension hR b I hI c
  have hhI : ∀ u ∈ I.image b, 1 ≤ normalHeight δ u := fun u hu => hh u (hI ▸ hu)
  have hhI0 : ∀ u ∈ I.image b, 0 ≤ normalHeight δ u := fun u hu => zero_le_one.trans (hhI u hu)
  have hsumBudget : (∑ u ∈ I.image b, normalHeight δ u) + 1 ≤ (e : ℝ) := by
    have hn : (0 : ℝ) ≤ (n - R.fiberDimension - R.negative.card : ℕ) := Nat.cast_nonneg _
    rw [hI]
    norm_num only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one] at hbudget
    linarith
  have hΨpure : Ψ.IsPure := «Σ».completeQuotientStarFan_isPure hpure b I hF
  let H := «Σ».faceSupportLattice b I hF a
  have hH : Ψ.IsStrictSupport (fun u => (H u : ℝ)) := by
    rw [show (fun u => (H u : ℝ)) = «Σ».faceSupport b I hF (fun u => (a u : ℝ)) from
      «Σ».faceSupportLattice_cast b I hF a]
    exact «Σ».faceSupport_isStrictSupport b I hF _ ha
  have hfiber' : (2 * R'.fiberDimension + 1 : ℕ) ≤ R'.degree C := by
    rw [hr', R.focusQuotientRelation_degree hR b I hI]
    simpa only [D, hI] using hfiber
  have hbase (Q : Ψ.PrimitiveRelation) (hQ : Q.IsCombinatoriallyContractible)
      (hQne : Q.positive ≠ R'.positive) :
      (2 * ((n - I.card) - c.fiberIndices.card) + 1 : ℕ) ≤ Q.degree C := by
    rw [hb]
    have hlower := «Σ».displaced_faceSupport_degree_lower_bound b I hF hpure
      a ha he hedges (normalHeight δ) hhI0 (by linarith) Q hQ
    change (e : ℝ) - (∑ u ∈ I.image b, normalHeight δ u) ≤ Q.degree C at hlower
    rw [hI] at hlower
    linarith
  have hdegrees (Q : Ψ.PrimitiveRelation) (hQ : Q.IsCombinatoriallyContractible) :
      1 * (Q.fiberDimension : ℝ) ≤ Q.degree (fun u => C u - 1) := by
    simpa only [one_mul] using
      c.all_adjoint_contractible_degrees_of_fiber_and_base hR' hN' C hfiber' hbase Q hQ
  have hstandard : Finset.univ.image (Pi.basisFun ℤ (Fin (n - I.card))) ∈ Ψ.cones :=
    «Σ».quotient_of_full_basis_standard_cone b I hfull
  have hcoords := Ψ.coordinate_box_mem_fanPolytope hΨpure H hH (fun u => C u - 1)
    1 zero_le_one hdegrees hstandard
    (fun j => normalHeight δ (b (complementaryEmbedding I j)) - 1)
    (fun j => by obtain ⟨hlo, hhi⟩ := htangent j; constructor <;> linarith)
  have hpoint : (fun j => -(C (Pi.basisFun ℤ (Fin (n - I.card)) j) - 1) +
      (normalHeight δ (b (complementaryEmbedding I j)) - 1)) =
      tangentSliceCoordinates (fun u => (a u : ℝ)) b I δ := by
    funext j
    rw [show C (Pi.basisFun ℤ (Fin (n - I.card)) j) = a (b (complementaryEmbedding I j)) from
      «Σ».faceSupport_displaced_standard_coordinate b I hfull hF _ _ j]
    dsimp only [tangentSliceCoordinates]
    ring
  rw [hpoint] at hcoords
  have hcanonical := «Σ».canonical_slice_eq_of_edges b I hF hpure a ha hedges
    (normalHeight δ) hhI hsumBudget
  have hslice : quotientFaceMap D b I (tangentSliceCoordinates (fun u => (a u : ℝ)) b I δ) ∈
      {x ∈ «Σ».fanPolytope (fun u => (a u : ℝ) - 1) | ∀ u ∈ I.image b,
        (dotProductEquiv ℝ (Fin n) (embed n u)) x + (a u : ℝ) = normalHeight δ u} := by
    rw [← hcanonical]
    exact ⟨_, hcoords, rfl⟩
  rw [quotientFaceMap_tangentSliceCoordinates _ b I v δ hv] at hslice
  exact «Σ».fanPolytope_sub_pos_subset_interior _ 1 zero_lt_one hslice.1

end SmoothCompleteFan

end PaperVerification.ToricGeometry
end
end Source_ToricFocusSliceBoxes
-- END ORIGINAL PaperVerification.ToricFocusSliceBoxes


-- BEGIN ORIGINAL PaperVerification.ToricShiftedBoxes
section Source_ToricShiftedBoxes

-- original header: module

-- original header: public import PaperVerification.ToricFocusSliceBoxes

-- original header: @[expose] public section

/-!
# Full shifted boxes in the original polytope and its interior

The normal heights are computed from the actual integral shear. Their
budgets and the genuine primitive fiber coefficients put each arbitrary
real box point in the exact quotient slice. The base-dimension zero nef
endpoint is included throughout.
-/

noncomputable section

namespace PaperVerification.ToricGeometry

open Set
open scoped BigOperators Classical

namespace SmoothCompleteFan

variable {n : ℕ} («Σ» : SmoothCompleteFan n)

theorem shifted_box_mem
    (hpure : «Σ».IsPure) (a : Lattice n → ℤ)
    (ha : «Σ».IsStrictSupport (fun u => (a u : ℝ)))
    {e : ℕ} (he : 0 < e)
    (hedges : («Σ».supportLatticePolytope hpure a ha).EdgesAtLeast e)
    (R : «Σ».PrimitiveRelation) (hR : R.IsCombinatoriallyContractible)
    (hne : R.negative.Nonempty)
    (b : Module.Basis (Fin n) ℤ (Lattice n)) (I : Finset (Fin n))
    (hI : I.image b = R.negative) (hfull : Finset.univ.image b ∈ «Σ».cones)
    (j : Fin n) (hj : j ∈ I) (v : Ambient n)
    (hv : ∀ i, (dotProductEquiv ℝ (Fin n) (embed n (b i))) v = -(a (b i) : ℝ))
    (side t : ℝ) (hside : 0 ≤ side)
    (ht : side * (R.negative.card - 1 : ℕ) ≤ t)
    (hbudget : t + side + side * ((n - R.fiberDimension - R.negative.card : ℕ) : ℝ) ≤ e)
    (hfiber : side * R.fiberDimension ≤ R.degree (fun u => (a u : ℝ)) +
      (R.minimumCoefficient hne : ℝ) * t)
    («λ» : Fin n → ℝ) («hλ» : ∀ i, 0 ≤ «λ» i ∧ «λ» i ≤ side) :
    v + (t • integralBasisReal (integralDualBasis b) j +
      ∑ k, «λ» k • starShearBasis (integralBasisReal (integralDualBasis b)) I j k) ∈
      «Σ».fanPolytope (fun u => (a u : ℝ)) := by
  let B := integralBasisReal (integralDualBasis b)
  let δ := t • B j + ∑ k, «λ» k • starShearBasis B I j k
  have hcard : I.card = R.negative.card := by
    rw [← hI, Finset.card_image_of_injective _ b.injective]
  have hheight := shifted_star_box_normal_heights B I j hj side t hside
    (by simpa only [hcard] using ht) «λ» «hλ»
  have hsum : (∑ u ∈ R.negative, normalHeight δ u) = ∑ i ∈ I, B.coord i δ := by
    rw [← hI]
    exact normalHeight_sum_image δ b I
  have hh (u : Lattice n) (hu : u ∈ R.negative) : 0 ≤ normalHeight δ u := by
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp (hI.symm ▸ hu)
    rw [normalHeight_basis]
    exact hheight.1 i hi
  have htotalLo : t ≤ ∑ u ∈ R.negative, normalHeight δ u := by
    rw [hsum]
    exact hheight.2.1
  have htotalHi : (∑ u ∈ R.negative, normalHeight δ u) ≤ t + side := by
    rw [hsum]
    exact hheight.2.2
  apply «Σ».focus_slice_box_mem hpure a ha he hedges R hR b I hI hfull v δ hv side hside hh
  · intro k
    have hk : complementaryEmbedding I k ∉ I :=
      (mem_range_complementaryEmbedding_iff I _).mp ⟨k, rfl⟩
    have hkj : complementaryEmbedding I k ≠ j := fun h => hk (h.symm ▸ hj)
    rw [normalHeight_basis, show B.coord (complementaryEmbedding I k) δ =
        B.coord (complementaryEmbedding I k)
          (t • B j + ∑ l, «λ» l • starShearBasis B I j l) from rfl,
      coord_shifted_star_box, if_neg hkj, add_zero]
    exact «hλ» _
  · linarith
  · have hlower := R.degree_displaced_focus_lower hne (fun u => (a u : ℝ))
      0 (normalHeight δ) hh
    simp only [zero_mul, add_zero, sub_zero] at hlower
    have hm : (0 : ℝ) ≤ R.minimumCoefficient hne := Nat.cast_nonneg _
    have hmul := mul_le_mul_of_nonneg_left htotalLo hm
    linarith

theorem shifted_inner_unit_box_mem
    (hpure : «Σ».IsPure) (a : Lattice n → ℤ)
    (ha : «Σ».IsStrictSupport (fun u => (a u : ℝ)))
    {e : ℕ} (he : 0 < e)
    (hedges : («Σ».supportLatticePolytope hpure a ha).EdgesAtLeast e)
    (R : «Σ».PrimitiveRelation) (hR : R.IsCombinatoriallyContractible)
    (hne : R.negative.Nonempty)
    (b : Module.Basis (Fin n) ℤ (Lattice n)) (I : Finset (Fin n))
    (hI : I.image b = R.negative) (hfull : Finset.univ.image b ∈ «Σ».cones)
    (j : Fin n) (hj : j ∈ I) (v : Ambient n)
    (hv : ∀ i, (dotProductEquiv ℝ (Fin n) (embed n (b i))) v = -(a (b i) : ℝ))
    (t : ℝ) (ht : 2 * (R.negative.card - 1 : ℕ) ≤ t)
    (hbudget : t + 2 + (2 * (n - R.fiberDimension - R.negative.card : ℕ) + 1 : ℕ) ≤ e)
    (hfiber : (2 * R.fiberDimension + 1 : ℕ) ≤
      R.degree (fun u => (a u : ℝ)) + R.negativeCoefficientSum +
        (R.minimumCoefficient hne : ℝ) * (t + 1 - R.negative.card))
    («λ» : Fin n → ℝ) («hλ» : ∀ i, 0 ≤ «λ» i ∧ «λ» i ≤ 1) :
    v + (t • integralBasisReal (integralDualBasis b) j +
      ∑ k, (1 + «λ» k) • starShearBasis (integralBasisReal (integralDualBasis b)) I j k) ∈
      interior («Σ».fanPolytope (fun u => (a u : ℝ))) := by
  let B := integralBasisReal (integralDualBasis b)
  let δ := t • B j + ∑ k, (1 + «λ» k) • starShearBasis B I j k
  have hcard : I.card = R.negative.card := by
    rw [← hI, Finset.card_image_of_injective _ b.injective]
  have hheight := shifted_inner_star_box_normal_heights B I j hj t
    (by simpa only [hcard] using ht) «λ» «hλ»
  have hsum : (∑ u ∈ R.negative, normalHeight δ u) = ∑ i ∈ I, B.coord i δ := by
    rw [← hI]
    exact normalHeight_sum_image δ b I
  have hh (u : Lattice n) (hu : u ∈ R.negative) : 1 ≤ normalHeight δ u := by
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp (hI.symm ▸ hu)
    rw [normalHeight_basis]
    exact hheight.1 i hi
  have htotalLo : t + 1 ≤ ∑ u ∈ R.negative, normalHeight δ u := by
    rw [hsum]
    exact hheight.2.1
  have htotalHi : (∑ u ∈ R.negative, normalHeight δ u) ≤ t + 2 := by
    rw [hsum]
    exact hheight.2.2
  apply «Σ».focus_inner_slice_box_mem hpure a ha he hedges R hR b I hI hfull v δ hv hh
  · intro k
    have hk : complementaryEmbedding I k ∉ I :=
      (mem_range_complementaryEmbedding_iff I _).mp ⟨k, rfl⟩
    have hkj : complementaryEmbedding I k ≠ j := fun h => hk (h.symm ▸ hj)
    rw [normalHeight_basis, show B.coord (complementaryEmbedding I k) δ =
        B.coord (complementaryEmbedding I k)
          (t • B j + ∑ l, (1 + «λ» l) • starShearBasis B I j l) from rfl,
      coord_shifted_star_box, if_neg hkj, add_zero]
    obtain ⟨hlo, hhi⟩ := «hλ» (complementaryEmbedding I k)
    constructor <;> linarith
  · linarith
  · have hlower := R.degree_displaced_focus_lower hne (fun u => (a u : ℝ))
      1 (normalHeight δ) hh
    simp only [one_mul] at hlower
    have hm : (0 : ℝ) ≤ R.minimumCoefficient hne := Nat.cast_nonneg _
    have hmul := mul_le_mul_of_nonneg_left
      (sub_le_sub_right htotalLo (R.negative.card : ℝ)) hm
    linarith

end SmoothCompleteFan

end PaperVerification.ToricGeometry
end
end Source_ToricShiftedBoxes
-- END ORIGINAL PaperVerification.ToricShiftedBoxes


-- BEGIN ORIGINAL PaperVerification.ToricSelectedBoxAssembly
section Source_ToricSelectedBoxAssembly

-- original header: module

-- original header: public import PaperVerification.ToricCartierBoxCoordinates
-- original header: public import PaperVerification.ToricOutsideBoxes
-- original header: public import PaperVerification.ToricShiftedBoxes

-- original header: @[expose] public section

/-!
# Exhaustive assembly of the actual selected-fan boxes

The local statements are applied after the full-cone classification.
The resulting box is expressed in the chosen Cartier basis of each full
cone; no preferred basis ordering remains in the conclusion.
-/

noncomputable section

namespace PaperVerification.ToricGeometry

open scoped BigOperators Classical

namespace LatticePolytope

variable {n : ℕ} (P : LatticePolytope n)

theorem exists_normal_basis_point («Σ» : SmoothCompleteFan n)
    (hfan : «Σ».realCones = P.normalFan)
    (b : Module.Basis (Fin n) ℤ (Lattice n))
    (hfull : Finset.univ.image b ∈ «Σ».cones) :
    ∃ v ∈ P.carrier, P.normalCone v =
      (latticeRayCone (Finset.univ.image b) : Set (Ambient n)) := by
  have hmem : (latticeRayCone (Finset.univ.image b) : Set (Ambient n)) ∈
      «Σ».realCones := ⟨Finset.univ.image b, hfull, rfl⟩
  rw [hfan] at hmem
  obtain ⟨v, hv, heq⟩ := hmem
  exact ⟨v, hv, heq.symm⟩

end LatticePolytope

namespace SmoothCompleteFan

variable {n : ℕ} («Σ» : SmoothCompleteFan n)
variable {ι : Type*} [Fintype ι] (R : ι → «Σ».PrimitiveRelation)
variable (hne : ∀ i, (R i).negative.Nonempty)
variable (hdisj : «Σ».PairwiseDisjointFoci (fun i => (R i).negative))

/-- Local ordinary and star-chart containments imply the exact full
centered box for every actual selected full cone and its chosen basis. -/
theorem selected_centered_box_of_charts
    (P : LatticePolytope n) (hfan : «Σ».realCones = P.normalFan)
    (c radius : ℝ) (u : ι → ℝ) (A : Set (Ambient n))
    (houtside : ∀ (b : Module.Basis (Fin n) ℤ (Lattice n)),
      Finset.univ.image b ∈ «Σ».cones →
      (∀ i, ¬ (R i).negative ⊆ Finset.univ.image b) →
      ∀ (v : Ambient n), v ∈ P.carrier →
      P.normalCone v = (latticeRayCone (Finset.univ.image b) : Set (Ambient n)) →
      ∀ t : Fin n → ℝ, (∀ k, |t k| ≤ radius) →
        v + ∑ k, (c + t k) • integralBasisReal (integralDualBasis b) k ∈ A)
    (hstar : ∀ (i : ι) (b : Module.Basis (Fin n) ℤ (Lattice n))
      (I : Finset (Fin n)), Finset.univ.image b ∈ «Σ».cones →
      I.image b = (R i).negative → ∀ j ∈ I,
      ∀ (v : Ambient n), v ∈ P.carrier →
      P.normalCone v = (latticeRayCone (Finset.univ.image b) : Set (Ambient n)) →
      ∀ t : Fin n → ℝ, (∀ k, |t k| ≤ radius) →
        v + u i • integralBasisReal (integralDualBasis b) j +
          ∑ k, (c + t k) •
            starShearBasis (integralBasisReal (integralDualBasis b)) I j k ∈ A)
    (s : («Σ».selectedFan R hne hdisj).fullCones)
    (t : Fin n → ℝ) (ht : ∀ k, |t k| ≤ radius) :
    («Σ».selectedFan R hne hdisj).cartierPoint
        («Σ».selectedCenteredSupport R (fun v => (P.integralSupport v : ℝ)) c u) s +
      ∑ k, t k • («Σ».selectedFan R hne hdisj).cartierBasis s k ∈ A := by
  let Γ := «Σ».selectedFan R hne hdisj
  rcases «Σ».selected_full_cone_chart R hne hdisj s with ⟨hs, hnone⟩ |
    ⟨i, b, I, j, hfull, hI, hj, hset⟩
  · let b := Γ.fullConeBasis s
    have hset : (s : Finset (Lattice n)) = Finset.univ.image b := Γ.fullConeBasis_ray_set s
    have hfull : Finset.univ.image b ∈ «Σ».cones := hset ▸ hs
    have hn : ∀ i, ¬ (R i).negative ⊆ Finset.univ.image b := hset ▸ hnone
    obtain ⟨v, hv, hcone⟩ := P.exists_normal_basis_point «Σ» hfan b hfull
    apply Γ.centered_box_in_cartierBasis _ s b hset A radius ?_ t ht
    intro «λ» «hλ»
    rw [«Σ».selected_center_outside_chart R hne hdisj
      (fun v => (P.integralSupport v : ℝ)) c u s hs hnone b hset v
      (P.normal_basis_vertex_active «Σ» v hv b hcone)]
    simpa only [add_smul, Finset.sum_add_distrib, add_assoc] using
      houtside b hfull hn v hv hcone «λ» «hλ»
  · obtain ⟨v, hv, hcone⟩ := P.exists_normal_basis_point «Σ» hfan b hfull
    apply Γ.centered_box_in_cartierBasis _ s (starRayBasis b I j) hset A radius ?_ t ht
    intro «λ» «hλ»
    rw [«Σ».selected_center_star_chart R hne hdisj
      (fun v => (P.integralSupport v : ℝ)) c u s i b I hfull hI j hj hset v
      (P.normal_basis_vertex_active «Σ» v hv b hcone),
      integralBasisReal_dual_starRayBasis b I j hj]
    simpa only [add_smul, Finset.sum_add_distrib, add_assoc] using
      hstar i b I hfull hI j hj v hv hcone «λ» «hλ»

end SmoothCompleteFan

end PaperVerification.ToricGeometry
end
end Source_ToricSelectedBoxAssembly
-- END ORIGINAL PaperVerification.ToricSelectedBoxAssembly


-- BEGIN ORIGINAL PaperVerification.ToricCanonicalBoxes
section Source_ToricCanonicalBoxes

-- original header: module

-- original header: public import PaperVerification.ToricSelectedBoxAssembly
-- original header: public import PaperVerification.ToricMixedPolytopeBridges

-- original header: @[expose] public section

/-!
# The complete boxes at the canonical centers

Every full cone uses its actual chosen Cartier basis. The two parity
boxes have radius one. The two adjoint boxes have radius one half, with
the second box contained in the actual topological interior. The only
hypotheses are the original polytopes, their literal edge bounds and the
nonempty-focus branch of the exhaustive obstruction selection.
-/

noncomputable section

namespace PaperVerification.ToricGeometry

open Set
open scoped BigOperators Classical

namespace SmoothCompleteFan

variable {n : ℕ} («Σ» : SmoothCompleteFan n)

theorem canonical_parity_boxes (hpure : «Σ».IsPure)
    (P Q : LatticePolytope n) (hP : P.Smooth) (hQ : Q.Smooth)
    (hfanP : «Σ».realCones = P.normalFan) (hfanQ : «Σ».realCones = Q.normalFan)
    (hboundP : P.EdgesAtLeast n) (hboundQ : Q.EdgesAtLeast n)
    (hne : ∀ i, («Σ».parityFamily P Q i).negative.Nonempty) :
    let Γ := «Σ».selectedFan («Σ».parityFamily P Q) hne
      («Σ».parityFamily_disjoint hpure P Q hP hQ hfanP hfanQ hboundP hboundQ)
    (∀ (s : Γ.fullCones) (t : Fin n → ℝ), (∀ i, |t i| ≤ 1) →
      Γ.cartierPoint («Σ».parityCenter P Q P hne) s +
        ∑ i, t i • Γ.cartierBasis s i ∈ P.carrier) ∧
    (∀ (s : Γ.fullCones) (t : Fin n → ℝ), (∀ i, |t i| ≤ 1) →
      Γ.cartierPoint («Σ».parityCenter P Q Q hne) s +
        ∑ i, t i • Γ.cartierBasis s i ∈ Q.carrier) := by
  let R := «Σ».parityFamily P Q
  have hR : ∀ i, (R i).IsCombinatoriallyContractible :=
    «Σ».parityFamily_contractible P Q
  have hlarge : ∀ i, n < 2 * (R i).fiberDimension :=
    «Σ».parityFamily_large hpure P Q hP hQ hfanP hfanQ hboundP hboundQ
  let hdisj := «Σ».parityFamily_disjoint hpure P Q hP hQ hfanP hfanQ hboundP hboundQ
  have make_box (L : LatticePolytope n) (hL : L.Smooth)
      (hfanL : «Σ».realCones = L.normalFan) (hboundL : L.EdgesAtLeast n)
      (hinactive : ∀ S : «Σ».PrimitiveRelation, S.IsCombinatoriallyContractible →
        (∀ i, S.positive ≠ (R i).positive) →
        2 * (S.fiberDimension : ℝ) ≤ S.degree (fun u => (L.integralSupport u : ℝ)))
      (s : («Σ».selectedFan R hne hdisj).fullCones)
      (t : Fin n → ℝ) (ht : ∀ i, |t i| ≤ 1) :
      («Σ».selectedFan R hne hdisj).cartierPoint («Σ».parityCenter P Q L hne) s +
        ∑ i, t i • («Σ».selectedFan R hne hdisj).cartierBasis s i ∈ L.carrier := by
    change («Σ».selectedFan R hne hdisj).cartierPoint
      («Σ».selectedCenteredSupport R (fun u => (L.integralSupport u : ℝ)) 1
        (fun i => («Σ».parityDisplacements P Q L hne i : ℝ))) s + _ ∈ _
    apply «Σ».selected_centered_box_of_charts R hne hdisj L hfanL 1 1
      (fun i => («Σ».parityDisplacements P Q L hne i : ℝ)) L.carrier ?_ ?_ s t ht
    · intro b hfull hnone v hv hcone «λ» «hλ»
      apply L.outside_side_two_box «Σ» hpure hL hfanL hboundL v hv b hfull hcone
      · intro S hS hbad hsub
        have hno : ∀ i, S.positive ≠ (R i).positive := by
          intro i he
          exact hnone i ((S.negative_unique (R i) he) ▸ hsub)
        exact (not_lt_of_ge (hinactive S hS hno)) hbad
      · intro k
        obtain ⟨hlo, hhi⟩ := abs_le.mp («hλ» k)
        constructor <;> linarith
    · intro i b I hfull hI j hj v hv hcone «λ» «hλ»
      have hb := (R i).parityDisplacement_bounds (hR i) (hne i) (hlarge i)
        hpure L hL hfanL hboundL
      have hq : 1 ≤ (R i).negative.card := Finset.card_pos.mpr (hne i)
      have hqcast : (((R i).negative.card - 1 : ℕ) : ℝ) =
          ((R i).negative.card : ℝ) - 1 := by rw [Nat.cast_sub hq, Nat.cast_one]
      have he : 0 < n := by
        have hd := (R i).contractible_dimension_bound (hR i)
        have hr := (R i).fiberDimension_pos
        omega
      have hbox := «Σ».shifted_box_mem hpure L.integralSupport
        (L.integralSupport_isStrictSupport «Σ» hfanL) he
        (L.supportReconstruction_edgesAtLeast «Σ» hpure hfanL hboundL)
        (R i) (hR i) (hne i) b I hI hfull j hj v
        (L.normal_basis_vertex_active «Σ» v hv b hcone)
        2 ((R i).parityDisplacement (hne i) L.integralSupport : ℝ)
        (by norm_num) (by rw [hqcast]; exact hb.2.1)
        (by change _ + 2 + 2 * (R i).baseDimension ≤ (n : ℝ); linarith [hb.2.2.1])
        hb.2.2.2.2 (fun k => 1 + «λ» k)
        (by intro k; obtain ⟨hlo, hhi⟩ := abs_le.mp («hλ» k); constructor <;> linarith)
      rw [L.fanPolytope_integralSupport_eq «Σ» hfanL] at hbox
      simpa only [parityDisplacements, add_assoc] using hbox
  constructor
  · intro s t ht
    apply make_box P hP hfanP hboundP ?_ s t ht
    intro S hS hn
    exact («Σ».parity_unselected_degree_bounds _ _ S hS hn).1
  · intro s t ht
    apply make_box Q hQ hfanQ hboundQ ?_ s t ht
    intro S hS hn
    exact («Σ».parity_unselected_degree_bounds _ _ S hS hn).2

theorem canonical_adjoint_boxes (hpure : «Σ».IsPure)
    (P Q : LatticePolytope n) (hP : P.Smooth) (hQ : Q.Smooth)
    (hfanP : «Σ».realCones = P.normalFan) (hfanQ : «Σ».realCones = Q.normalFan)
    (hboundP : P.EdgesAtLeast (n + 1)) (hboundQ : Q.EdgesAtLeast (n + 1))
    (hne : ∀ i, («Σ».adjointFamily Q i).negative.Nonempty) :
    let Γ := «Σ».selectedFan («Σ».adjointFamily Q) hne
      («Σ».adjointFamily_disjoint hpure Q hQ hfanQ hboundQ)
    (∀ (s : Γ.fullCones) (t : Fin n → ℝ), (∀ i, |t i| ≤ 1 / 2) →
      Γ.cartierPoint («Σ».firstAdjointCenter P Q) s +
        ∑ i, t i • Γ.cartierBasis s i ∈ P.carrier) ∧
    (∀ (s : Γ.fullCones) (t : Fin n → ℝ), (∀ i, |t i| ≤ 1 / 2) →
      Γ.cartierPoint («Σ».secondAdjointCenter Q hne) s +
        ∑ i, t i • Γ.cartierBasis s i ∈ interior Q.carrier) := by
  let R := «Σ».adjointFamily Q
  have hR : ∀ i, (R i).IsCombinatoriallyContractible := «Σ».adjointFamily_contractible Q
  let hdisj := «Σ».adjointFamily_disjoint hpure Q hQ hfanQ hboundQ
  constructor
  · intro s t ht
    change («Σ».selectedFan R hne hdisj).cartierPoint
      («Σ».selectedCenteredSupport R (fun u => (P.integralSupport u : ℝ)) (1 / 2)
        (fun i => ((R i).negative.card : ℝ) - 1)) s + _ ∈ _
    apply «Σ».selected_centered_box_of_charts R hne hdisj P hfanP (1 / 2) (1 / 2)
      (fun i => ((R i).negative.card : ℝ) - 1) P.carrier ?_ ?_ s t ht
    · intro b hfull hnone v hv hcone «λ» «hλ»
      apply P.unit_box_of_edge_bound «Σ» hpure hP hfanP hboundP (by omega)
        v hv b hfull hcone (fun k => 1 / 2 + «λ» k)
      intro k
      obtain ⟨hlo, hhi⟩ := abs_le.mp («hλ» k)
      constructor <;> linarith
    · intro i b I hfull hI j hj v hv hcone «λ» «hλ»
      have hq : 1 ≤ (R i).negative.card := Finset.card_pos.mpr (hne i)
      have hqcast : (((R i).negative.card - 1 : ℕ) : ℝ) =
          ((R i).negative.card : ℝ) - 1 := by rw [Nat.cast_sub hq, Nat.cast_one]
      have hdim : (n : ℝ) = (R i).fiberDimension + (R i).negative.card +
          (R i).baseDimension := by exact_mod_cast (R i).dimension_eq (hR i)
      have hdegree := P.contractible_degree_lower_bound hP «Σ» hpure hfanP hboundP (R i) (hR i)
      have hshift0 : (0 : ℝ) ≤ ((R i).negative.card : ℝ) - 1 := by
        have hqR : (1 : ℝ) ≤ (R i).negative.card := by exact_mod_cast hq
        linarith
      have hmul : (0 : ℝ) ≤ (R i).minimumCoefficient (hne i) *
          (((R i).negative.card : ℝ) - 1) := mul_nonneg (Nat.cast_nonneg _) hshift0
      have hr : (R i).fiberDimension ≤ n := by
        have hd := (R i).contractible_dimension_bound (hR i)
        omega
      have hrR : ((R i).fiberDimension : ℝ) ≤ n := by exact_mod_cast hr
      have hbox := «Σ».shifted_box_mem hpure P.integralSupport
        (P.integralSupport_isStrictSupport «Σ» hfanP) (Nat.succ_pos n)
        (P.supportReconstruction_edgesAtLeast «Σ» hpure hfanP hboundP)
        (R i) (hR i) (hne i) b I hI hfull j hj v
        (P.normal_basis_vertex_active «Σ» v hv b hcone)
        1 (((R i).negative.card : ℝ) - 1) zero_le_one
        (by rw [one_mul, hqcast])
        (by change _ + 1 + 1 * (R i).baseDimension ≤ ((n + 1 : ℕ) : ℝ)
            simp only [one_mul, Nat.cast_add, Nat.cast_one]
            have hr0 : (0 : ℝ) ≤ (R i).fiberDimension := Nat.cast_nonneg _
            linarith)
        (by simp only [one_mul, Nat.cast_add, Nat.cast_one] at *; linarith)
        (fun k => 1 / 2 + «λ» k)
        (by intro k; obtain ⟨hlo, hhi⟩ := abs_le.mp («hλ» k); constructor <;> linarith)
      rw [P.fanPolytope_integralSupport_eq «Σ» hfanP] at hbox
      simpa only [add_assoc] using hbox
  · intro s t ht
    change («Σ».selectedFan R hne hdisj).cartierPoint
      («Σ».selectedCenteredSupport R (fun u => (Q.integralSupport u : ℝ)) (3 / 2)
        (fun i => («Σ».adjointDisplacements Q hne i : ℝ))) s + _ ∈ _
    apply «Σ».selected_centered_box_of_charts R hne hdisj Q hfanQ (3 / 2) (1 / 2)
      (fun i => («Σ».adjointDisplacements Q hne i : ℝ)) (interior Q.carrier) ?_ ?_ s t ht
    · intro b hfull hnone v hv hcone «λ» «hλ»
      have hout : ∀ S : «Σ».PrimitiveRelation, S.IsCombinatoriallyContractible →
          0 < 2 * (S.fiberDimension : ℝ) + 1 -
            S.degree (fun u => (Q.integralSupport u : ℝ)) - S.negativeCoefficientSum →
          ¬ S.negative ⊆ Finset.univ.image b := by
        intro S hS hbad hsub
        have hno : ∀ i, S.positive ≠ (R i).positive := by
          intro i he
          exact hnone i ((S.negative_unique (R i) he) ▸ hsub)
        have hbound := «Σ».adjoint_unselected_degree_bound
          (fun u => (Q.integralSupport u : ℝ)) S hS hno
        rw [S.coefficientSum_cast] at hbound
        linarith
      have hbox := Q.outside_inner_unit_box «Σ» hpure hQ hfanQ hboundQ
        v hv b hfull hcone hout (fun k => 1 / 2 + «λ» k)
        (by intro k; obtain ⟨hlo, hhi⟩ := abs_le.mp («hλ» k); constructor <;> linarith)
      have hcoeff (k : Fin n) : (3 / 2 : ℝ) + «λ» k = 1 + (1 / 2 + «λ» k) := by ring
      simpa only [hcoeff, add_smul, one_smul, Finset.sum_add_distrib, add_assoc] using hbox
    · intro i b I hfull hI j hj v hv hcone «λ» «hλ»
      have hb := (R i).adjointDisplacement_bounds (hR i) (hne i)
        hpure Q hQ hfanQ hboundQ («Σ».selectionRelation_test _ i)
      have hq : 1 ≤ (R i).negative.card := Finset.card_pos.mpr (hne i)
      have hqcast : (((R i).negative.card - 1 : ℕ) : ℝ) =
          ((R i).negative.card : ℝ) - 1 := by rw [Nat.cast_sub hq, Nat.cast_one]
      have hbox := «Σ».shifted_inner_unit_box_mem hpure Q.integralSupport
        (Q.integralSupport_isStrictSupport «Σ» hfanQ) (Nat.succ_pos n)
        (Q.supportReconstruction_edgesAtLeast «Σ» hpure hfanQ hboundQ)
        (R i) (hR i) (hne i) b I hI hfull j hj v
        (Q.normal_basis_vertex_active «Σ» v hv b hcone)
        ((R i).adjointDisplacement (hne i) Q.integralSupport : ℝ)
        (by rw [hqcast]; exact hb.2.1)
        (by change _ + 2 + ((2 * (R i).baseDimension + 1 : ℕ) : ℝ) ≤ ((n + 1 : ℕ) : ℝ)
            simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one]
            linarith [hb.2.2.1])
        (by simpa only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one] using hb.2.2.2)
        (fun k => 1 / 2 + «λ» k)
        (by intro k; obtain ⟨hlo, hhi⟩ := abs_le.mp («hλ» k); constructor <;> linarith)
      rw [Q.fanPolytope_integralSupport_eq «Σ» hfanQ] at hbox
      have hcoeff (k : Fin n) : (1 : ℝ) + (1 / 2 + «λ» k) = 3 / 2 + «λ» k := by ring
      simpa only [adjointDisplacements, hcoeff, add_assoc] using hbox

end SmoothCompleteFan

end PaperVerification.ToricGeometry
end
end Source_ToricCanonicalBoxes
-- END ORIGINAL PaperVerification.ToricCanonicalBoxes


-- BEGIN ORIGINAL PaperVerification.ToricTargetCases
section Source_ToricTargetCases

-- original header: module

-- original header: public import PaperVerification.ToricCenterTargets

-- original header: @[expose] public section

/-!
# Exhaustive integral-height alternatives for the mixed induction

The alternatives use actual primitive facet slacks. The ceiling bounds
give the precise near-locus height budget; no target is discarded at a
boundary or at an unblown singleton focus.
-/

noncomputable section

namespace PaperVerification.ToricGeometry.SmoothCompleteFan

open Set
open scoped BigOperators Classical

variable {n : ℕ} («Σ» : SmoothCompleteFan n)

theorem parity_target_cases (hpure : «Σ».IsPure)
    (P Q : LatticePolytope n) (hP : P.Smooth) (hQ : Q.Smooth)
    (hfanP : «Σ».realCones = P.normalFan) (hfanQ : «Σ».realCones = Q.normalFan)
    (hboundP : P.EdgesAtLeast n) (hboundQ : Q.EdgesAtLeast n)
    (hne : ∀ i, («Σ».parityFamily P Q i).negative.Nonempty)
    (m : Lattice n) (hm : embed n m ∈ interior (P.minkowskiSum Q)) :
    (∃ u ∈ «Σ».rays, latticeSlack (P.integralSupport + Q.integralSupport) m u = 1) ∨
    (∃ i : «Σ».parityIndices P Q,
      (∑ u ∈ («Σ».parityFamily P Q i).negative,
        latticeSlack (P.integralSupport + Q.integralSupport) m u) ≤
          «Σ».parityDisplacements P Q P hne i + «Σ».parityDisplacements P Q Q hne i + 1 ∧
      (∑ u ∈ («Σ».parityFamily P Q i).negative,
        latticeSlack (P.integralSupport + Q.integralSupport) m u) ≤
          2 * ((n : ℤ) - 2 * («Σ».parityFamily P Q i).baseDimension) - 3) ∨
    ((∀ u ∈ «Σ».rays, 2 ≤ latticeSlack (P.integralSupport + Q.integralSupport) m u) ∧
      ∀ i, «Σ».parityDisplacements P Q P hne i + «Σ».parityDisplacements P Q Q hne i + 2 ≤
        ∑ u ∈ («Σ».parityFamily P Q i).negative,
          latticeSlack (P.integralSupport + Q.integralSupport) m u) := by
  have hpos := «Σ».latticeSlack_pos_of_interior_minkowski hpure P Q hfanP hfanQ m hm
  by_cases hold : ∀ u ∈ «Σ».rays,
      2 ≤ latticeSlack (P.integralSupport + Q.integralSupport) m u
  · right
    by_cases hcover : ∀ i,
        «Σ».parityDisplacements P Q P hne i + «Σ».parityDisplacements P Q Q hne i + 2 ≤
          ∑ u ∈ («Σ».parityFamily P Q i).negative,
            latticeSlack (P.integralSupport + Q.integralSupport) m u
    · exact Or.inr ⟨hold, hcover⟩
    · left
      push_neg at hcover
      obtain ⟨i, hi⟩ := hcover
      have hR := «Σ».parityFamily_contractible P Q i
      have hlarge := «Σ».parityFamily_large hpure P Q hP hQ hfanP hfanQ hboundP hboundQ i
      have hA := ((«Σ».parityFamily P Q i).parityDisplacement_bounds hR (hne i) hlarge
        hpure P hP hfanP hboundP).2.2.1
      have hB := ((«Σ».parityFamily P Q i).parityDisplacement_bounds hR (hne i) hlarge
        hpure Q hQ hfanQ hboundQ).2.2.1
      have htA : «Σ».parityDisplacements P Q P hne i ≤
          (n : ℤ) - 2 * («Σ».parityFamily P Q i).baseDimension - 2 := by
        exact_mod_cast hA
      have htB : «Σ».parityDisplacements P Q Q hne i ≤
          (n : ℤ) - 2 * («Σ».parityFamily P Q i).baseDimension - 2 := by
        exact_mod_cast hB
      exact ⟨i, by omega, by omega⟩
  · left
    push_neg at hold
    obtain ⟨u, hu, hd⟩ := hold
    have hh := hpos u hu
    exact ⟨u, hu, by omega⟩

theorem adjoint_target_cases (hpure : «Σ».IsPure)
    (P Q : LatticePolytope n) (hP : P.Smooth) (hQ : Q.Smooth)
    (hfanP : «Σ».realCones = P.normalFan) (hfanQ : «Σ».realCones = Q.normalFan)
    (hboundP : P.EdgesAtLeast (n + 1)) (hboundQ : Q.EdgesAtLeast (n + 1))
    (hne : ∀ i, («Σ».adjointFamily Q i).negative.Nonempty)
    (m : Lattice n) (hm : embed n m ∈ interior (P.minkowskiSum Q)) :
    (∃ u ∈ «Σ».rays, latticeSlack (P.integralSupport + Q.integralSupport) m u = 1) ∨
    ((∀ u ∈ «Σ».rays, 2 ≤ latticeSlack (P.integralSupport + Q.integralSupport) m u) ∧
      ∃ i : «Σ».adjointIndices Q,
        2 * ((«Σ».adjointFamily Q i).negative.card : ℤ) ≤
          ∑ u ∈ («Σ».adjointFamily Q i).negative,
            latticeSlack (P.integralSupport + Q.integralSupport) m u ∧
        (∑ u ∈ («Σ».adjointFamily Q i).negative,
          latticeSlack (P.integralSupport + Q.integralSupport) m u) ≤
            ((«Σ».adjointFamily Q i).negative.card : ℤ) + «Σ».adjointDisplacements Q hne i) ∨
    ((∀ u ∈ «Σ».rays, 2 ≤ latticeSlack (P.integralSupport + Q.integralSupport) m u) ∧
      ∀ i, ((«Σ».adjointFamily Q i).negative.card : ℤ) +
        «Σ».adjointDisplacements Q hne i + 1 ≤
          ∑ u ∈ («Σ».adjointFamily Q i).negative,
            latticeSlack (P.integralSupport + Q.integralSupport) m u) := by
  have hpos := «Σ».latticeSlack_pos_of_interior_minkowski hpure P Q hfanP hfanQ m hm
  by_cases hold : ∀ u ∈ «Σ».rays,
      2 ≤ latticeSlack (P.integralSupport + Q.integralSupport) m u
  · right
    by_cases hcover : ∀ i, ((«Σ».adjointFamily Q i).negative.card : ℤ) +
        «Σ».adjointDisplacements Q hne i + 1 ≤
          ∑ u ∈ («Σ».adjointFamily Q i).negative,
            latticeSlack (P.integralSupport + Q.integralSupport) m u
    · exact Or.inr ⟨hold, hcover⟩
    · left
      push_neg at hcover
      obtain ⟨i, hi⟩ := hcover
      refine ⟨hold, i, ?_, by omega⟩
      calc
        2 * ((«Σ».adjointFamily Q i).negative.card : ℤ) =
            ∑ _u ∈ («Σ».adjointFamily Q i).negative, (2 : ℤ) := by simp; ring
        _ ≤ _ := Finset.sum_le_sum (fun u hu => hold u
          («Σ».ray_mem_of_mem_cone («Σ».adjointFamily Q i).negative_cone hu))
  · left
    push_neg at hold
    obtain ⟨u, hu, hd⟩ := hold
    have hh := hpos u hu
    exact ⟨u, hu, by omega⟩

end PaperVerification.ToricGeometry.SmoothCompleteFan
end
end Source_ToricTargetCases
-- END ORIGINAL PaperVerification.ToricTargetCases


-- BEGIN ORIGINAL PaperVerification.ToricCoveredTargets
section Source_ToricCoveredTargets

-- original header: module

-- original header: public import PaperVerification.ToricCanonicalBoxes
-- original header: public import PaperVerification.ToricTargetCases

-- original header: @[expose] public section

/-!
# Complete decompositions for targets satisfying the center inequalities

The finite obstruction selection, exact integer corrections, center
nefness, actual box containment, and lattice covering are all composed
here. The hypotheses contain no assumed box, nef divisor, primitive
degree bound, or decomposition. Only the original polytopes and the
literal height conditions for this branch remain.
-/

noncomputable section

namespace PaperVerification.ToricGeometry.SmoothCompleteFan

open Set
open PaperVerification.ToricExchange
open scoped BigOperators Classical

variable {n : ℕ} («Σ» : SmoothCompleteFan n)

theorem covered_parity_decomposition (hpure : «Σ».IsPure)
    (P Q : LatticePolytope n) (hP : P.Smooth) (hQ : Q.Smooth)
    (hfanP : «Σ».realCones = P.normalFan) (hfanQ : «Σ».realCones = Q.normalFan)
    (hboundP : P.EdgesAtLeast n) (hboundQ : Q.EdgesAtLeast n)
    (hne : ∀ i, («Σ».parityFamily P Q i).negative.Nonempty)
    (m : Lattice n)
    (hold : ∀ u ∈ «Σ».rays, 2 ≤ latticeSlack (P.integralSupport + Q.integralSupport) m u)
    (hselected : ∀ i,
      «Σ».parityDisplacements P Q P hne i + «Σ».parityDisplacements P Q Q hne i + 2 ≤
        ∑ u ∈ («Σ».parityFamily P Q i).negative,
          latticeSlack (P.integralSupport + Q.integralSupport) m u)
    (p : Lattice n) :
    ∃ x y : Lattice n,
      embed n x ∈ P.carrier ∧ embed n y ∈ Q.carrier ∧
      x + y = m ∧ SameParity x p := by
  let R := «Σ».parityFamily P Q
  let hdisj := «Σ».parityFamily_disjoint hpure P Q hP hQ hfanP hfanQ hboundP hboundQ
  let Γ := «Σ».selectedFan R hne hdisj
  have hΓ : Γ.IsPure := «Σ».selectedFan_isPure R hne hdisj hpure
  obtain ⟨hnefP, hnefQ⟩ := «Σ».canonical_parity_centers_isNef hpure
    P Q hP hQ hfanP hfanQ hboundP hboundQ hne
  obtain ⟨hboxP, hboxQ⟩ := «Σ».canonical_parity_boxes hpure
    P Q hP hQ hfanP hfanQ hboundP hboundQ hne
  have hm := «Σ».parity_centers_cover_of_slacks hpure
    P Q hP hQ hfanP hfanQ hboundP hboundQ hne m hold hselected
  exact Γ.parity_summands_of_nef_centers hΓ P.carrier Q.carrier
    (convex_convexHull ℝ _) (convex_convexHull ℝ _)
    («Σ».parityCenter P Q P hne) («Σ».parityCenter P Q Q hne)
    hnefP hnefQ hboxP hboxQ m p hm

theorem covered_adjoint_decomposition (hpure : «Σ».IsPure)
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
    ∃ x y : Lattice n,
      embed n x ∈ P.carrier ∧ embed n y ∈ interior Q.carrier ∧ x + y = m := by
  let R := «Σ».adjointFamily Q
  let hdisj := «Σ».adjointFamily_disjoint hpure Q hQ hfanQ hboundQ
  let Γ := «Σ».selectedFan R hne hdisj
  have hΓ : Γ.IsPure := «Σ».selectedFan_isPure R hne hdisj hpure
  obtain ⟨hnefP, hnefQ⟩ := «Σ».canonical_adjoint_centers_isNef hpure
    P Q hP hQ hfanP hfanQ hboundP hboundQ hne
  obtain ⟨hboxP, hboxQ⟩ := «Σ».canonical_adjoint_boxes hpure
    P Q hP hQ hfanP hfanQ hboundP hboundQ hne
  have hm := «Σ».adjoint_centers_cover_of_slacks hpure
    P Q hP hQ hfanP hfanQ hboundP hboundQ hne m hold hselected
  exact Γ.integral_summands_of_nef_centers hΓ P.carrier (interior Q.carrier)
    (convex_convexHull ℝ _) (convex_convexHull ℝ _).interior
    («Σ».firstAdjointCenter P Q) («Σ».secondAdjointCenter Q hne)
    hnefP hnefQ hboxP hboxQ m hm

end PaperVerification.ToricGeometry.SmoothCompleteFan
end
end Source_ToricCoveredTargets
-- END ORIGINAL PaperVerification.ToricCoveredTargets


-- BEGIN ORIGINAL PaperVerification.ToricAffineInterior
section Source_ToricAffineInterior

-- original header: module
-- original header: public import PaperVerification.ToricIntegralAffine
-- original header: public import Mathlib.Analysis.Convex.Intrinsic
-- original header: public import Mathlib.Topology.Algebra.ConstMulAction
-- original header: @[expose] public section
/-!
# Relative interiors under saturated integral affine charts

Injective finite-dimensional affine maps preserve intrinsic interiors. The proof
factors an injective linear map through its actual range, using an affine
equivalence and the isometric subtype inclusion. Full-dimensional source charts
therefore convert intrinsic interior exactly to ordinary interior.
-/

noncomputable section

namespace PaperVerification.ToricGeometry

open Set
open scoped Pointwise
open PaperVerification.ToricExchange

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 2000000 in
/-- Relative interior commutes with an injective linear map between finite
real vector spaces, even when its image has lower ambient dimension. -/
theorem intrinsicInterior_linear_image {d n : ℕ}
    (L : Ambient d →ₗ[ℝ] Ambient n) (hL : Function.Injective L) (S : Set (Ambient d)) :
    intrinsicInterior ℝ (L '' S) = L '' intrinsicInterior ℝ S := by
  let e : Ambient d ≃ₗ[ℝ] L.range := LinearEquiv.ofInjective L hL
  let i := L.range.subtypeₗᵢ.toAffineIsometry
  have himage : L '' S = i '' (e.toAffineEquiv '' S) := by
    rw [Set.image_image]
    rfl
  have he : intrinsicInterior ℝ (e.toAffineEquiv '' S) =
      e.toAffineEquiv '' intrinsicInterior ℝ S :=
    AffineEquiv.intrinsicInterior_image (𝕜 := ℝ)
      (V := Ambient d) (W := L.range) (P := Ambient d) (Q := L.range)
      e.toAffineEquiv S
  rw [himage, i.intrinsicInterior_image, he, Set.image_image]
  rfl

/-- In the full-dimensional case, intrinsic interior is exactly ordinary interior. -/
theorem intrinsicInterior_eq_interior_of_fullSpan {n : ℕ} (S : Set (Ambient n))
    (hS : affineSpan ℝ S = ⊤) : intrinsicInterior ℝ S = interior S := by
  rw [intrinsicInterior, hS]
  let e := Homeomorph.Set.univ (Ambient n)
  change e '' interior (e ⁻¹' S) = interior S
  rw [e.image_interior, Set.image_preimage_eq S e.surjective]

namespace IntegralAffineEmbedding

variable {d n : ℕ} (e : IntegralAffineEmbedding d n)

/-- Relative interior commutes with the actual affine lattice chart. -/
theorem intrinsicInterior_image (S : Set (Ambient d)) :
    intrinsicInterior ℝ (e.realMap '' S) = e.realMap '' intrinsicInterior ℝ S := by
  let τ := AffineEquiv.constVAdd ℝ (Ambient n) (embed n e.origin)
  have himage : e.realMap '' S = τ '' (e.realLinear '' S) := by
    rw [Set.image_image]
    rfl
  rw [himage, τ.intrinsicInterior_image,
    intrinsicInterior_linear_image e.realLinear e.injective, Set.image_image]
  rfl

/-- Interior lattice points in source coordinates correspond exactly to
relative-interior ambient lattice points, with no omitted lattice classes. -/
theorem lattice_intrinsicInterior_image_iff (S : Set (Ambient d)) (z : Lattice n) :
    embed n z ∈ intrinsicInterior ℝ (e.realMap '' S) ↔
      ∃ w : Lattice d, embed d w ∈ intrinsicInterior ℝ S ∧ e.latticeMap w = z := by
  rw [e.intrinsicInterior_image]
  exact e.lattice_image_membership (intrinsicInterior ℝ S) z

/-- For a full-dimensional coordinate polytope, the source intrinsic interior
in the previous equivalence is its ordinary topological interior. -/
theorem lattice_interior_image_iff (P : LatticePolytope d) (z : Lattice n) :
    embed n z ∈ intrinsicInterior ℝ (e.realMap '' P.carrier) ↔
      ∃ w : Lattice d, embed d w ∈ interior P.carrier ∧ e.latticeMap w = z := by
  rw [e.lattice_intrinsicInterior_image_iff,
    intrinsicInterior_eq_interior_of_fullSpan P.carrier P.fullDimensional]

/-- Scale only the chart's integral origin; the saturated direction lattice
and its coordinate map remain unchanged. -/
def scaleOrigin (k : ℕ) : IntegralAffineEmbedding d n where
  origin := (k : ℤ) • e.origin
  linear := e.linear
  realLinear := e.realLinear
  injective := e.injective
  compatible := e.compatible
  saturated := e.saturated

/-- Dilating the coordinate set and the chart origin gives the ordinary
ambient dilation, including the translation multiplicity. -/
theorem scaleOrigin_image (k : ℕ) (S : Set (Ambient d)) :
    (e.scaleOrigin k).realMap '' ((k : ℝ) • S) = (k : ℝ) • (e.realMap '' S) := by
  ext z
  constructor
  · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩
    refine ⟨e.realMap x, ⟨x, hx, rfl⟩, ?_⟩
    simp only [realMap_apply, scaleOrigin, embed_int_smul, Int.cast_natCast,
      map_smul, smul_add]
  · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩
    refine ⟨(k : ℝ) • x, ⟨x, hx, rfl⟩, ?_⟩
    simp only [realMap_apply, scaleOrigin, embed_int_smul, Int.cast_natCast,
      map_smul, smul_add]

/-- The double-origin chart records the sum of two affine lattice images. -/
theorem scaleOrigin_two_latticeMap (x y : Lattice d) :
    (e.scaleOrigin 2).latticeMap (x + y) = e.latticeMap x + e.latticeMap y := by
  simp only [latticeMap, scaleOrigin, map_add]
  abel

/-- A nonzero dilation of a full-dimensional coordinate polytope still has
ordinary interior equal to intrinsic interior. -/
theorem intrinsicInterior_dilate_eq_interior (P : LatticePolytope d)
    (r : ℝ) (hr : r ≠ 0) :
    intrinsicInterior ℝ (r • P.carrier) = interior (r • P.carrier) := by
  rw [PaperVerification.ToricExchange.intrinsicInterior_smul r hr,
    intrinsicInterior_eq_interior_of_fullSpan P.carrier P.fullDimensional,
    interior_smul₀ hr]

/-- Relative-interior lattice targets in twice an affine face have exactly
ordinary-interior lattice coordinates in twice the coordinate polytope. -/
theorem lattice_intrinsicInterior_twice_image_iff (P : LatticePolytope d) (z : Lattice n) :
    embed n z ∈ intrinsicInterior ℝ ((2 : ℝ) • (e.realMap '' P.carrier)) ↔
      ∃ w : Lattice d, embed d w ∈ interior ((2 : ℝ) • P.carrier) ∧
        (e.scaleOrigin 2).latticeMap w = z := by
  have hdilate : (e.scaleOrigin 2).realMap '' ((2 : ℝ) • P.carrier) =
      (2 : ℝ) • (e.realMap '' P.carrier) := by
    simpa using e.scaleOrigin_image 2 P.carrier
  rw [← hdilate,
    (e.scaleOrigin 2).lattice_intrinsicInterior_image_iff,
    intrinsicInterior_dilate_eq_interior P (2 : ℝ) (by norm_num)]

end IntegralAffineEmbedding

end PaperVerification.ToricGeometry
end
end Source_ToricAffineInterior
-- END ORIGINAL PaperVerification.ToricAffineInterior


-- BEGIN ORIGINAL PaperVerification.ToricMainReduction
section Source_ToricMainReduction

-- original header: module
-- original header: public import PaperVerification.ToricSmoothFaces
-- original header: public import PaperVerification.ToricAffineInterior
-- original header: @[expose] public section
/-!
# Exact passage from the mixed principal claims to quadratic generation

This file proves the complete face-coordinate and exchange reduction. The two
mixed principal statements are explicit inputs to this reduction; their proofs
are supplied by the dimension induction in `ToricMainTheorems`, which applies
the reduction to obtain the unconditional principal theorem. The unrestricted
integer-decomposition theorem used here has its own independent proof through
smooth face charts.
-/

noncomputable section

namespace PaperVerification.ToricGeometry

open Set
open scoped Pointwise
open PaperVerification.ToricExchange

namespace LatticePolytope

/-- Adding a convex polytope to itself is exactly its ordinary double dilation. -/
theorem minkowskiSum_self {n : ℕ} (P : LatticePolytope n) :
    P.minkowskiSum P = (2 : ℝ) • P.carrier := by
  change P.carrier + P.carrier = _
  have hconv : Convex ℝ P.carrier := convex_convexHull ℝ _
  have hone : (1 : ℝ) + 1 = 2 := by norm_num
  simpa only [hone, one_smul] using (hconv.add_smul
    (show (0 : ℝ) ≤ 1 by norm_num) (show (0 : ℝ) ≤ 1 by norm_num)).symm

/-- The full prescribed-parity mixed statement supplies Proposition 2.1(i)
on every actual face in its saturated affine lattice. -/
theorem faceParity_of_mixed_parity {n : ℕ} (P : LatticePolytope n)
    (hP : P.Smooth) (hlP : P.EdgesAtLeast n)
    (hparity : Theorem1_2PolytopeStatement) :
    FaceParity (embed n) P.carrier := by
  intro F hFc hFP z hz c hc
  obtain ⟨x, hx, hxz⟩ := intrinsicInterior_subset hz
  obtain ⟨d, Q, e, hd, hstrict, hQ, hlQ, heF⟩ :=
    P.smooth_face_chart hP hlP F ⟨x, hx⟩ hFc hFP
  have hld : Q.EdgesAtLeast d := Q.edgesAtLeast_mono hlQ hd
  have hz' : embed n z ∈ intrinsicInterior ℝ ((2 : ℝ) • (e.realMap '' Q.carrier)) := by
    simpa only [heF] using hz
  obtain ⟨u, hu, huz⟩ := (e.lattice_intrinsicInterior_twice_image_iff Q z).mp hz'
  have hcRange : embed n c ∈ Set.range e.realMap := by
    rw [e.realMap_range_eq_affineSpan Q, heF]
    exact hc
  obtain ⟨c0, hc0⟩ := e.exists_latticeMap_of_mem_range c hcRange
  have huSum : embed d u ∈ interior (Q.minkowskiSum Q) := by
    simpa only [Q.minkowskiSum_self] using hu
  obtain ⟨a, b, ha, hb, hab, hpar⟩ :=
    hparity d Q Q hQ hQ rfl hld hld u huSum c0
  refine ⟨e.latticeMap a, e.latticeMap b, ?_, ?_, ?_, ?_⟩
  · rw [e.embed_latticeMap, ← heF]
    exact ⟨embed d a, ha, rfl⟩
  · rw [e.embed_latticeMap, ← heF]
    exact ⟨embed d b, hb, rfl⟩
  · rw [← e.scaleOrigin_two_latticeMap, hab, huz]
  · simpa only [hc0] using e.sameParity_latticeMap hpar

/-- On a proper face the original edge threshold `n` is at least `d+1`.
Thus the full adjoint mixed statement supplies exactly Proposition 2.1(ii). -/
theorem faceAdjoint_of_mixed_adjoint {n : ℕ} (P : LatticePolytope n)
    (hP : P.Smooth) (hlP : P.EdgesAtLeast n)
    (hadjoint : Theorem1_3PolytopeStatement) :
    FaceAdjoint (embed n) P.carrier := by
  intro F hFc hFP hproper z hz
  obtain ⟨x, hx, hxz⟩ := intrinsicInterior_subset hz
  obtain ⟨d, Q, e, hd, hQ, hlQ, heF⟩ :=
    P.proper_smooth_face_chart hP hlP F ⟨x, hx⟩ hFc hFP hproper
  have hld : Q.EdgesAtLeast (d + 1) := Q.edgesAtLeast_mono hlQ (by omega)
  have hz' : embed n z ∈ intrinsicInterior ℝ ((2 : ℝ) • (e.realMap '' Q.carrier)) := by
    simpa only [heF] using hz
  obtain ⟨u, hu, huz⟩ := (e.lattice_intrinsicInterior_twice_image_iff Q z).mp hz'
  have huSum : embed d u ∈ interior (Q.minkowskiSum Q) := by
    simpa only [Q.minkowskiSum_self] using hu
  obtain ⟨a, b, ha, hb, hab⟩ := (hadjoint d Q Q hQ hQ rfl hld hld u).mp huSum
  refine ⟨e.latticeMap a, e.latticeMap b, ?_, ?_, ?_⟩
  · rw [e.embed_latticeMap, ← heF]
    exact ⟨embed d a, ha, rfl⟩
  · rw [← heF, e.intrinsicInterior_image, e.embed_latticeMap]
    refine ⟨embed d b, ?_, rfl⟩
    rw [intrinsicInterior_eq_interior_of_fullSpan Q.carrier Q.fullDimensional]
    exact hb
  · rw [← e.scaleOrigin_two_latticeMap, hab, huz]

end LatticePolytope

/-- The exact principal quadratic-generation statement follows from the two
exact mixed principal statements, with all face and exchange dependencies
proved here. This reduction alone is not a verification of those inputs. -/
theorem theorem1_1_of_mixed (R : Type*) [Field R]
    (hparity : Theorem1_2PolytopeStatement) (hadjoint : Theorem1_3PolytopeStatement) :
    Theorem1_1Statement R := by
  intro n hn P hP hlP
  have hidp := P.integerDecomposition_of_smooth_long_edges hP hlP
  refine ⟨hidp, ?_⟩
  exact (P.proposition2_1 R hidp (P.faceParity_of_mixed_parity hP hlP hparity)
    (P.faceAdjoint_of_mixed_adjoint hP hlP hadjoint)).2

end PaperVerification.ToricGeometry
end
end Source_ToricMainReduction
-- END ORIGINAL PaperVerification.ToricMainReduction


-- BEGIN ORIGINAL PaperVerification.ToricMixedBaseCases
section Source_ToricMixedBaseCases

-- original header: module
-- original header: public import PaperVerification.ToricStatements
-- original header: public import Mathlib.Topology.Algebra.Group.Pointwise
-- original header: @[expose] public section
/-!
# Dimension-zero mixed cases and the automatic inclusion

The mixed induction starts in the actual zero-dimensional lattice.
The reverse inclusion in adjoint multiplication is purely topological and is
proved without smoothness, positivity, or a common normal fan.
-/

noncomputable section

namespace PaperVerification.ToricGeometry

open Set
open scoped Pointwise
open PaperVerification.ToricExchange

namespace LatticePolytope

/-- The carrier of any zero-dimensional lattice polytope is the whole
zero-dimensional real vector space. -/
theorem carrier_eq_univ_zero (P : LatticePolytope 0) : P.carrier = Set.univ := by
  apply Set.eq_univ_of_forall
  intro x
  obtain ⟨z, hz⟩ := P.nonempty
  have hmem : embed 0 z ∈ P.carrier :=
    subset_convexHull ℝ _ ⟨z, hz, rfl⟩
  simpa only [Subsingleton.elim (embed 0 z) x] using hmem

/-- The prescribed-parity base case retains all lattice targets and classes. -/
theorem mixed_parity_dimension_zero (P Q : LatticePolytope 0)
    (m c : Lattice 0) :
    ∃ a b : Lattice 0,
      embed 0 a ∈ P.carrier ∧ embed 0 b ∈ Q.carrier ∧
      a + b = m ∧ SameParity a c := by
  refine ⟨m, 0, ?_, ?_, add_zero m, ?_⟩
  · rw [P.carrier_eq_univ_zero]
    exact Set.mem_univ _
  · rw [Q.carrier_eq_univ_zero]
    exact Set.mem_univ _
  · refine ⟨0, ?_⟩
    exact Subsingleton.elim _ _

/-- Adding any carrier point to an interior point of the second polytope
always gives an interior point of the actual Minkowski sum. -/
theorem add_mem_interior_minkowskiSum {n : ℕ} (P Q : LatticePolytope n)
    (a b : Lattice n) (ha : embed n a ∈ P.carrier)
    (hb : embed n b ∈ interior Q.carrier) :
    embed n (a + b) ∈ interior (P.minkowskiSum Q) := by
  rw [map_add]
  exact subset_interior_add_right (Set.add_mem_add ha hb)

/-- The entire adjoint membership equivalence in dimension zero. -/
theorem mixed_adjoint_dimension_zero (P Q : LatticePolytope 0) (m : Lattice 0) :
    embed 0 m ∈ interior (P.minkowskiSum Q) ↔
      ∃ a b : Lattice 0, embed 0 a ∈ P.carrier ∧
        embed 0 b ∈ interior Q.carrier ∧ a + b = m := by
  constructor
  · intro _
    refine ⟨m, 0, ?_, ?_, add_zero m⟩
    · rw [P.carrier_eq_univ_zero]
      exact Set.mem_univ _
    · rw [Q.carrier_eq_univ_zero, interior_univ]
      exact Set.mem_univ _
  · rintro ⟨a, b, ha, hb, rfl⟩
    exact P.add_mem_interior_minkowskiSum Q a b ha hb

end LatticePolytope

/-- The one-sided formulation used by the induction is equivalent to the
full equality in the principal adjoint statement. The omitted inclusion is
proved above for arbitrary polytopes. -/
theorem theorem1_3_iff_interior_decomposition :
    Theorem1_3PolytopeStatement ↔
      ∀ n : ℕ, ∀ P Q : LatticePolytope n,
        P.Smooth → Q.Smooth → P.SameNormalFan Q →
        P.EdgesAtLeast (n + 1) → Q.EdgesAtLeast (n + 1) →
        ∀ m : Lattice n, embed n m ∈ interior (P.minkowskiSum Q) →
          ∃ a b : Lattice n, embed n a ∈ P.carrier ∧
            embed n b ∈ interior Q.carrier ∧ a + b = m := by
  constructor
  · intro h n P Q hP hQ hfan hlenP hlenQ m hm
    exact (h n P Q hP hQ hfan hlenP hlenQ m).mp hm
  · intro h n P Q hP hQ hfan hlenP hlenQ m
    constructor
    · exact h n P Q hP hQ hfan hlenP hlenQ m
    · rintro ⟨a, b, ha, hb, rfl⟩
      exact P.add_mem_interior_minkowskiSum Q a b ha hb

end PaperVerification.ToricGeometry

end
end Source_ToricMixedBaseCases
-- END ORIGINAL PaperVerification.ToricMixedBaseCases


-- BEGIN ORIGINAL PaperVerification.ToricBundleFanBaseInduction
section Source_ToricBundleFanBaseInduction

-- original header: module

-- original header: public import PaperVerification.ToricBundleFanInduction


-- original header: @[expose] public section
/-!
# Separate base edge bounds and fiber degrees

These sharpened induction interfaces retain the original geometry while
separating its two independent positivity requirements.  They apply to the
quotient faces arising in the nonempty-focus branches: their edges need only
the base-dimensional threshold, while their fiber degree retains its own bound.
-/

noncomputable section

namespace PaperVerification.ToricGeometry.SmoothCompleteFan.PrimitiveRelation.BundleCoordinates

open Set
open scoped BigOperators Classical Pointwise
open PaperVerification.ToricExchange

variable {n : ℕ} {«Σ» : SmoothCompleteFan n} {R : «Σ».PrimitiveRelation}
  (c : R.BundleCoordinates)

theorem fiberDegree_nat_of_degree_bound (c : R.BundleCoordinates)
    (hN : R.negative = ∅) (P : LatticePolytope n) {bound : ℕ}
    (hbound : (bound : ℝ) ≤ R.degree (fun v => (P.integralSupport v : ℝ))) :
    ∃ k : ℕ, (∑ v ∈ R.positive, P.integralSupport v) = k ∧ bound ≤ k := by
  have h := hbound
  simp only [SmoothCompleteFan.PrimitiveRelation.degree, hN, Finset.sum_empty,
    sub_zero] at h
  have hZ : (bound : ℤ) ≤ ∑ v ∈ R.positive, P.integralSupport v := by
    exact_mod_cast h
  let k := (∑ v ∈ R.positive, P.integralSupport v).toNat
  have hk : (k : ℤ) = ∑ v ∈ R.positive, P.integralSupport v :=
    Int.toNat_of_nonneg (le_trans (Int.natCast_nonneg bound) hZ)
  exact ⟨k, hk.symm, by exact_mod_cast hZ.trans_eq hk.symm⟩

/-- Parity needs base edges at least b and fiber degrees at least r,
where b+r is the ambient dimension. -/
theorem bundle_parity_of_base_bounds (hR : R.IsCombinatoriallyContractible)
    (hN : R.negative = ∅) (hpure : «Σ».IsPure)
    (P Q : LatticePolytope n) (hP : P.Smooth) (hQ : Q.Smooth)
    (hfanP : «Σ».realCones = P.normalFan) (hfanQ : «Σ».realCones = Q.normalFan)
    (hlenP : P.EdgesAtLeast (n - c.fiberIndices.card))
    (hlenQ : Q.EdgesAtLeast (n - c.fiberIndices.card))
    (hdegreeP : (c.fiberIndices.card : ℝ) ≤
      R.degree (fun v => (P.integralSupport v : ℝ)))
    (hdegreeQ : (c.fiberIndices.card : ℝ) ≤
      R.degree (fun v => (Q.integralSupport v : ℝ)))
    (IH : ∀ A B : LatticePolytope (n - c.fiberIndices.card),
      A.Smooth → B.Smooth → A.SameNormalFan B →
      A.EdgesAtLeast (n - c.fiberIndices.card) → B.EdgesAtLeast (n - c.fiberIndices.card) →
      ∀ m : Lattice (n - c.fiberIndices.card),
        embed (n - c.fiberIndices.card) m ∈ interior (A.minkowskiSum B) →
      ∀ p : Lattice (n - c.fiberIndices.card), ∃ u v : Lattice (n - c.fiberIndices.card),
        embed (n - c.fiberIndices.card) u ∈ A.carrier ∧
        embed (n - c.fiberIndices.card) v ∈ B.carrier ∧ u + v = m ∧ SameParity u p)
    (m : Lattice n) (hm : embed n m ∈ interior (P.minkowskiSum Q))
    (p : Lattice n) :
    ∃ u v : Lattice n,
      embed n u ∈ P.carrier ∧ embed n v ∈ Q.carrier ∧
        u + v = m ∧ SameParity u p := by
  let a := P.integralSupport
  let b := Q.integralSupport
  have ha : «Σ».IsStrictSupport (fun v => (a v : ℝ)) :=
    P.integralSupport_isStrictSupport «Σ» hfanP
  have hb : «Σ».IsStrictSupport (fun v => (b v : ℝ)) :=
    Q.integralSupport_isStrictSupport «Σ» hfanQ
  have hcarrierP : P.carrier = «Σ».fanPolytope (fun v => (a v : ℝ)) :=
    (P.fanPolytope_integralSupport_eq «Σ» hfanP).symm
  have hcarrierQ : Q.carrier = «Σ».fanPolytope (fun v => (b v : ℝ)) :=
    (Q.fanPolytope_integralSupport_eq «Σ» hfanQ).symm
  obtain ⟨k, hk, hkn⟩ := c.fiberDegree_nat_of_degree_bound hN P hdegreeP
  obtain ⟨l, hl, hln⟩ := c.fiberDegree_nat_of_degree_bound hN Q hdegreeQ
  let γ := c.integerHomogeneousWeight (a + b) m
  have hγ : (∑ v ∈ R.positive, γ v) = (k + l : ℕ) := by
    rw [c.integerHomogeneousWeight_total hN]
    simp only [Pi.add_apply, Finset.sum_add_distrib]
    rw [hk, hl]
    simp
  have hmfan : embed n m ∈ interior («Σ».fanPolytope (fun v => ((a + b) v : ℝ))) :=
    c.interior_minkowski_support hpure P Q hfanP hfanQ m hm
  have hγpos (v : Lattice n) (hv : v ∈ R.positive) : 0 < γ v :=
    c.integerHomogeneousWeight_pos_of_interior (a + b) m hmfan (R.primitive.1 hv)
  obtain ⟨α, β, hα, hβ, hα0, hβ0, hweights, hpar⟩ :=
    c.homogeneous_parity_allocation hkn
      hln γ (c.integerHomogeneousWeight a p) hγ hγpos
  have hαa : (∑ v ∈ R.positive, α v) = ∑ v ∈ R.positive, a v := hα.trans hk.symm
  have hβb : (∑ v ∈ R.positive, β v) = ∑ v ∈ R.positive, b v := hβ.trans hl.symm
  obtain ⟨A, hA, hAsm, hAfan, hAlen⟩ :=
    c.exists_basePolytope hR hN hpure a α ha hαa hα0 P hcarrierP hlenP
  obtain ⟨B, hB, hBsm, hBfan, hBlen⟩ :=
    c.exists_basePolytope hR hN hpure b β hb hβb hβ0 Q hcarrierQ hlenQ
  have hbaseA := c.integerBaseWeight_isStrictSupport hR hN a α ha hαa hα0
  have hbaseB := c.integerBaseWeight_isStrictSupport hR hN b β hb hβb hβ0
  have hmBase : embed (n - c.fiberIndices.card) (c.integerBasePoint m) ∈
      interior (A.minkowskiSum B) := by
    have h := c.integerBasePoint_mem_interior_sum_support hR hN a b α β m hmfan hweights
    rw [c.baseFan.fanPolytope_add (c.baseFan_isPure hpure) _ _
      (SmoothCompleteFan.IsStrictSupport.isNef c.baseFan hbaseA)
      (SmoothCompleteFan.IsStrictSupport.isNef c.baseFan hbaseB)] at h
    simpa only [LatticePolytope.minkowskiSum, hA, hB] using h
  have hABfan : A.SameNormalFan B := hAfan.trans hBfan.symm
  obtain ⟨u, v, hu, hv, huv, hup⟩ := IH A B hAsm hBsm hABfan hAlen hBlen
    (c.integerBasePoint m) hmBase (c.integerBasePoint p)
  refine ⟨c.integerPoint a α u, c.integerPoint b β v, ?_, ?_,
    c.integerPoint_sum_eq a b α β m u v hweights huv,
    c.integerPoint_sameParity a α p u hpar hup⟩
  · rw [hcarrierP, c.integerPoint_mem_fanPolytope_iff hR hN a α hαa]
    exact ⟨hα0, hA ▸ hu⟩
  · rw [hcarrierQ, c.integerPoint_mem_fanPolytope_iff hR hN b β hβb]
    exact ⟨hβ0, hB ▸ hv⟩

/-- Adjoint splitting needs base edges at least b+1 and only the second
fiber degree at least r+1.  The first degree is the actual positive degree
of its strictly supported polytope. -/
theorem bundle_adjoint_of_base_bounds (hR : R.IsCombinatoriallyContractible)
    (hN : R.negative = ∅) (hpure : «Σ».IsPure)
    (P Q : LatticePolytope n) (hP : P.Smooth) (hQ : Q.Smooth)
    (hfanP : «Σ».realCones = P.normalFan) (hfanQ : «Σ».realCones = Q.normalFan)
    (hlenP : P.EdgesAtLeast ((n - c.fiberIndices.card) + 1))
    (hlenQ : Q.EdgesAtLeast ((n - c.fiberIndices.card) + 1))
    (hdegreeQ : ((c.fiberIndices.card + 1 : ℕ) : ℝ) ≤
      R.degree (fun v => (Q.integralSupport v : ℝ)))
    (IH : ∀ A B : LatticePolytope (n - c.fiberIndices.card),
      A.Smooth → B.Smooth → A.SameNormalFan B →
      A.EdgesAtLeast ((n - c.fiberIndices.card) + 1) →
      B.EdgesAtLeast ((n - c.fiberIndices.card) + 1) →
      ∀ m : Lattice (n - c.fiberIndices.card),
        embed (n - c.fiberIndices.card) m ∈ interior (A.minkowskiSum B) →
      ∃ u v : Lattice (n - c.fiberIndices.card),
        embed (n - c.fiberIndices.card) u ∈ A.carrier ∧
        embed (n - c.fiberIndices.card) v ∈ interior B.carrier ∧ u + v = m)
    (m : Lattice n) (hm : embed n m ∈ interior (P.minkowskiSum Q)) :
    ∃ u v : Lattice n,
      embed n u ∈ P.carrier ∧ embed n v ∈ interior Q.carrier ∧ u + v = m := by
  let a := P.integralSupport
  let b := Q.integralSupport
  have ha : «Σ».IsStrictSupport (fun v => (a v : ℝ)) :=
    P.integralSupport_isStrictSupport «Σ» hfanP
  have hb : «Σ».IsStrictSupport (fun v => (b v : ℝ)) :=
    Q.integralSupport_isStrictSupport «Σ» hfanQ
  have hcarrierP : P.carrier = «Σ».fanPolytope (fun v => (a v : ℝ)) :=
    (P.fanPolytope_integralSupport_eq «Σ» hfanP).symm
  have hcarrierQ : Q.carrier = «Σ».fanPolytope (fun v => (b v : ℝ)) :=
    (Q.fanPolytope_integralSupport_eq «Σ» hfanQ).symm
  obtain ⟨k, hk, hkn⟩ := c.fiberDegree_nat_of_degree_bound hN P
    (bound := 0) (by simpa using (R.degree_pos_of_strictSupport ha).le)
  obtain ⟨l, hl, hln⟩ := c.fiberDegree_nat_of_degree_bound hN Q hdegreeQ
  let γ := c.integerHomogeneousWeight (a + b) m
  have hγ : (∑ v ∈ R.positive, γ v) = (k + l : ℕ) := by
    rw [c.integerHomogeneousWeight_total hN]
    simp only [Pi.add_apply, Finset.sum_add_distrib]
    rw [hk, hl]
    simp
  have hmfan : embed n m ∈ interior («Σ».fanPolytope (fun v => ((a + b) v : ℝ))) :=
    c.interior_minkowski_support hpure P Q hfanP hfanQ m hm
  have hγpos (v : Lattice n) (hv : v ∈ R.positive) : 0 < γ v :=
    c.integerHomogeneousWeight_pos_of_interior (a + b) m hmfan (R.primitive.1 hv)
  obtain ⟨α, β, hα, hβ, hα0, hβpos, hweights⟩ :=
    c.homogeneous_adjoint_allocation
      hln γ hγ hγpos
  have hβ0 (v : Lattice n) (hv : v ∈ R.positive) : 0 ≤ β v := (hβpos v hv).le
  have hαa : (∑ v ∈ R.positive, α v) = ∑ v ∈ R.positive, a v := hα.trans hk.symm
  have hβb : (∑ v ∈ R.positive, β v) = ∑ v ∈ R.positive, b v := hβ.trans hl.symm
  obtain ⟨A, hA, hAsm, hAfan, hAlen⟩ :=
    c.exists_basePolytope hR hN hpure a α ha hαa hα0 P hcarrierP hlenP
  obtain ⟨B, hB, hBsm, hBfan, hBlen⟩ :=
    c.exists_basePolytope hR hN hpure b β hb hβb hβ0 Q hcarrierQ hlenQ
  have hbaseA := c.integerBaseWeight_isStrictSupport hR hN a α ha hαa hα0
  have hbaseB := c.integerBaseWeight_isStrictSupport hR hN b β hb hβb hβ0
  have hmBase : embed (n - c.fiberIndices.card) (c.integerBasePoint m) ∈
      interior (A.minkowskiSum B) := by
    have h := c.integerBasePoint_mem_interior_sum_support hR hN a b α β m hmfan hweights
    rw [c.baseFan.fanPolytope_add (c.baseFan_isPure hpure) _ _
      (SmoothCompleteFan.IsStrictSupport.isNef c.baseFan hbaseA)
      (SmoothCompleteFan.IsStrictSupport.isNef c.baseFan hbaseB)] at h
    simpa only [LatticePolytope.minkowskiSum, hA, hB] using h
  have hABfan : A.SameNormalFan B := hAfan.trans hBfan.symm
  obtain ⟨u, v, hu, hv, huv⟩ := IH A B hAsm hBsm hABfan hAlen hBlen
    (c.integerBasePoint m) hmBase
  refine ⟨c.integerPoint a α u, c.integerPoint b β v, ?_, ?_,
    c.integerPoint_sum_eq a b α β m u v hweights huv⟩
  · rw [hcarrierP, c.integerPoint_mem_fanPolytope_iff hR hN a α hαa]
    exact ⟨hα0, hA ▸ hu⟩
  · rw [hcarrierQ, c.integerPoint_mem_interior_fanPolytope_iff hR hN b β hβb]
    exact ⟨hβpos, hB ▸ hv⟩

end PaperVerification.ToricGeometry.SmoothCompleteFan.PrimitiveRelation.BundleCoordinates
end
end Source_ToricBundleFanBaseInduction
-- END ORIGINAL PaperVerification.ToricBundleFanBaseInduction


-- BEGIN ORIGINAL PaperVerification.ToricFocusSlicePolytopes
section Source_ToricFocusSlicePolytopes

-- original header: module

-- original header: public import PaperVerification.ToricFocusHeightDegrees
-- original header: public import PaperVerification.ToricQuotientFacePolytopes

-- original header: @[expose] public section

/-!
# Integral focus slices, including the zero-base nef endpoint

Below the original edge threshold the displaced divisor is strictly
supported. At equality, zero base dimension implies that the quotient
fan has only the fiber primitive collection. Its actual positive degree
proves strict support of the restriction, even when the global displaced
support is merely nef.
-/

noncomputable section

namespace PaperVerification.ToricGeometry.SmoothCompleteFan.PrimitiveRelation

open Set
open scoped BigOperators Classical

variable {n : ℕ} {«Σ» : SmoothCompleteFan n} (R : «Σ».PrimitiveRelation)
    (hR : R.IsCombinatoriallyContractible)
    (b : Module.Basis (Fin n) ℤ (Lattice n)) (I : Finset (Fin n))
    (hI : I.image b = R.negative)

theorem focus_slice_fiber_degree_lower_bound
    (hpure : «Σ».IsPure) (a : Lattice n → ℤ)
    (ha : «Σ».IsStrictSupport (fun u => (a u : ℝ)))
    {e : ℕ} (hedges : («Σ».supportLatticePolytope hpure a ha).EdgesAtLeast e)
    (h : Lattice n → ℕ) :
    (e : ℝ) ≤ (R.focusQuotientRelation hR b I hI).degree
      (fun u => («Σ».faceSupportLattice b I (hI.symm ▸ R.negative_cone)
        (displacedSupportLattice a (I.image b) h) u : ℝ)) := by
  rw [«Σ».faceSupportLattice_cast, R.focusQuotientRelation_degree hR b I hI,
    displacedSupportLattice_cast, hI, R.degree_displaced_focus]
  have hbase := «Σ».support_contractible_degree_lower_bound_of_edges hpure a ha hedges R hR
  have hnonneg : 0 ≤ ∑ u ∈ R.negative, (R.coefficient u : ℝ) * (h u : ℝ) :=
    Finset.sum_nonneg (fun u hu => mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
  exact hbase.trans (le_add_of_nonneg_right hnonneg)

include hR in
/-- Actual strict support of the restriction, with the nef endpoint
included precisely when its base dimension is zero. -/
theorem focus_slice_isStrictSupport
    (hpure : «Σ».IsPure) (a : Lattice n → ℤ)
    (ha : «Σ».IsStrictSupport (fun u => (a u : ℝ)))
    {e : ℕ} (he : 0 < e)
    (hedges : («Σ».supportLatticePolytope hpure a ha).EdgesAtLeast e)
    (h : Lattice n → ℕ) (hbudget : (∑ u ∈ I.image b, h u) ≤ e)
    (hendpoint : (∑ u ∈ I.image b, h u) = e →
      (n - I.card) - R.fiberDimension = 0) :
    («Σ».completeQuotientStarFan b I (hI.symm ▸ R.negative_cone)).IsStrictSupport
      (fun u => («Σ».faceSupportLattice b I (hI.symm ▸ R.negative_cone)
        (displacedSupportLattice a (I.image b) h) u : ℝ)) := by
  let hF : I.image b ∈ «Σ».cones := hI.symm ▸ R.negative_cone
  let Ψ := «Σ».completeQuotientStarFan b I hF
  let d := displacedSupportLattice a (I.image b) h
  by_cases hlt : (∑ u ∈ I.image b, h u) < e
  · rw [«Σ».faceSupportLattice_cast]
    apply «Σ».faceSupport_isStrictSupport b I hF
    rw [displacedSupportLattice_cast]
    apply «Σ».displacedSupport_isStrictSupport_of_edges hpure a ha hedges _ _
      (fun u hu => Nat.cast_nonneg _)
    exact_mod_cast hlt
  · have hzero := hendpoint (by omega)
    let R' := R.focusQuotientRelation hR b I hI
    let c := R'.bundleCoordinates
    have hR' : R'.IsCombinatoriallyContractible :=
      R.focusQuotientRelation_contractible hR b I hI
    have hN' : R'.negative = ∅ := rfl
    have hbasezero : (n - I.card) - c.fiberIndices.card = 0 := by
      rw [c.fiberIndices_card, R.focusQuotientRelation_fiberDimension hR b I hI]
      exact hzero
    let H := «Σ».faceSupportLattice b I hF a
    have hH : Ψ.IsStrictSupport (fun u => (H u : ℝ)) := by
      rw [show (fun u => (H u : ℝ)) = «Σ».faceSupport b I hF
        (fun u => (a u : ℝ)) from «Σ».faceSupportLattice_cast b I hF a]
      exact «Σ».faceSupport_isStrictSupport b I hF _ ha
    have hΨpure : Ψ.IsPure := «Σ».completeQuotientStarFan_isPure hpure b I hF
    apply Ψ.isStrictSupport_of_extremal_primitive_pos hΨpure H hH
    intro S hS
    have hsame : S.positive = R'.positive := by
      by_contra hne
      have hcard := c.other_primitive_card_le hR' hN' S.primitive hne
      rw [hbasezero] at hcard
      have htwo := (Ψ.primitiveCollection_card_bounds S.primitive).1
      omega
    rw [S.degree_unique R' hsame]
    have hdegree := R.focus_slice_fiber_degree_lower_bound hR b I hI hpure a ha hedges h
    have heR : (0 : ℝ) < e := by exact_mod_cast he
    exact heR.trans_le hdegree

/-- The full-dimensional smooth quotient polytope and its saturated
affine image are constructed, with every original degree and edge
threshold retained. The fiber bound concerns its actual integral support. -/
theorem exists_focus_slicePolytope
    (hpure : «Σ».IsPure) (a : Lattice n → ℤ)
    (ha : «Σ».IsStrictSupport (fun u => (a u : ℝ)))
    {e : ℕ} (he : 0 < e)
    (hedges : («Σ».supportLatticePolytope hpure a ha).EdgesAtLeast e)
    (h : Lattice n → ℕ) (hbudget : (∑ u ∈ I.image b, h u) ≤ e)
    (hendpoint : (∑ u ∈ I.image b, h u) = e →
      (n - I.card) - R.fiberDimension = 0) :
    ∃ Q : LatticePolytope (n - I.card),
      Q.carrier = («Σ».completeQuotientStarFan b I (hI.symm ▸ R.negative_cone)).fanPolytope
        (fun u => («Σ».faceSupportLattice b I (hI.symm ▸ R.negative_cone)
          (displacedSupportLattice a (I.image b) h) u : ℝ)) ∧
      Q.Smooth ∧ Q.normalFan =
        («Σ».completeQuotientStarFan b I (hI.symm ▸ R.negative_cone)).realCones ∧
      Q.EdgesAtLeast (e - ∑ u ∈ I.image b, h u) ∧
      (quotientFaceIntegralChart (displacedSupportLattice a (I.image b) h) b I).realMap ''
        Q.carrier = {x ∈ «Σ».fanPolytope (fun u => (a u : ℝ)) | ∀ u ∈ I.image b,
          (dotProductEquiv ℝ (Fin n) (embed n u)) x + (a u : ℝ) = (h u : ℝ)} ∧
      («Σ».completeQuotientStarFan b I (hI.symm ▸ R.negative_cone)).IsStrictSupport
        (fun u => («Σ».faceSupportLattice b I (hI.symm ▸ R.negative_cone)
          (displacedSupportLattice a (I.image b) h) u : ℝ)) ∧
      (e : ℝ) ≤ (R.focusQuotientRelation hR b I hI).degree
        (fun u => (Q.integralSupport u : ℝ)) := by
  let hF : I.image b ∈ «Σ».cones := hI.symm ▸ R.negative_cone
  let Ψ := «Σ».completeQuotientStarFan b I hF
  let d := displacedSupportLattice a (I.image b) h
  let c := «Σ».faceSupportLattice b I hF d
  have hΨpure : Ψ.IsPure := «Σ».completeQuotientStarFan_isPure hpure b I hF
  have hc : Ψ.IsStrictSupport (fun u => (c u : ℝ)) :=
    R.focus_slice_isStrictSupport hR b I hI hpure a ha he hedges h hbudget hendpoint
  let Q := Ψ.supportLatticePolytope hΨpure c hc
  have hQ : Q.carrier = Ψ.fanPolytope (fun u => (c u : ℝ)) :=
    Ψ.supportLatticePolytope_carrier hΨpure c hc
  have hQbound : Q.EdgesAtLeast (e - ∑ u ∈ I.image b, h u) := by
    by_cases hlt : (∑ u ∈ I.image b, h u) < e
    · obtain ⟨A, hA, hAsm, hAfan, hAbound, hAimage⟩ :=
        «Σ».exists_displaced_facePolytope b I hF hpure a ha hedges h hlt
      have hcar : Q.carrier = A.carrier := hQ.trans hA.symm
      simpa only [LatticePolytope.EdgesAtLeast, LatticePolytope.IsEdge, hcar] using hAbound
    · have hzero : e - ∑ u ∈ I.image b, h u = 0 := by omega
      rw [hzero]
      apply (Q.edgesAtLeast_iff 0).mpr
      intro x y hxy
      exact Nat.zero_le _
  have hd : «Σ».IsNef (fun u => (d u : ℝ)) := by
    rw [displacedSupportLattice_cast]
    apply «Σ».displacedSupport_isNef_of_edges hpure a ha hedges _ _
      (fun u hu => Nat.cast_nonneg _)
    exact_mod_cast hbudget
  have himage : (quotientFaceIntegralChart d b I).realMap '' Q.carrier =
      {x ∈ «Σ».fanPolytope (fun u => (a u : ℝ)) | ∀ u ∈ I.image b,
        (dotProductEquiv ℝ (Fin n) (embed n u)) x + (a u : ℝ) = (h u : ℝ)} := by
    rw [hQ, «Σ».quotientFaceIntegralChart_image_fanPolytope b I hF hpure d hd,
      displacedSupportLattice_cast]
    exact «Σ».displaced_supportFace_eq_slice _ _ _ (fun u hu => Nat.cast_nonneg _)
  have hdegree : (R.focusQuotientRelation hR b I hI).degree
      (fun u => (Q.integralSupport u : ℝ)) =
      (R.focusQuotientRelation hR b I hI).degree (fun u => (c u : ℝ)) := by
    apply (R.focusQuotientRelation hR b I hI).degree_congr_on_rays
    · intro u hu
      exact Ψ.supportLatticePolytope_integralSupport_on_ray hΨpure c hc u
        ((R.focusQuotientRelation hR b I hI).primitive.1 hu)
    · intro u hu
      exact Ψ.supportLatticePolytope_integralSupport_on_ray hΨpure c hc u
        (Ψ.ray_mem_of_mem_cone (R.focusQuotientRelation hR b I hI).negative_cone hu)
  refine ⟨Q, hQ, Ψ.supportLatticePolytope_smooth hΨpure c hc,
    Ψ.supportLatticePolytope_normalFan hΨpure c hc, hQbound, himage, hc, ?_⟩
  rw [hdegree]
  exact R.focus_slice_fiber_degree_lower_bound hR b I hI hpure a ha hedges h

end PaperVerification.ToricGeometry.SmoothCompleteFan.PrimitiveRelation
end
end Source_ToricFocusSlicePolytopes
-- END ORIGINAL PaperVerification.ToricFocusSlicePolytopes


-- BEGIN ORIGINAL PaperVerification.ToricNormalAllocation
section Source_ToricNormalAllocation

-- original header: module
-- original header: public import PaperVerification.ToricSimplexParity
-- original header: @[expose] public section
/-!
# Integral normal-height and fiber allocations

The bounded parity split is the exact token-allocation argument of Section 6.5.
It treats every number of coordinates and every prescribed residue vector.
The ordinary fiber allocation is used in the adjoint argument of Section 7.5.
-/

namespace PaperVerification.Toric

open scoped BigOperators

/-- Split a positive normal-height vector in every prescribed parity, while
keeping both total heights at most `R`. The reserve of three is the one used
in Section 6.5 to compensate for both floor operations. -/
theorem bounded_parity_split_nat {q R : ℕ} (hq : q ≤ R)
    (m e : Fin q → ℕ) (hm : ∀ i, 0 < m i) (he : ∀ i, e i ≤ 1)
    (hbudget : (∑ i, m i) + 3 ≤ 2 * R) :
    ∃ h k : Fin q → ℕ,
      (∀ i, h i + k i = m i) ∧ (∑ i, h i) ≤ R ∧ (∑ i, k i) ≤ R ∧
      (∀ i, h i % 2 = e i) := by
  let c : Fin q → ℕ := fun i => (m i - e i) / 2
  let f : Fin q → ℕ := fun i => (m i - e i) % 2
  have hcoord (i : Fin q) : e i + 2 * c i + f i = m i := by
    have hmi := hm i
    have hei := he i
    dsimp only [c, f]
    omega
  have hf (i : Fin q) : f i ≤ 1 := by dsimp only [f]; omega
  have hE : (∑ i, e i) ≤ R := by
    have h : (∑ i, e i) ≤ q := calc
      _ ≤ ∑ _ : Fin q, 1 := Finset.sum_le_sum (fun i _ => he i)
      _ = q := by simp
    exact h.trans hq
  have hF : (∑ i, f i) ≤ R := by
    have h : (∑ i, f i) ≤ q := calc
      _ ≤ ∑ _ : Fin q, 1 := Finset.sum_le_sum (fun i _ => hf i)
      _ = q := by simp
    exact h.trans hq
  have htotal : (∑ i, e i) + 2 * (∑ i, c i) + (∑ i, f i) = ∑ i, m i := by
    calc
      _ = ∑ i, (e i + 2 * c i + f i) := by
        simp only [Finset.sum_add_distrib, Finset.mul_sum]
      _ = ∑ i, m i := Finset.sum_congr rfl (fun i _ => hcoord i)
  let U := (R - ∑ i, e i) / 2
  let V := (R - ∑ i, f i) / 2
  have hcapacity : (∑ i, c i) ≤ U + V := by
    dsimp only [U, V]
    omega
  obtain ⟨u, hu, husum⟩ := allocate_le_sum Finset.univ c ((∑ i, c i) - V)
    (Nat.sub_le _ _)
  let h : Fin q → ℕ := fun i => e i + 2 * u i
  let k : Fin q → ℕ := fun i => f i + 2 * (c i - u i)
  have huv (i : Fin q) : u i ≤ c i := hu i (Finset.mem_univ i)
  have hhsum : (∑ i, h i) = (∑ i, e i) + 2 * ((∑ i, c i) - V) := by
    simp only [h, Finset.sum_add_distrib, ← Finset.mul_sum, husum]
  have hksum : (∑ i, k i) = (∑ i, f i) +
      2 * ((∑ i, c i) - ((∑ i, c i) - V)) := by
    simp only [k, Finset.sum_add_distrib, ← Finset.mul_sum,
      Finset.sum_tsub_distrib Finset.univ (fun i _ => huv i), husum]
  refine ⟨h, k, ?_, ?_, ?_, ?_⟩
  · intro i
    have hi := huv i
    have hci := hcoord i
    change e i + 2 * u i + (f i + 2 * (c i - u i)) = m i
    omega
  · rw [hhsum]
    dsimp only [U, V] at hcapacity ⊢
    omega
  · rw [hksum]
    dsimp only [V]
    omega
  · intro i
    have hi := he i
    change (e i + 2 * u i) % 2 = e i
    omega

/-- Section 6.5 in the actual integer normal lattice, with no restriction on
the chosen integer representative of the parity class. -/
theorem bounded_parity_split_integer {q R : ℕ} (hq : q ≤ R)
    (m α : Fin q → ℤ) (hm : ∀ i, 0 < m i)
    (hbudget : (∑ i, m i) + 3 ≤ 2 * (R : ℤ)) :
    ∃ h k : Fin q → ℤ,
      (∀ i, 0 ≤ h i) ∧ (∀ i, 0 ≤ k i) ∧ h + k = m ∧
      (∑ i, h i) ≤ R ∧ (∑ i, k i) ≤ R ∧
      ∃ w : Fin q → ℤ, h - α = w + w := by
  let mN : Fin q → ℕ := fun i => (m i).toNat
  let e : Fin q → ℕ := fun i => (α i % 2).toNat
  have hmcast (i : Fin q) : (mN i : ℤ) = m i :=
    Int.toNat_of_nonneg (hm i).le
  have hmN (i : Fin q) : 0 < mN i := by
    have hi := hm i
    dsimp only [mN]
    omega
  have he (i : Fin q) : e i ≤ 1 := by dsimp only [e]; omega
  have hsumcast : ((∑ i, mN i : ℕ) : ℤ) = ∑ i, m i := by
    simp only [Nat.cast_sum, hmcast]
  have hbudgetN : (∑ i, mN i) + 3 ≤ 2 * R := by omega
  obtain ⟨hN, kN, hsum, hh, hk, hpar⟩ :=
    bounded_parity_split_nat hq mN e hmN he hbudgetN
  refine ⟨fun i => hN i, fun i => kN i, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i
    exact Nat.cast_nonneg _
  · intro i
    exact Nat.cast_nonneg _
  · funext i
    have hi := hsum i
    have hmi := hmcast i
    change (hN i : ℤ) + (kN i : ℤ) = m i
    omega
  · simpa only [← Nat.cast_sum, Nat.cast_le] using hh
  · simpa only [← Nat.cast_sum, Nat.cast_le] using hk
  · apply (integer_parity_iff_double _ α).mp
    intro i
    have hi := hpar i
    have hei : (e i : ℤ) = α i % 2 :=
      Int.toNat_of_nonneg (Int.emod_nonneg _ (by decide))
    change ((hN i : ℤ) - α i) % 2 = 0
    omega

/-- A nonnegative homogeneous fiber vector admits any prescribed first
total between zero and its total degree. No positivity or parity is required. -/
theorem homogeneous_degree_split {q a b : ℕ} (m : Fin q → ℕ)
    (hm : ∑ i, m i = a + b) :
    ∃ u v : Fin q → ℕ, (∀ i, u i + v i = m i) ∧
      (∑ i, u i) = a ∧ (∑ i, v i) = b := by
  obtain ⟨u, hu, hsum⟩ := allocate_le_sum Finset.univ m a (by omega)
  refine ⟨u, fun i => m i - u i, ?_, hsum, ?_⟩
  · intro i
    have hi := hu i (Finset.mem_univ i)
    change u i + (m i - u i) = m i
    omega
  · rw [Finset.sum_tsub_distrib Finset.univ hu, hm, hsum]
    omega

end PaperVerification.Toric
end Source_ToricNormalAllocation
-- END ORIGINAL PaperVerification.ToricNormalAllocation


-- BEGIN ORIGINAL PaperVerification.ToricNormalFiniteAllocation
section Source_ToricNormalFiniteAllocation

-- original header: module

-- original header: public import PaperVerification.ToricNormalAllocation
-- original header: public import PaperVerification.ToricBundleFanAllocation

-- original header: @[expose] public section

/-! # Bounded parity allocation on an actual finite set of primitive normals -/

noncomputable section

namespace PaperVerification.ToricGeometry

open scoped BigOperators Classical

theorem finset_bounded_parity_split {ι : Type*} (s : Finset ι) {R : ℕ}
    (hs : s.card ≤ R) (m p : ι → ℤ) (hm : ∀ u ∈ s, 0 < m u)
    (hbudget : (∑ u ∈ s, m u) + 3 ≤ 2 * (R : ℤ)) :
    ∃ h k : ι → ℕ,
      (∀ u ∈ s, (h u : ℤ) + (k u : ℤ) = m u) ∧
      (∑ u ∈ s, h u) ≤ R ∧ (∑ u ∈ s, k u) ≤ R ∧
      (∀ u ∈ s, ∃ w : ℤ, (h u : ℤ) - p u = w + w) := by
  let m' : Fin s.card → ℤ := fun j => m (s.equivFin.symm j)
  let p' : Fin s.card → ℤ := fun j => p (s.equivFin.symm j)
  have hm' (j : Fin s.card) : 0 < m' j := hm _ (s.equivFin.symm j).property
  have hbudget' : (∑ j, m' j) + 3 ≤ 2 * (R : ℤ) := by
    simpa only [m', sum_finsetIntegerRestriction] using hbudget
  obtain ⟨h', k', hh', hk', hsum', hH', hK', w, hw⟩ :=
    PaperVerification.Toric.bounded_parity_split_integer hs m' p' hm' hbudget'
  let hZ := finsetIntegerExtension s h'
  let kZ := finsetIntegerExtension s k'
  let h : ι → ℕ := fun u => (hZ u).toNat
  let k : ι → ℕ := fun u => (kZ u).toNat
  have hcast (u : ι) (hu : u ∈ s) : (h u : ℤ) = hZ u := by
    apply Int.toNat_of_nonneg
    change 0 ≤ finsetIntegerExtension s h' u
    rw [finsetIntegerExtension_apply s h' hu]
    exact hh' _
  have kcast (u : ι) (hu : u ∈ s) : (k u : ℤ) = kZ u := by
    apply Int.toNat_of_nonneg
    change 0 ≤ finsetIntegerExtension s k' u
    rw [finsetIntegerExtension_apply s k' hu]
    exact hk' _
  refine ⟨h, k, ?_, ?_, ?_, ?_⟩
  · intro u hu
    rw [hcast u hu, kcast u hu]
    change finsetIntegerExtension s h' u + finsetIntegerExtension s k' u = m u
    rw [finsetIntegerExtension_apply s h' hu, finsetIntegerExtension_apply s k' hu]
    have hsum := congrFun hsum' (s.equivFin ⟨u, hu⟩)
    simpa only [Pi.add_apply, m', Equiv.symm_apply_apply] using hsum
  · have htotal : ((∑ u ∈ s, h u : ℕ) : ℤ) = ∑ j, h' j := by
      rw [Nat.cast_sum, Finset.sum_congr rfl hcast, sum_finsetIntegerExtension]
    have htotal' : ((∑ u ∈ s, h u : ℕ) : ℤ) ≤ R := htotal.symm ▸ hH'
    exact_mod_cast htotal'
  · have htotal : ((∑ u ∈ s, k u : ℕ) : ℤ) = ∑ j, k' j := by
      rw [Nat.cast_sum, Finset.sum_congr rfl kcast, sum_finsetIntegerExtension]
    have htotal' : ((∑ u ∈ s, k u : ℕ) : ℤ) ≤ R := htotal.symm ▸ hK'
    exact_mod_cast htotal'
  · intro u hu
    refine ⟨w (s.equivFin ⟨u, hu⟩), ?_⟩
    rw [hcast u hu]
    change finsetIntegerExtension s h' u - p u = _
    rw [finsetIntegerExtension_apply s h' hu]
    have he := congrFun hw (s.equivFin ⟨u, hu⟩)
    simpa only [Pi.sub_apply, Pi.add_apply, p', Equiv.symm_apply_apply] using he

end PaperVerification.ToricGeometry
end
end Source_ToricNormalFiniteAllocation
-- END ORIGINAL PaperVerification.ToricNormalFiniteAllocation


-- BEGIN ORIGINAL PaperVerification.ToricSlicePairTargets
section Source_ToricSlicePairTargets

-- original header: module

-- original header: public import PaperVerification.ToricNearFacetAdjoint

-- original header: @[expose] public section

/-!
# Exact targets and lattice reconstruction on a pair of normal slices

Normal heights determine an actual saturated affine lattice. The target's
remaining coordinates are integral, and strict incident inequalities give
the ordinary topological interior of the sum of the quotient polytopes.
The canonical slice identity gives the interior-summand reconstruction.
-/

noncomputable section

namespace PaperVerification.ToricGeometry.SmoothCompleteFan

open Set
open scoped BigOperators Classical Pointwise

variable {n : ℕ} («Σ» : SmoothCompleteFan n)
    (b : Module.Basis (Fin n) ℤ (Lattice n)) (I : Finset (Fin n))
    (hF : I.image b ∈ «Σ».cones)

theorem exists_quotient_slice_sum_target
    (a c : Lattice n → ℤ) (h k : Lattice n → ℕ) (m : Lattice n)
    (hm : embed n m ∈ interior («Σ».fanPolytope (fun u => ((a + c) u : ℝ))))
    (hnormal : ∀ u ∈ I.image b,
      latticeSlack (a + c) m u = (h u : ℤ) + (k u : ℤ)) :
    ∃ mQ : Lattice (n - I.card),
      (quotientFaceIntegralChart
        (displacedSupportLattice a (I.image b) h + displacedSupportLattice c (I.image b) k)
        b I).latticeMap mQ = m ∧
      embed (n - I.card) mQ ∈ interior ((«Σ».completeQuotientStarFan b I hF).fanPolytope
        (fun u => ((«Σ».faceSupportLattice b I hF (displacedSupportLattice a (I.image b) h) +
          «Σ».faceSupportLattice b I hF (displacedSupportLattice c (I.image b) k)) u : ℝ))) := by
  let dA := displacedSupportLattice a (I.image b) h
  let dC := displacedSupportLattice c (I.image b) k
  let eSum := quotientFaceIntegralChart (dA + dC) b I
  have hcoeff (u : Lattice n) : (dA + dC) u =
      (a + c) u - if u ∈ I.image b then (h u : ℤ) + (k u : ℤ) else 0 := by
    dsimp only [dA, dC, displacedSupportLattice, Pi.add_apply]
    split_ifs <;> omega
  have hcoeffR : (fun u => ((dA + dC) u : ℝ)) =
      displacedSupport (fun u => ((a + c) u : ℝ)) (I.image b)
        (fun u => (h u : ℝ) + (k u : ℝ)) := by
    funext u
    rw [hcoeff]
    simp only [displacedSupport, Pi.sub_apply, facetWeight]
    split_ifs <;> simp
  have hmactive : ∀ i ∈ I,
      (dotProductEquiv ℝ (Fin n) (embed n (b i))) (embed n m) = -((dA + dC) (b i) : ℝ) := by
    intro i hi
    have hbi : b i ∈ I.image b := Finset.mem_image.mpr ⟨i, hi, rfl⟩
    have hnormal' := hnormal (b i) hbi
    rw [normalRay_pairing_lattice, hcoeff, if_pos hbi]
    have hz : (∑ j, b i j * m j) = -((a + c) (b i) - ((h (b i) : ℤ) + (k (b i) : ℤ))) := by
      dsimp only [latticeSlack] at hnormal'
      omega
    exact_mod_cast hz
  obtain ⟨mQ, hmQmap⟩ := eSum.exists_latticeMap_of_mem_range m (by
    rw [quotientFaceIntegralChart_realMap]
    exact (mem_range_quotientFaceMap_iff _ b I _).mpr hmactive)
  have hmQreal : quotientFaceMap (fun u => ((dA + dC) u : ℝ)) b I
      (embed (n - I.card) mQ) = embed n m := by
    rw [← quotientFaceIntegralChart_realMap, ← IntegralAffineEmbedding.embed_latticeMap]
    exact congrArg (embed n) hmQmap
  refine ⟨mQ, hmQmap, ?_⟩
  have hinterior : embed (n - I.card) mQ ∈ interior
      ((«Σ».completeQuotientStarFan b I hF).fanPolytope
        («Σ».faceSupport b I hF (fun u => ((dA + dC) u : ℝ)))) := by
    rw [hcoeffR]
    apply «Σ».quotient_slice_interior b I hF _ (fun u => (h u : ℝ) + (k u : ℝ))
    rw [← hcoeffR, hmQreal]
    exact hm
  rw [← «Σ».faceSupportLattice_cast, «Σ».faceSupportLattice_add] at hinterior
  exact hinterior

theorem quotient_slice_sum_target_interior
    (a c : Lattice n → ℤ) (h k : Lattice n → ℕ)
    (A C : LatticePolytope (n - I.card))
    (hA : A.carrier = («Σ».completeQuotientStarFan b I hF).fanPolytope
      (fun u => («Σ».faceSupportLattice b I hF (displacedSupportLattice a (I.image b) h) u : ℝ)))
    (hC : C.carrier = («Σ».completeQuotientStarFan b I hF).fanPolytope
      (fun u => («Σ».faceSupportLattice b I hF (displacedSupportLattice c (I.image b) k) u : ℝ)))
    (hpure : «Σ».IsPure)
    (hqa : («Σ».completeQuotientStarFan b I hF).IsNef
      (fun u => («Σ».faceSupportLattice b I hF (displacedSupportLattice a (I.image b) h) u : ℝ)))
    (hqc : («Σ».completeQuotientStarFan b I hF).IsNef
      (fun u => («Σ».faceSupportLattice b I hF (displacedSupportLattice c (I.image b) k) u : ℝ)))
    (mQ : Lattice (n - I.card))
    (hmQ : embed (n - I.card) mQ ∈ interior ((«Σ».completeQuotientStarFan b I hF).fanPolytope
      (fun u => ((«Σ».faceSupportLattice b I hF (displacedSupportLattice a (I.image b) h) +
        «Σ».faceSupportLattice b I hF (displacedSupportLattice c (I.image b) k)) u : ℝ)))) :
    embed (n - I.card) mQ ∈ interior (A.minkowskiSum C) := by
  have hcast : (fun u => ((«Σ».faceSupportLattice b I hF (displacedSupportLattice a (I.image b) h) +
        «Σ».faceSupportLattice b I hF (displacedSupportLattice c (I.image b) k)) u : ℝ)) =
      (fun u => («Σ».faceSupportLattice b I hF (displacedSupportLattice a (I.image b) h) u : ℝ)) +
        (fun u => («Σ».faceSupportLattice b I hF (displacedSupportLattice c (I.image b) k) u : ℝ)) := by
    funext u
    simp only [Pi.add_apply, Int.cast_add]
  rw [hcast, («Σ».completeQuotientStarFan b I hF).fanPolytope_add
    («Σ».completeQuotientStarFan_isPure hpure b I hF) _ _ hqa hqc, ← hA, ← hC] at hmQ
  exact hmQ

/-- A genuine interior lattice point of the parent quotient slice maps
back to an interior lattice point of the original polytope, with the
normal height at least one and the proved nonincident reserve. -/
theorem quotient_slice_interior_lattice_image (hpure : «Σ».IsPure)
    (a : Lattice n → ℤ) (ha : «Σ».IsStrictSupport (fun u => (a u : ℝ)))
    {e : ℕ} (hedges : («Σ».supportLatticePolytope hpure a ha).EdgesAtLeast e)
    (h : Lattice n → ℕ) (hh : ∀ u ∈ I.image b, 1 ≤ h u)
    (hbudget : (∑ u ∈ I.image b, h u) + 1 ≤ e)
    (z : Lattice (n - I.card))
    (hz : embed (n - I.card) z ∈ interior
      ((«Σ».completeQuotientStarFan b I hF).fanPolytope
        (fun u => («Σ».faceSupportLattice b I hF (displacedSupportLattice a (I.image b) h) u : ℝ)))) :
    embed n ((quotientFaceIntegralChart (displacedSupportLattice a (I.image b) h) b I).latticeMap z) ∈
      interior («Σ».fanPolytope (fun u => (a u : ℝ))) := by
  let d := displacedSupportLattice a (I.image b) h
  let Ψ := «Σ».completeQuotientStarFan b I hF
  let eQ := quotientFaceIntegralChart d b I
  have hzadj := (Ψ.lattice_mem_interior_iff_adjointSupport
    («Σ».faceSupportLattice b I hF d) z).mp hz
  have hzcanonical : embed (n - I.card) z ∈ Ψ.fanPolytope
      (fun u => «Σ».faceSupport b I hF (fun u => (d u : ℝ)) u - 1) := by
    simpa only [← «Σ».faceSupportLattice_cast, Int.cast_sub, Int.cast_one] using hzadj
  have hcanonical := «Σ».canonical_slice_eq_of_edges b I hF hpure a ha hedges
    (fun u => (h u : ℝ)) (fun u hu => by exact_mod_cast hh u hu)
    (by exact_mod_cast hbudget)
  rw [← displacedSupportLattice_cast] at hcanonical
  have hzimage : eQ.realMap (embed (n - I.card) z) ∈
      {x ∈ «Σ».fanPolytope (fun u => (a u : ℝ) - 1) | ∀ u ∈ I.image b,
        (dotProductEquiv ℝ (Fin n) (embed n u)) x + (a u : ℝ) = (h u : ℝ)} := by
    rw [← hcanonical, quotientFaceIntegralChart_realMap]
    exact Set.mem_image_of_mem _ hzcanonical
  apply («Σ».lattice_mem_interior_iff_adjointSupport a (eQ.latticeMap z)).mpr
  simpa only [IntegralAffineEmbedding.embed_latticeMap, Int.cast_sub, Int.cast_one] using hzimage.1

end PaperVerification.ToricGeometry.SmoothCompleteFan
end
end Source_ToricSlicePairTargets
-- END ORIGINAL PaperVerification.ToricSlicePairTargets


-- BEGIN ORIGINAL PaperVerification.ToricNearSelectedParity
section Source_ToricNearSelectedParity

-- original header: module

-- original header: public import PaperVerification.ToricFocusSlicePolytopes
-- original header: public import PaperVerification.ToricSlicePairTargets
-- original header: public import PaperVerification.ToricNormalFiniteAllocation
-- original header: public import PaperVerification.ToricBundleFanBaseInduction
-- original header: public import PaperVerification.ToricMixedPolytopeBridges

-- original header: @[expose] public section

/-!
# Every prescribed parity near a selected nonempty focus

The literal normal slacks are split within the exact height budgets. The
resulting saturated quotient slices are genuine smooth polytopes, including
the zero-base nef endpoint. Their actual empty-focus relation supplies the
fiber allocation, and only the ordinary theorem in the smaller base dimension
is used for the remaining coordinates.
-/

noncomputable section

namespace PaperVerification.ToricGeometry.SmoothCompleteFan

open Set
open PaperVerification.ToricExchange
open scoped BigOperators Classical Pointwise

variable {n : ℕ} («Σ» : SmoothCompleteFan n)

theorem near_selected_parity_decomposition (hpure : «Σ».IsPure)
    (a c : Lattice n → ℤ)
    (ha : «Σ».IsStrictSupport (fun u => (a u : ℝ)))
    (hc : «Σ».IsStrictSupport (fun u => (c u : ℝ)))
    (hedgesA : («Σ».supportLatticePolytope hpure a ha).EdgesAtLeast n)
    (hedgesC : («Σ».supportLatticePolytope hpure c hc).EdgesAtLeast n)
    (R : «Σ».PrimitiveRelation) (hR : R.IsCombinatoriallyContractible)
    (hne : R.negative.Nonempty) (hlarge : n < 2 * R.fiberDimension)
    (m : Lattice n)
    (hm : embed n m ∈ interior («Σ».fanPolytope (fun u => ((a + c) u : ℝ))))
    (hbudget : (∑ u ∈ R.negative, latticeSlack (a + c) m u) + 3 ≤
      2 * ((n : ℤ) - 2 * R.baseDimension))
    (IH : ∀ d : ℕ, d < n → ParityDimensionStatement d) (p : Lattice n) :
    ∃ x y : Lattice n,
      embed n x ∈ «Σ».fanPolytope (fun u => (a u : ℝ)) ∧
      embed n y ∈ «Σ».fanPolytope (fun u => (c u : ℝ)) ∧
      x + y = m ∧ SameParity x p := by
  have hdim := R.dimension_eq hR
  have hrpos := R.fiberDimension_pos
  have hqpos : 0 < R.negative.card := Finset.card_pos.mpr hne
  have hn : 0 < n := by omega
  have hbase : 2 * R.baseDimension ≤ n := by omega
  have hqcap : R.negative.card ≤ n - 2 * R.baseDimension := by omega
  have hcapcast : ((n - 2 * R.baseDimension : ℕ) : ℤ) =
      (n : ℤ) - 2 * R.baseDimension := by
    rw [Nat.cast_sub hbase, Nat.cast_mul, Nat.cast_ofNat]
  have hmpos (u : Lattice n) (hu : u ∈ R.negative) :
      0 < latticeSlack (a + c) m u :=
    «Σ».latticeSlack_pos_of_interior (a + c) m hm u
      («Σ».ray_mem_of_mem_cone R.negative_cone hu)
  obtain ⟨h, k, hsum, hH, hK, hpar⟩ := finset_bounded_parity_split R.negative hqcap
    (latticeSlack (a + c) m) (latticeSlack a p) hmpos (by rw [hcapcast]; exact hbudget)
  obtain ⟨b, I, hI'⟩ := «Σ».smooth R.negative R.negative_cone
  have hI : I.image b = R.negative := hI'.symm
  let hF : I.image b ∈ «Σ».cones := hI.symm ▸ R.negative_cone
  let Ψ := «Σ».completeQuotientStarFan b I hF
  let RQ := R.focusQuotientRelation hR b I hI
  let coord := RQ.bundleCoordinates
  have hIcard : I.card = R.negative.card := by
    rw [← hI, Finset.card_image_of_injective I b.injective]
  have hrdim : coord.fiberIndices.card = R.fiberDimension := by
    rw [coord.fiberIndices_card, R.focusQuotientRelation_fiberDimension hR b I hI]
  have hbqdim : (n - I.card) - coord.fiberIndices.card = R.baseDimension := by
    rw [hrdim, hIcard]
    omega
  have hbq0 : (n - I.card) - R.fiberDimension = R.baseDimension := by
    rw [hIcard]
    omega
  have hH' : (∑ u ∈ I.image b, h u) ≤ n - 2 * R.baseDimension := by rw [hI]; exact hH
  have hK' : (∑ u ∈ I.image b, k u) ≤ n - 2 * R.baseDimension := by rw [hI]; exact hK
  obtain ⟨A, hApoly, hAsm, hAfan, hAlen, hAimage, hqa, hAdegree⟩ :=
    R.exists_focus_slicePolytope hR b I hI hpure a ha hn hedgesA h
      (hH'.trans (Nat.sub_le _ _)) (by intro he; rw [hbq0]; omega)
  obtain ⟨C, hCpoly, hCsm, hCfan, hClen, hCimage, hqc, hCdegree⟩ :=
    R.exists_focus_slicePolytope hR b I hI hpure c hc hn hedgesC k
      (hK'.trans (Nat.sub_le _ _)) (by intro he; rw [hbq0]; omega)
  let dA := displacedSupportLattice a (I.image b) h
  let dC := displacedSupportLattice c (I.image b) k
  let eA := quotientFaceIntegralChart dA b I
  let eC := quotientFaceIntegralChart dC b I
  obtain ⟨mQ, hmQmap, hmQ⟩ := «Σ».exists_quotient_slice_sum_target b I hF a c h k m hm
    (by intro u hu; exact (hsum u (hI ▸ hu)).symm)
  have hmQinterior : embed (n - I.card) mQ ∈ interior (A.minkowskiSum C) :=
    «Σ».quotient_slice_sum_target_interior b I hF a c h k A C hApoly hCpoly hpure
      (IsStrictSupport.isNef Ψ hqa) (IsStrictSupport.isNef Ψ hqc) mQ hmQ
  obtain ⟨pQ, hpQ⟩ := quotientFace_parity_representative dA b I p (by
    intro i hi
    have hbi : b i ∈ I.image b := Finset.mem_image.mpr ⟨i, hi, rfl⟩
    obtain ⟨w, hw⟩ := hpar (b i) (hI ▸ hbi)
    refine ⟨-w, ?_⟩
    have hcomm : (∑ j, p j * b i j) = ∑ j, b i j * p j :=
      Finset.sum_congr rfl (fun j hj => mul_comm _ _)
    rw [hcomm]
    dsimp only [dA, displacedSupportLattice]
    rw [if_pos hbi]
    dsimp only [latticeSlack] at hw
    omega)
  have hAlen' : A.EdgesAtLeast ((n - I.card) - coord.fiberIndices.card) :=
    A.edgesAtLeast_mono hAlen (by rw [hbqdim]; omega)
  have hClen' : C.EdgesAtLeast ((n - I.card) - coord.fiberIndices.card) :=
    C.edgesAtLeast_mono hClen (by rw [hbqdim]; omega)
  have hAdegree' : (coord.fiberIndices.card : ℝ) ≤
      RQ.degree (fun u => (A.integralSupport u : ℝ)) := by
    have hle : (coord.fiberIndices.card : ℝ) ≤ (n : ℝ) := by rw [hrdim]; exact_mod_cast (by omega : R.fiberDimension ≤ n)
    exact hle.trans hAdegree
  have hCdegree' : (coord.fiberIndices.card : ℝ) ≤
      RQ.degree (fun u => (C.integralSupport u : ℝ)) := by
    have hle : (coord.fiberIndices.card : ℝ) ≤ (n : ℝ) := by rw [hrdim]; exact_mod_cast (by omega : R.fiberDimension ≤ n)
    exact hle.trans hCdegree
  have hIH : ParityDimensionStatement ((n - I.card) - coord.fiberIndices.card) := by
    rw [hbqdim]
    exact IH R.baseDimension (by omega)
  obtain ⟨xQ, yQ, hxQ, hyQ, hxyQ, hpQ'⟩ := coord.bundle_parity_of_base_bounds
    (R.focusQuotientRelation_contractible hR b I hI) rfl
    («Σ».completeQuotientStarFan_isPure hpure b I hF)
    A C hAsm hCsm hAfan.symm hCfan.symm hAlen' hClen' hAdegree' hCdegree'
    hIH mQ hmQinterior pQ
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

/-- The complete selected-locus parity branch on the original polytopes. -/
theorem polytope_near_selected_parity (hpure : «Σ».IsPure)
    (P Q : LatticePolytope n) (hP : P.Smooth) (hQ : Q.Smooth)
    (hfanP : «Σ».realCones = P.normalFan) (hfanQ : «Σ».realCones = Q.normalFan)
    (hboundP : P.EdgesAtLeast n) (hboundQ : Q.EdgesAtLeast n)
    (R : «Σ».PrimitiveRelation) (hR : R.IsCombinatoriallyContractible)
    (hne : R.negative.Nonempty) (hlarge : n < 2 * R.fiberDimension)
    (m : Lattice n) (hm : embed n m ∈ interior (P.minkowskiSum Q))
    (hbudget : (∑ u ∈ R.negative, latticeSlack (P.integralSupport + Q.integralSupport) m u) + 3 ≤
      2 * ((n : ℤ) - 2 * R.baseDimension))
    (IH : ∀ d : ℕ, d < n → ParityDimensionStatement d) (p : Lattice n) :
    ∃ x y : Lattice n, embed n x ∈ P.carrier ∧ embed n y ∈ Q.carrier ∧
      x + y = m ∧ SameParity x p := by
  have ha := P.integralSupport_isStrictSupport «Σ» hfanP
  have hc := Q.integralSupport_isStrictSupport «Σ» hfanQ
  have hedgesP := P.supportReconstruction_edgesAtLeast «Σ» hpure hfanP hboundP
  have hedgesQ := Q.supportReconstruction_edgesAtLeast «Σ» hpure hfanQ hboundQ
  have hm' : embed n m ∈ interior («Σ».fanPolytope
      (fun u => ((P.integralSupport + Q.integralSupport) u : ℝ))) := by
    rw [«Σ».integralSupport_sum_polytope_eq hpure P Q hfanP hfanQ]
    exact hm
  obtain ⟨x, y, hx, hy, hxy, hp⟩ := «Σ».near_selected_parity_decomposition hpure
    P.integralSupport Q.integralSupport ha hc hedgesP hedgesQ R hR hne hlarge m hm' hbudget IH p
  rw [P.fanPolytope_integralSupport_eq «Σ» hfanP] at hx
  rw [Q.fanPolytope_integralSupport_eq «Σ» hfanQ] at hy
  exact ⟨x, y, hx, hy, hxy, hp⟩

end PaperVerification.ToricGeometry.SmoothCompleteFan
end
end Source_ToricNearSelectedParity
-- END ORIGINAL PaperVerification.ToricNearSelectedParity


-- BEGIN ORIGINAL PaperVerification.ToricNearSelectedAdjoint
section Source_ToricNearSelectedAdjoint

-- original header: module

-- original header: public import PaperVerification.ToricNearSelectedParity

-- original header: @[expose] public section

/-!
# An interior summand near a selected nonempty focus

The second parent has height one in every focus normal, while the first
receives the remaining target height. Actual quotient parent polytopes
satisfy the separate base-edge and fiber-degree bounds. Their ordinary
lower-dimensional adjoint decomposition lifts through the exact canonical
slice identity, with no missing boundary or zero-base case.
-/

noncomputable section

namespace PaperVerification.ToricGeometry.SmoothCompleteFan

open Set
open scoped BigOperators Classical Pointwise

variable {n : ℕ} («Σ» : SmoothCompleteFan n)

theorem near_selected_adjoint_decomposition (hpure : «Σ».IsPure)
    (a c : Lattice n → ℤ)
    (ha : «Σ».IsStrictSupport (fun u => (a u : ℝ)))
    (hc : «Σ».IsStrictSupport (fun u => (c u : ℝ)))
    (hedgesA : («Σ».supportLatticePolytope hpure a ha).EdgesAtLeast (n + 1))
    (hedgesC : («Σ».supportLatticePolytope hpure c hc).EdgesAtLeast (n + 1))
    (R : «Σ».PrimitiveRelation) (hR : R.IsCombinatoriallyContractible)
    (hne : R.negative.Nonempty) (t : ℤ)
    (ht : t ≤ (n : ℤ) - 2 * R.baseDimension - 2)
    (m : Lattice n)
    (hm : embed n m ∈ interior («Σ».fanPolytope (fun u => ((a + c) u : ℝ))))
    (hslacks : ∀ u ∈ R.negative, 2 ≤ latticeSlack (a + c) m u)
    (hbudget : (∑ u ∈ R.negative, latticeSlack (a + c) m u) ≤ R.negative.card + t)
    (IH : ∀ d : ℕ, d < n → AdjointDimensionStatement d) :
    ∃ x y : Lattice n,
      embed n x ∈ «Σ».fanPolytope (fun u => (a u : ℝ)) ∧
      embed n y ∈ interior («Σ».fanPolytope (fun u => (c u : ℝ))) ∧ x + y = m := by
  have hdim := R.dimension_eq hR
  have hrpos := R.fiberDimension_pos
  have hqpos : 0 < R.negative.card := Finset.card_pos.mpr hne
  have hn : 0 < n := by omega
  let h : Lattice n → ℕ := fun u => (latticeSlack (a + c) m u - 1).toNat
  let k : Lattice n → ℕ := fun _ => 1
  have hcast (u : Lattice n) (hu : u ∈ R.negative) :
      (h u : ℤ) = latticeSlack (a + c) m u - 1 :=
    Int.toNat_of_nonneg (by have := hslacks u hu; omega)
  have hsum (u : Lattice n) (hu : u ∈ R.negative) :
      (h u : ℤ) + (k u : ℤ) = latticeSlack (a + c) m u := by
    rw [hcast u hu]
    simp only [k, Nat.cast_one]
    omega
  have hHZ : ((∑ u ∈ R.negative, h u : ℕ) : ℤ) =
      (∑ u ∈ R.negative, latticeSlack (a + c) m u) - R.negative.card := by
    rw [Nat.cast_sum, Finset.sum_congr rfl hcast, Finset.sum_sub_distrib]
    simp only [Finset.sum_const, nsmul_eq_mul, mul_one]
  have hH : (∑ u ∈ R.negative, h u) + 2 * R.baseDimension + 2 ≤ n := by
    have hcast' : ((∑ u ∈ R.negative, h u : ℕ) : ℤ) + 2 * R.baseDimension + 2 ≤ n := by omega
    exact_mod_cast hcast'
  obtain ⟨b, I, hI'⟩ := «Σ».smooth R.negative R.negative_cone
  have hI : I.image b = R.negative := hI'.symm
  let hF : I.image b ∈ «Σ».cones := hI.symm ▸ R.negative_cone
  let Ψ := «Σ».completeQuotientStarFan b I hF
  let RQ := R.focusQuotientRelation hR b I hI
  let coord := RQ.bundleCoordinates
  have hIcard : I.card = R.negative.card := by
    rw [← hI, Finset.card_image_of_injective I b.injective]
  have hrdim : coord.fiberIndices.card = R.fiberDimension := by
    rw [coord.fiberIndices_card, R.focusQuotientRelation_fiberDimension hR b I hI]
  have hbqdim : (n - I.card) - coord.fiberIndices.card = R.baseDimension := by
    rw [hrdim, hIcard]
    omega
  have hH' : (∑ u ∈ I.image b, h u) + 2 * R.baseDimension + 2 ≤ n := by rw [hI]; exact hH
  have hK' : (∑ u ∈ I.image b, k u) = R.negative.card := by simp only [hI, k, Finset.sum_const, smul_eq_mul, mul_one]
  obtain ⟨A, hApoly, hAsm, hAfan, hAlen, hAimage, hqa, hAdegree⟩ :=
    R.exists_focus_slicePolytope hR b I hI hpure a ha (by omega) hedgesA h
      (by omega) (by intro he; omega)
  obtain ⟨C, hCpoly, hCsm, hCfan, hClen, hCimage, hqc, hCdegree⟩ :=
    R.exists_focus_slicePolytope hR b I hI hpure c hc (by omega) hedgesC k
      (by rw [hK']; omega) (by intro he; rw [hK'] at he; omega)
  let dA := displacedSupportLattice a (I.image b) h
  let dC := displacedSupportLattice c (I.image b) k
  let eA := quotientFaceIntegralChart dA b I
  let eC := quotientFaceIntegralChart dC b I
  obtain ⟨mQ, hmQmap, hmQ⟩ := «Σ».exists_quotient_slice_sum_target b I hF a c h k m hm
    (by intro u hu; exact (hsum u (hI ▸ hu)).symm)
  have hmQinterior : embed (n - I.card) mQ ∈ interior (A.minkowskiSum C) :=
    «Σ».quotient_slice_sum_target_interior b I hF a c h k A C hApoly hCpoly hpure
      (IsStrictSupport.isNef Ψ hqa) (IsStrictSupport.isNef Ψ hqc) mQ hmQ
  have hAlen' : A.EdgesAtLeast (((n - I.card) - coord.fiberIndices.card) + 1) :=
    A.edgesAtLeast_mono hAlen (by rw [hbqdim]; omega)
  have hClen' : C.EdgesAtLeast (((n - I.card) - coord.fiberIndices.card) + 1) :=
    C.edgesAtLeast_mono hClen (by rw [hbqdim, hK']; omega)
  have hCdegree' : ((coord.fiberIndices.card + 1 : ℕ) : ℝ) ≤
      RQ.degree (fun u => (C.integralSupport u : ℝ)) := by
    have hle : ((coord.fiberIndices.card + 1 : ℕ) : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by
      rw [hrdim]
      exact_mod_cast (by omega : R.fiberDimension + 1 ≤ n + 1)
    exact hle.trans hCdegree
  have hIH : AdjointDimensionStatement ((n - I.card) - coord.fiberIndices.card) := by
    rw [hbqdim]
    exact IH R.baseDimension (by omega)
  obtain ⟨xQ, yQ, hxQ, hyQ, hxyQ⟩ := coord.bundle_adjoint_of_base_bounds
    (R.focusQuotientRelation_contractible hR b I hI) rfl
    («Σ».completeQuotientStarFan_isPure hpure b I hF)
    A C hAsm hCsm hAfan.symm hCfan.symm hAlen' hClen' hCdegree'
    hIH mQ hmQinterior
  refine ⟨eA.latticeMap xQ, eC.latticeMap yQ, ?_, ?_, ?_⟩
  · have hx : eA.realMap (embed (n - I.card) xQ) ∈ eA.realMap '' A.carrier :=
      Set.mem_image_of_mem _ hxQ
    rw [hAimage] at hx
    simpa only [IntegralAffineEmbedding.embed_latticeMap] using hx.1
  · rw [hCpoly] at hyQ
    exact «Σ».quotient_slice_interior_lattice_image b I hF hpure c hc hedgesC k
      (fun u hu => le_rfl) (by rw [hK']; omega) yQ hyQ
  · rw [← quotientFaceIntegralChart_add, hxyQ]
    exact hmQmap

/-- The complete selected-locus adjoint branch on the original polytopes,
with the literal old normal slacks and an exact integer displacement. -/
theorem polytope_near_selected_adjoint (hpure : «Σ».IsPure)
    (P Q : LatticePolytope n) (hP : P.Smooth) (hQ : Q.Smooth)
    (hfanP : «Σ».realCones = P.normalFan) (hfanQ : «Σ».realCones = Q.normalFan)
    (hboundP : P.EdgesAtLeast (n + 1)) (hboundQ : Q.EdgesAtLeast (n + 1))
    (R : «Σ».PrimitiveRelation) (hR : R.IsCombinatoriallyContractible)
    (hne : R.negative.Nonempty) (t : ℤ)
    (ht : t ≤ (n : ℤ) - 2 * R.baseDimension - 2)
    (m : Lattice n) (hm : embed n m ∈ interior (P.minkowskiSum Q))
    (hslacks : ∀ u ∈ R.negative, 2 ≤ latticeSlack (P.integralSupport + Q.integralSupport) m u)
    (hbudget : (∑ u ∈ R.negative, latticeSlack (P.integralSupport + Q.integralSupport) m u) ≤
      R.negative.card + t)
    (IH : ∀ d : ℕ, d < n → AdjointDimensionStatement d) :
    ∃ x y : Lattice n,
      embed n x ∈ P.carrier ∧ embed n y ∈ interior Q.carrier ∧ x + y = m := by
  have ha := P.integralSupport_isStrictSupport «Σ» hfanP
  have hc := Q.integralSupport_isStrictSupport «Σ» hfanQ
  have hedgesP := P.supportReconstruction_edgesAtLeast «Σ» hpure hfanP hboundP
  have hedgesQ := Q.supportReconstruction_edgesAtLeast «Σ» hpure hfanQ hboundQ
  have hm' : embed n m ∈ interior («Σ».fanPolytope
      (fun u => ((P.integralSupport + Q.integralSupport) u : ℝ))) := by
    rw [«Σ».integralSupport_sum_polytope_eq hpure P Q hfanP hfanQ]
    exact hm
  obtain ⟨x, y, hx, hy, hxy⟩ := «Σ».near_selected_adjoint_decomposition hpure
    P.integralSupport Q.integralSupport ha hc hedgesP hedgesQ R hR hne t ht m hm'
    hslacks hbudget IH
  rw [P.fanPolytope_integralSupport_eq «Σ» hfanP] at hx
  rw [Q.fanPolytope_integralSupport_eq «Σ» hfanQ] at hy
  exact ⟨x, y, hx, hy, hxy⟩

end PaperVerification.ToricGeometry.SmoothCompleteFan
end
end Source_ToricNearSelectedAdjoint
-- END ORIGINAL PaperVerification.ToricNearSelectedAdjoint


-- BEGIN ORIGINAL PaperVerification.ToricMainTheorems
section Source_ToricMainTheorems

-- original header: module

-- original header: public import PaperVerification.ToricCoveredTargets
-- original header: public import PaperVerification.ToricNearSelectedParity
-- original header: public import PaperVerification.ToricNearSelectedAdjoint
-- original header: public import PaperVerification.ToricFanConstruction
-- original header: public import PaperVerification.ToricMixedBaseCases
-- original header: public import PaperVerification.ToricParityClasses
-- original header: public import PaperVerification.ToricMainReduction

-- original header: @[expose] public section

/-!
# The mixed theorems by induction on the actual dimension

The induction hypotheses below are precisely the original mixed assertions
in smaller dimensions. The obstruction families are constructed from all
contractible primitive relations that fail the stated degree tests. Their
focus alternatives and the exhaustive literal-height alternatives account
for every target. No local box, quotient, positivity, or decomposition
assertion is an additional hypothesis of the resulting theorem.

These declarations concern actual lattice polytopes. The separate
scheme/divisor correspondence is needed to transfer the mixed assertions
to the manuscript's scheme-theoretic input language.
-/

noncomputable section

namespace PaperVerification.ToricGeometry

open Set
open PaperVerification.ToricExchange
open scoped BigOperators Classical Pointwise

theorem parity_dimension_statement (n : ℕ) : ParityDimensionStatement n := by
  induction n using Nat.strong_induction_on with
  | h n IH =>
      intro P Q hP hQ hPQ hboundP hboundQ m hm p
      by_cases hn : n = 0
      · subst n
        exact P.mixed_parity_dimension_zero Q m p
      · obtain ⟨«Σ», hfanP, hpure⟩ := P.exists_smooth_complete_normal_fan_exact_pure hP
        have hfanQ : «Σ».realCones = Q.normalFan := hfanP.trans hPQ
        rcases «Σ».parityFamily_focus_cases hpure P Q hP hQ hfanP hfanQ
            hboundP hboundQ with ⟨i, hi⟩ | hne
        · exact «Σ».polytope_fiber_type_parity hpure P Q hP hQ hfanP hfanQ
            hboundP hboundQ («Σ».parityFamily P Q i)
            («Σ».parityFamily_contractible P Q i) hi IH m hm p
        · rcases «Σ».parity_target_cases hpure P Q hP hQ hfanP hfanQ
              hboundP hboundQ hne m hm with
            ⟨u, hu, hu1⟩ | ⟨i, _, hi⟩ | ⟨hold, hcover⟩
          · exact «Σ».polytope_near_facet_parity hpure P Q hP hQ hfanP hfanQ
              hboundP hboundQ u hu m hm hu1 IH p
          · apply «Σ».polytope_near_selected_parity hpure P Q hP hQ hfanP hfanQ
              hboundP hboundQ («Σ».parityFamily P Q i)
              («Σ».parityFamily_contractible P Q i) (hne i)
              («Σ».parityFamily_large hpure P Q hP hQ hfanP hfanQ hboundP hboundQ i)
              m hm _ IH p
            omega
          · exact «Σ».covered_parity_decomposition hpure P Q hP hQ hfanP hfanQ
              hboundP hboundQ hne m hold hcover p

/-- The full prescribed-parity theorem for smooth lattice polytopes
with the same actual normal fan, in every dimension. -/
theorem toric_theorem_1_2_polytope : Theorem1_2PolytopeStatement :=
  parity_dimension_statement

/-- The exact quotient-class formulation, with the actual quotient
`M / 2M` and an arbitrary prescribed class. -/
theorem toric_theorem_1_2_quotient_classes
    (n : ℕ) (P Q : LatticePolytope n)
    (hP : P.Smooth) (hQ : Q.Smooth) (hfan : P.SameNormalFan Q)
    (hboundP : P.EdgesAtLeast n) (hboundQ : Q.EdgesAtLeast n)
    (m : Lattice n) (hm : embed n m ∈ interior (P.minkowskiSum Q))
    (α : ParityClass n) :
    ∃ a b : Lattice n,
      embed n a ∈ P.carrier ∧ embed n b ∈ Q.carrier ∧
      a + b = m ∧ parityClass n a = α :=
  theorem1_2_iff_quotient_classes.mp toric_theorem_1_2_polytope
    n P Q hP hQ hfan hboundP hboundQ m hm α

theorem adjoint_dimension_statement (n : ℕ) : AdjointDimensionStatement n := by
  induction n using Nat.strong_induction_on with
  | h n IH =>
      intro P Q hP hQ hPQ hboundP hboundQ m hm
      by_cases hn : n = 0
      · subst n
        exact (P.mixed_adjoint_dimension_zero Q m).mp hm
      · obtain ⟨«Σ», hfanP, hpure⟩ := P.exists_smooth_complete_normal_fan_exact_pure hP
        have hfanQ : «Σ».realCones = Q.normalFan := hfanP.trans hPQ
        rcases «Σ».adjointFamily_focus_cases hpure Q hQ hfanQ hboundQ with
          ⟨i, hi⟩ | hne
        · exact «Σ».polytope_fiber_type_adjoint hpure P Q hP hQ hfanP hfanQ
            hboundP hboundQ («Σ».adjointFamily Q i)
            («Σ».adjointFamily_contractible Q i) hi IH m hm
        · rcases «Σ».adjoint_target_cases hpure P Q hP hQ hfanP hfanQ
              hboundP hboundQ hne m hm with
            ⟨u, hu, hu1⟩ | ⟨hold, i, _, hi⟩ | ⟨hold, hcover⟩
          · exact «Σ».polytope_near_facet_adjoint hpure P Q hP hQ hfanP hfanQ
              hboundP hboundQ u hu m hm hu1 IH
          · have ht : «Σ».adjointDisplacements Q hne i ≤
                (n : ℤ) - 2 * («Σ».adjointFamily Q i).baseDimension - 2 := by
              have hreal := ((«Σ».adjointFamily Q i).adjointDisplacement_bounds
                («Σ».adjointFamily_contractible Q i) (hne i) hpure Q hQ hfanQ hboundQ
                («Σ».selectionRelation_test _ i)).2.2.1
              exact_mod_cast hreal
            exact «Σ».polytope_near_selected_adjoint hpure P Q hP hQ hfanP hfanQ
              hboundP hboundQ («Σ».adjointFamily Q i)
              («Σ».adjointFamily_contractible Q i) (hne i)
              («Σ».adjointDisplacements Q hne i) ht m hm
              (fun u hu => hold u
                («Σ».ray_mem_of_mem_cone («Σ».adjointFamily Q i).negative_cone hu))
              hi IH
          · exact «Σ».covered_adjoint_decomposition hpure P Q hP hQ hfanP hfanQ
              hboundP hboundQ hne m hold hcover

/-- The full adjoint lattice-point equality, including both inclusions,
with no additional positivity or nondegeneracy hypothesis on the adjoint
polytope. -/
theorem toric_theorem_1_3_polytope : Theorem1_3PolytopeStatement :=
  theorem1_3_iff_interior_decomposition.mpr adjoint_dimension_statement

/-- The same adjoint statement written as the literal equality of
pointwise sums of lattice-point sets. -/
theorem toric_theorem_1_3_polytope_sets
    (n : ℕ) (P Q : LatticePolytope n)
    (hP : P.Smooth) (hQ : Q.Smooth) (hfan : P.SameNormalFan Q)
    (hboundP : P.EdgesAtLeast (n + 1)) (hboundQ : Q.EdgesAtLeast (n + 1)) :
    {m : Lattice n | embed n m ∈ P.carrier} +
        {m : Lattice n | embed n m ∈ interior Q.carrier} =
      {m : Lattice n | embed n m ∈ interior (P.minkowskiSum Q)} := by
  ext m
  constructor
  · rintro ⟨a, ha, b, hb, hab⟩
    exact (toric_theorem_1_3_polytope n P Q hP hQ hfan hboundP hboundQ m).mpr
      ⟨a, b, ha, hb, hab⟩
  · intro hm
    obtain ⟨a, b, ha, hb, hab⟩ :=
      (toric_theorem_1_3_polytope n P Q hP hQ hfan hboundP hboundQ m).mp hm
    exact ⟨a, ha, b, hb, hab⟩

/-- Theorem 1.1 over an arbitrary field: unrestricted integer
decomposition and equality of the actual polynomial kernel with the
ideal generated by all quadratic exchange binomials. -/
theorem toric_theorem_1_1 (k : Type*) [Field k] : Theorem1_1Statement k :=
  theorem1_1_of_mixed k toric_theorem_1_2_polytope toric_theorem_1_3_polytope

end PaperVerification.ToricGeometry

#print axioms PaperVerification.ToricGeometry.toric_theorem_1_2_polytope
#print axioms PaperVerification.ToricGeometry.toric_theorem_1_2_quotient_classes
#print axioms PaperVerification.ToricGeometry.toric_theorem_1_3_polytope
#print axioms PaperVerification.ToricGeometry.toric_theorem_1_3_polytope_sets
#print axioms PaperVerification.ToricGeometry.toric_theorem_1_1
end
end Source_ToricMainTheorems
-- END ORIGINAL PaperVerification.ToricMainTheorems


