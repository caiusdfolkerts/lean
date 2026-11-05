module

public import PaperVerification.ToricSelectedBounds
public import PaperVerification.ToricSimultaneousLift

@[expose] public section

/-!
# Exact support coefficients at every selected locus

The same coefficient formula covers a newly inserted ray and an unblown
divisor ray. The finite degree identity records every positive and negative
selected contribution, so the correction estimates are ordinary arithmetic.
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

def selectedPullback (a : Lattice n → ℝ) : Lattice n → ℝ :=
  simultaneousSupport («Σ».selectedStarFocus R) a 0

include hdisj in
theorem selectedSupport_at_selected_ray (a : Lattice n → ℝ) (t : ι → ℝ) (i : ι) :
    simultaneousSupport (fun i => (R i).negative) a t («Σ».selectedRay R i) =
      (∑ v ∈ (R i).negative, a v) - t i :=
  simultaneousSupport_at_sum _ («Σ».selectedRay_injective R hdisj) a t i

include hne hdisj in
theorem selectedPullback_at_selected_ray (a : Lattice n → ℝ) (i : ι) :
    «Σ».selectedPullback R a («Σ».selectedRay R i) = ∑ v ∈ (R i).negative, a v := by
  by_cases hi : 2 ≤ (R i).negative.card
  · let i' : «Σ».BlowupIndices R := ⟨i, hi⟩
    have hinj := «Σ».simultaneous_sum_rays_injective («Σ».selectedStarFocus R)
      (fun j => (R j).negative_cone) («Σ».selectedStarFocus_disjoint R hdisj)
    simpa only [selectedPullback, selectedStarFocus, selectedRay, i', Pi.zero_apply, sub_zero] using
      simultaneousSupport_at_sum («Σ».selectedStarFocus R) hinj a 0 i'
  · have hf := «Σ».selected_focus_of_not_blowup R hne i hi
    have heold : «Σ».selectedRay R i ∈ «Σ».rays :=
      «Σ».ray_mem_of_mem_cone (R i).negative_cone (hf.symm ▸ Finset.mem_singleton_self _)
    rw [selectedPullback, «Σ».simultaneousSupport_old («Σ».selectedStarFocus R)
      (fun j => (R j).negative_cone) (fun j => j.property) a 0 _ heold, hf,
      Finset.sum_singleton]

include hne hdisj in
theorem selectedSupport_eq_pullback_sub (a : Lattice n → ℝ) (t : ι → ℝ) :
    simultaneousSupport (fun i => (R i).negative) a t =
      fun v => «Σ».selectedPullback R a v -
        ∑ i, if v = «Σ».selectedRay R i then t i else 0 := by
  funext v
  by_cases hex : ∃ i, v = «Σ».selectedRay R i
  · obtain ⟨i, rfl⟩ := hex
    rw [«Σ».selectedSupport_at_selected_ray R hdisj a t i,
      «Σ».selectedPullback_at_selected_ray R hne hdisj a i]
    have hs : (∑ j, if «Σ».selectedRay R i = «Σ».selectedRay R j then t j else 0) = t i := by
      simp only [(«Σ».selectedRay_injective R hdisj).eq_iff]
      simp
    rw [hs]
  · have hv : ∀ i, v ≠ «Σ».selectedRay R i := by simpa only [not_exists] using hex
    rw [simultaneousSupport_of_not_sum _ a t v hv]
    have hv' : ∀ i : «Σ».BlowupIndices R, v ≠ ∑ w ∈ «Σ».selectedStarFocus R i, w := fun i => hv i
    rw [selectedPullback, simultaneousSupport_of_not_sum _ a 0 v hv']
    simp only [hv, if_false, Finset.sum_const_zero, sub_zero]

include hR hne hdisj in
/-- A different selected ray cannot occur in either side of a selected
primitive relation. For the positive side this uses contraction replacement. -/
theorem selected_ray_not_positive_of_ne (i j : ι) (hij : i ≠ j) :
    «Σ».selectedRay R i ∉ (R j).positive := by
  by_cases hi : 2 ≤ (R i).negative.card
  · intro hh
    exact «Σ».sum_rays_not_mem_rays (R i).negative_cone hi ((R j).primitive.1 hh)
  · have hf := «Σ».selected_focus_of_not_blowup R hne i hi
    have hnot := «Σ».focus_not_subset_positive_of_disjoint (R i).negative
      (R i).negative_cone (R j) (hR j) (hdisj i j hij)
    intro hh
    apply hnot
    simpa only [hf, Finset.singleton_subset_iff] using hh

include hdisj in
theorem selected_ray_not_negative_of_ne (i j : ι) (hij : i ≠ j) :
    «Σ».selectedRay R i ∉ (R j).negative := by
  intro hh
  have hiN := («Σ».sum_rays_mem_cone_iff (R i).negative_cone (R j).negative_cone).mp
    (latticeRayCone_generator (R j).negative hh)
  exact hdisj i j hij ⟨(R j).negative, (R j).negative_cone,
    Finset.union_subset hiN (Finset.Subset.refl _)⟩

include hdisj in
theorem selectedSupport_on_blowup_focus (i : ι) (hi : 2 ≤ (R i).negative.card)
    (a : Lattice n → ℝ) (t : ι → ℝ) {v : Lattice n} (hv : v ∈ (R i).negative) :
    simultaneousSupport (fun j => (R j).negative) a t v = a v := by
  apply simultaneousSupport_of_not_sum
  intro j hh
  by_cases hji : j = i
  · subst j
    exact «Σ».sum_rays_not_mem_rays (R i).negative_cone hi
      (hh ▸ «Σ».ray_mem_of_mem_cone (R i).negative_cone hv)
  · apply «Σ».selected_ray_not_negative_of_ne R hdisj j i hji
    change (∑ w ∈ (R j).negative, w) ∈ (R i).negative
    exact hh ▸ hv

end SmoothCompleteFan

namespace SmoothCompleteFan.PrimitiveRelation

variable {n : ℕ} {Γ : SmoothCompleteFan n} (S : Γ.PrimitiveRelation)

theorem degree_sub_finite_ray_corrections {ι : Type*} [Fintype ι]
    (e : ι → Lattice n) (a : Lattice n → ℝ) (t : ι → ℝ) :
    S.degree (fun v => a v - ∑ i, if v = e i then t i else 0) =
      S.degree a - (∑ i, if e i ∈ S.positive then t i else 0) +
        ∑ i, if e i ∈ S.negative then (S.coefficient (e i) : ℝ) * t i else 0 := by
  have hp : (∑ v ∈ S.positive, ∑ i, if v = e i then t i else 0) =
      ∑ i, if e i ∈ S.positive then t i else 0 := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i hi
    simp
  have hn : (∑ v ∈ S.negative, (S.coefficient v : ℝ) *
      (∑ i, if v = e i then t i else 0)) =
      ∑ i, if e i ∈ S.negative then (S.coefficient (e i) : ℝ) * t i else 0 := by
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i hi
    simp [mul_ite]
  simp only [degree, Finset.sum_sub_distrib, mul_sub, hp, hn]
  ring

end SmoothCompleteFan.PrimitiveRelation

namespace SmoothCompleteFan

variable {n : ℕ} («Σ» : SmoothCompleteFan n)
variable {ι : Type*} [Fintype ι] (R : ι → «Σ».PrimitiveRelation)
variable (hne : ∀ i, (R i).negative.Nonempty)
variable (hdisj : «Σ».PairwiseDisjointFoci (fun i => (R i).negative))

theorem selected_support_degree
    (S : («Σ».selectedFan R hne hdisj).PrimitiveRelation)
    (a : Lattice n → ℝ) (t : ι → ℝ) :
    S.degree (simultaneousSupport (fun i => (R i).negative) a t) =
      S.degree («Σ».selectedPullback R a) -
        (∑ i, if «Σ».selectedRay R i ∈ S.positive then t i else 0) +
        ∑ i, if «Σ».selectedRay R i ∈ S.negative then
          (S.coefficient («Σ».selectedRay R i) : ℝ) * t i else 0 := by
  rw [«Σ».selectedSupport_eq_pullback_sub R hne hdisj a t]
  exact S.degree_sub_finite_ray_corrections («Σ».selectedRay R) («Σ».selectedPullback R a) t

theorem selected_support_degree_ge_pullback
    (S : («Σ».selectedFan R hne hdisj).PrimitiveRelation)
    (a : Lattice n → ℝ) (t : ι → ℝ) (ht : ∀ i, 0 ≤ t i)
    (hpos : ∀ i, «Σ».selectedRay R i ∉ S.positive) :
    S.degree («Σ».selectedPullback R a) ≤
      S.degree (simultaneousSupport (fun i => (R i).negative) a t) := by
  rw [«Σ».selected_support_degree R hne hdisj S a t]
  have hp : (∑ i, if «Σ».selectedRay R i ∈ S.positive then t i else 0) = 0 := by
    simp only [hpos, if_false, Finset.sum_const_zero]
  rw [hp, sub_zero]
  exact le_add_of_nonneg_right (Finset.sum_nonneg (fun i _ => by
    split_ifs
    · exact mul_nonneg (Nat.cast_nonneg _) (ht i)
    · exact le_rfl))

end SmoothCompleteFan

end PaperVerification.ToricGeometry
