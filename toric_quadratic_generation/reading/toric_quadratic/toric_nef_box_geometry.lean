module

public import PaperVerification.ToricOutsideInnerBoxNef
public import PaperVerification.ToricAdjointSupport

@[expose] public section

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
