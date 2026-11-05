module

public import PaperVerification.ToricFanPolytopes

@[expose] public section

/-!
# Corner boxes of genuine nef support polytopes

This form of the corner criterion includes degenerate nef endpoints. The
polytope remains its actual primitive halfspace intersection, and every
corner is obtained from a separately proved nef support subtraction.
-/

noncomputable section

namespace PaperVerification.ToricGeometry.SmoothCompleteFan

open Set
open scoped BigOperators Classical

variable {n : ℕ} («Σ» : SmoothCompleteFan n)

theorem fanPolytope_mono {a c : Lattice n → ℝ}
    (h : ∀ u ∈ «Σ».rays, a u ≤ c u) : «Σ».fanPolytope a ⊆ «Σ».fanPolytope c := by
  intro x hx u hu
  exact (neg_le_neg (h u hu)).trans (hx u hu)

theorem cartierPoint_sub_cone_selection (a : Lattice n → ℝ)
    (s : «Σ».fullCones) (I : Finset (Fin n)) (side : ℝ) :
    «Σ».cartierPoint (a - side • (fun u =>
      if u ∈ I.image («Σ».fullConeBasis s) then 1 else 0)) s =
      «Σ».cartierPoint a s + side • (∑ i ∈ I, «Σ».cartierBasis s i) := by
  have hmem (i : Fin n) : «Σ».fullConeBasis s i ∈ I.image («Σ».fullConeBasis s) ↔ i ∈ I := by
    simp only [Finset.mem_image, («Σ».fullConeBasis s).injective.eq_iff]
    simp
  simp only [cartierPoint, cartierBasis, Pi.sub_apply, Pi.smul_apply, smul_eq_mul,
    hmem, sub_smul, Finset.sum_sub_distrib, neg_sub]
  have he : (∑ i, (side * if i ∈ I then (1 : ℝ) else 0) •
      integralBasisReal (integralDualBasis («Σ».fullConeBasis s)) i) =
      side • ∑ i ∈ I, integralBasisReal (integralDualBasis («Σ».fullConeBasis s)) i := by
    simp only [mul_ite, mul_one, mul_zero, ite_smul, zero_smul]
    rw [Finset.sum_ite_mem, Finset.univ_inter, Finset.smul_sum]
  rw [he]
  abel

theorem corner_vertex_mem_fanPolytope {a : Lattice n → ℝ}
    (s : «Σ».fullCones) (I : Finset (Fin n)) (side : ℝ) (hside : 0 ≤ side)
    (hnef : «Σ».IsNef (a - side • (fun u =>
      if u ∈ I.image («Σ».fullConeBasis s) then 1 else 0))) :
    «Σ».cartierPoint a s + side • (∑ i ∈ I, «Σ».cartierBasis s i) ∈ «Σ».fanPolytope a := by
  rw [← «Σ».cartierPoint_sub_cone_selection]
  apply «Σ».fanPolytope_mono (a := a - side • _) ?_ («Σ».cartierPoint_mem_of_nef hnef s)
  intro u hu
  change a u - side * (if u ∈ I.image («Σ».fullConeBasis s) then 1 else 0) ≤ a u
  split_ifs <;> nlinarith

theorem corner_box_mem_fanPolytope_of_vertices (a : Lattice n → ℝ)
    (v : Ambient n) (B : Fin n → Ambient n) (side : ℝ)
    (hvertices : ∀ I : Finset (Fin n), v + side • (∑ i ∈ I, B i) ∈ «Σ».fanPolytope a)
    (t : Fin n → ℝ) (ht : ∀ i, 0 ≤ t i ∧ t i ≤ side) :
    v + ∑ i, t i • B i ∈ «Σ».fanPolytope a := by
  intro u hu
  let f : Ambient n →ₗ[ℝ] ℝ := dotProductEquiv ℝ (Fin n) (embed n u)
  let I := Finset.univ.filter (fun i => f (B i) < 0)
  have hv := hvertices I u hu
  have hmin : f (v + side • (∑ i ∈ I, B i)) ≤ f (v + ∑ i, t i • B i) := by
    simp only [map_add, map_sum, map_smul, smul_eq_mul]
    apply add_le_add le_rfl
    rw [Finset.mul_sum]
    calc
      (∑ i ∈ I, side * f (B i)) =
          ∑ i, if i ∈ I then side * f (B i) else 0 := by simp
      _ ≤ ∑ i, t i * f (B i) := by
        apply Finset.sum_le_sum
        intro i hi
        by_cases hiI : i ∈ I
        · rw [if_pos hiI]
          exact mul_le_mul_of_nonpos_right (ht i).2 (Finset.mem_filter.mp hiI).2.le
        · rw [if_neg hiI]
          have hf : 0 ≤ f (B i) := by
            simpa only [I, Finset.mem_filter, Finset.mem_univ, true_and, not_lt] using hiI
          exact mul_nonneg (ht i).1 hf
  exact hv.trans hmin

/-- Full corner boxes, including every real point and every nef endpoint,
follow from actual contractible primitive degree inequalities. -/
theorem corner_box_mem_fanPolytope (hpure : «Σ».IsPure)
    (H : Lattice n → ℤ) (hH : «Σ».IsStrictSupport (fun u => (H u : ℝ)))
    (a : Lattice n → ℝ) (side : ℝ) (hside : 0 ≤ side)
    (hdegree : ∀ R : «Σ».PrimitiveRelation, R.IsCombinatoriallyContractible →
      side * R.fiberDimension ≤ R.degree a)
    (s : «Σ».fullCones) (t : Fin n → ℝ) (ht : ∀ i, 0 ≤ t i ∧ t i ≤ side) :
    «Σ».cartierPoint a s + ∑ i, t i • «Σ».cartierBasis s i ∈ «Σ».fanPolytope a := by
  apply «Σ».corner_box_mem_fanPolytope_of_vertices a _ _ side ?_ t ht
  intro I
  apply «Σ».corner_vertex_mem_fanPolytope s I side hside
  apply «Σ».nef_sub_cone_selection_of_contractible_degrees hpure H hH a side hside hdegree
    («Σ».fullCones_mem s)
  rw [«Σ».fullConeBasis_ray_set]
  exact Finset.image_subset_image (Finset.subset_univ I)

end PaperVerification.ToricGeometry.SmoothCompleteFan
