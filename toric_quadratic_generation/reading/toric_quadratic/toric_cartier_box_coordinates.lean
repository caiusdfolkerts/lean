module

public import PaperVerification.ToricSelectedCharts
public import PaperVerification.ToricFanFaceHulls

@[expose] public section

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
