module

public import PaperVerification.ToricSupportAveragedEdges
public import PaperVerification.ToricDisplacedSupport

@[expose] public section

/-!
# Literal edge bounds after moving primitive facets

A nef difference of support functions gives feasible translated, scaled
axis segments in the new polytope. The classification of all actual edges
then transfers the original edge lower bound. This does not identify an
arbitrary wall relation with a primitive or extremal relation.
-/

noncomputable section

namespace PaperVerification.ToricGeometry

open Set
open scoped BigOperators Classical

theorem convex_axis_point_of_le {n : ℕ} (A : Set (Ambient n)) (hA : Convex ℝ A)
    (v e : Ambient n) (L t : ℝ) (hv : v ∈ A) (hL : v + L • e ∈ A)
    (ht : 0 ≤ t) (htL : t ≤ L) : v + t • e ∈ A := by
  by_cases hzero : L = 0
  · have htzero : t = 0 := by linarith
    simpa only [htzero, zero_smul, add_zero] using hv
  · have hLpos : 0 < L := lt_of_le_of_ne (ht.trans htL) (Ne.symm hzero)
    have hratio : t / L ∈ Icc (0 : ℝ) 1 :=
      ⟨div_nonneg ht hLpos.le, (div_le_one hLpos).mpr htL⟩
    have hh := hA.lineMap_mem hv hL hratio
    have heq : AffineMap.lineMap v (v + L • e) (t / L) = v + t • e := by
      rw [AffineMap.lineMap_apply_module', add_sub_cancel_left,
        smul_smul, div_mul_cancel₀ _ hzero, add_comm]
    simpa only [heq] using hh

namespace SmoothCompleteFan

variable {n : ℕ} («Σ» : SmoothCompleteFan n)

theorem cartierPoint_sub (a b : Lattice n → ℝ) (s : «Σ».fullCones) :
    «Σ».cartierPoint (a - b) s = «Σ».cartierPoint a s - «Σ».cartierPoint b s := by
  simp only [cartierPoint, Pi.sub_apply, sub_smul, Finset.sum_sub_distrib, neg_sub]
  abel

theorem cartierPoint_smul (t : ℝ) (a : Lattice n → ℝ) (s : «Σ».fullCones) :
    «Σ».cartierPoint (t • a) s = t • «Σ».cartierPoint a s := by
  simp only [cartierPoint, Pi.smul_apply, smul_eq_mul, mul_smul,
    ← Finset.smul_sum, smul_neg]

/-- The constructed polytope has exactly the prescribed support value
on each genuine primitive fan ray. -/
theorem supportLatticePolytope_integralSupport_on_ray (hpure : «Σ».IsPure)
    (a : Lattice n → ℤ) (ha : «Σ».IsStrictSupport (fun u => (a u : ℝ)))
    (u : Lattice n) (hu : u ∈ «Σ».rays) :
    ((«Σ».supportLatticePolytope hpure a ha).integralSupport u : ℝ) = a u := by
  let P := «Σ».supportLatticePolytope hpure a ha
  obtain ⟨s, hs, hus⟩ := («Σ».mem_rays_iff u).mp hu
  obtain ⟨U, hU, hsU, hUcard⟩ := hpure s hs
  let U' : «Σ».fullCones := ⟨U, Finset.mem_filter.mpr ⟨hU, hUcard⟩⟩
  let v := «Σ».cartierPoint (fun w => (a w : ℝ)) U'
  have hv : v ∈ P.carrier := by
    rw [«Σ».supportLatticePolytope_carrier]
    exact «Σ».cartierPoint_mem_of_nef (IsStrictSupport.isNef «Σ» ha) U'
  have hnormal : embed n u ∈ P.normalCone v := by
    rw [«Σ».supportLatticePolytope_cartier_normalCone]
    exact latticeRayCone_generator U (hsU hus)
  have hp := (P.integralSupport_spec u v hv).2.mpr hnormal
  have hvu := «Σ».cartierPoint_support_eq_of_mem (fun w => (a w : ℝ)) U' (hsU hus)
  linarith

theorem support_contractible_degree_lower_bound_of_edges (hpure : «Σ».IsPure)
    (a : Lattice n → ℤ) (ha : «Σ».IsStrictSupport (fun u => (a u : ℝ)))
    {e : ℕ} (hedges : («Σ».supportLatticePolytope hpure a ha).EdgesAtLeast e)
    (R : «Σ».PrimitiveRelation) (hR : R.IsCombinatoriallyContractible) :
    (e : ℝ) ≤ R.degree (fun u => (a u : ℝ)) := by
  let P := «Σ».supportLatticePolytope hpure a ha
  have hP := «Σ».supportLatticePolytope_smooth hpure a ha
  have hfan := («Σ».supportLatticePolytope_normalFan hpure a ha).symm
  have hl := P.contractible_degree_lower_bound hP «Σ» hpure hfan hedges R hR
  have heq : R.degree (fun u => (P.integralSupport u : ℝ)) =
      R.degree (fun u => (a u : ℝ)) := by
    unfold PrimitiveRelation.degree
    congr 1
    · exact Finset.sum_congr rfl (fun u hu =>
        «Σ».supportLatticePolytope_integralSupport_on_ray hpure a ha u (R.primitive.1 hu))
    · exact Finset.sum_congr rfl (fun u hu =>
        congrArg (fun t : ℝ => (R.coefficient u : ℝ) * t)
          («Σ».supportLatticePolytope_integralSupport_on_ray hpure a ha u
            («Σ».ray_mem_of_mem_cone R.negative_cone hu)))
  rwa [heq] at hl

theorem support_extremal_degree_lower_bound_of_edges (hpure : «Σ».IsPure)
    (a : Lattice n → ℤ) (ha : «Σ».IsStrictSupport (fun u => (a u : ℝ)))
    {e : ℕ} (hedges : («Σ».supportLatticePolytope hpure a ha).EdgesAtLeast e)
    (R : «Σ».PrimitiveRelation) (hR : R.IsExtremal) :
    (e : ℝ) ≤ R.degree (fun u => (a u : ℝ)) :=
  «Σ».support_contractible_degree_lower_bound_of_edges hpure a ha hedges R
    (R.combinatoriallyContractible_of_extremal hR)

/-- Nef displaced support from the literal all-edge hypothesis, including
the exact endpoint where the total displacement equals the edge bound. -/
theorem displacedSupport_isNef_of_edges (hpure : «Σ».IsPure)
    (a : Lattice n → ℤ) (ha : «Σ».IsStrictSupport (fun u => (a u : ℝ)))
    {e : ℕ} (hedges : («Σ».supportLatticePolytope hpure a ha).EdgesAtLeast e)
    (T : Finset (Lattice n)) (h : Lattice n → ℝ)
    (hh : ∀ u ∈ T, 0 ≤ h u) (hbudget : (∑ u ∈ T, h u) ≤ e) :
    «Σ».IsNef (displacedSupport (fun u => (a u : ℝ)) T h) :=
  «Σ».displacedSupport_isNef hpure a ha _ e
    («Σ».support_extremal_degree_lower_bound_of_edges hpure a ha hedges) T h hh hbudget

theorem displacedSupport_isStrictSupport_of_edges (hpure : «Σ».IsPure)
    (a : Lattice n → ℤ) (ha : «Σ».IsStrictSupport (fun u => (a u : ℝ)))
    {e : ℕ} (hedges : («Σ».supportLatticePolytope hpure a ha).EdgesAtLeast e)
    (T : Finset (Lattice n)) (h : Lattice n → ℝ)
    (hh : ∀ u ∈ T, 0 ≤ h u) (hbudget : (∑ u ∈ T, h u) < e) :
    «Σ».IsStrictSupport (displacedSupport (fun u => (a u : ℝ)) T h) :=
  «Σ».displacedSupport_isStrictSupport hpure a ha _ e
    («Σ».support_extremal_degree_lower_bound_of_edges hpure a ha hedges) T h hh hbudget

/-- A genuine nef support difference transfers all actual edge bounds
through the common primitive coordinate directions. -/
theorem support_edgesAtLeast_of_nef_difference (hpure : «Σ».IsPure)
    (a d : Lattice n → ℤ)
    (ha : «Σ».IsStrictSupport (fun u => (a u : ℝ)))
    (hd : «Σ».IsStrictSupport (fun u => (d u : ℝ)))
    {e bound : ℕ} (hedges : («Σ».supportLatticePolytope hpure a ha).EdgesAtLeast e)
    (c : ℝ) (hc : 0 ≤ c)
    (hnef : «Σ».IsNef ((fun u => (d u : ℝ)) - c • (fun u => (a u : ℝ))))
    (hbound : (bound : ℝ) ≤ c * e) :
    («Σ».supportLatticePolytope hpure d hd).EdgesAtLeast bound := by
  let A : Lattice n → ℝ := fun u => (a u : ℝ)
  let D : Lattice n → ℝ := fun u => (d u : ℝ)
  let N := D - c • A
  apply «Σ».support_edgesAtLeast_of_axis_points hpure d hd bound
  intro s i
  have hAxisA := «Σ».support_axis_point_of_edgesAtLeast hpure a ha hedges s i
  have hN := «Σ».cartierPoint_mem_of_nef hnef s
  have hlarge : «Σ».cartierPoint D s + (c * e) • «Σ».cartierBasis s i ∈ «Σ».fanPolytope D := by
    have heq : «Σ».cartierPoint D s + (c * e) • «Σ».cartierBasis s i =
        c • («Σ».cartierPoint A s + (e : ℝ) • «Σ».cartierBasis s i) + «Σ».cartierPoint N s := by
      dsimp [N]
      rw [«Σ».cartierPoint_sub, «Σ».cartierPoint_smul, smul_add, smul_smul]
      abel
    rw [heq]
    intro u hu
    have hAu := hAxisA u hu
    have hNu := hN u hu
    have hmult := mul_le_mul_of_nonneg_left hAu hc
    change -(D u - c * A u) ≤
      (dotProductEquiv ℝ (Fin n) (embed n u)) («Σ».cartierPoint N s) at hNu
    rw [map_add, map_smul]
    change -D u ≤ c *
      (dotProductEquiv ℝ (Fin n) (embed n u))
        («Σ».cartierPoint A s + (e : ℝ) • «Σ».cartierBasis s i) +
      (dotProductEquiv ℝ (Fin n) (embed n u)) («Σ».cartierPoint N s)
    nlinarith
  exact convex_axis_point_of_le («Σ».fanPolytope D) («Σ».convex_fanPolytope D)
    («Σ».cartierPoint D s) («Σ».cartierBasis s i) (c * e) bound
    («Σ».cartierPoint_mem_of_nef (IsStrictSupport.isNef «Σ» hd) s)
    hlarge (Nat.cast_nonneg _) hbound

/-- The proportional remainder of a displaced support function is nef.
Only the already proved extremal criterion and the exact facet-degree
estimate are used. -/
theorem displacedSupport_nef_difference (hpure : «Σ».IsPure)
    (a : Lattice n → ℤ) (ha : «Σ».IsStrictSupport (fun u => (a u : ℝ)))
    (e : ℝ) (he : 0 < e)
    (hdegree : ∀ R : «Σ».PrimitiveRelation, R.IsExtremal →
      e ≤ R.degree (fun u => (a u : ℝ)))
    (T : Finset (Lattice n)) (h : Lattice n → ℝ) (hh : ∀ u ∈ T, 0 ≤ h u) :
    «Σ».IsNef (displacedSupport (fun u => (a u : ℝ)) T h -
      (1 - (∑ u ∈ T, h u) / e) • (fun u => (a u : ℝ))) := by
  let A : Lattice n → ℝ := fun u => (a u : ℝ)
  let H := ∑ u ∈ T, h u
  have hH : 0 ≤ H := Finset.sum_nonneg hh
  have hHe : 0 ≤ H / e := div_nonneg hH he.le
  apply («Σ».isNef_iff_extremal_primitive_nonneg hpure a ha _).mpr
  intro R hR
  have hd := hdegree R hR
  have hf := R.degree_facetWeight_le T h hh
  have hmul := mul_le_mul_of_nonneg_left hd hHe
  have hcancel : (H / e) * e = H := div_mul_cancel₀ H he.ne'
  rw [hcancel] at hmul
  rw [R.degree_sub, R.degree_smul, displacedSupport, R.degree_sub]
  change 0 ≤ R.degree A - R.degree (facetWeight T h) -
    (1 - H / e) * R.degree A
  change R.degree (facetWeight T h) ≤ H at hf
  nlinarith

/-- Every actual edge loses at most the total normal displacement.
The resulting support is required to be strict only because the target
is an ordinary full-dimensional lattice polytope. -/
theorem displacedSupport_edgesAtLeast (hpure : «Σ».IsPure)
    (a d : Lattice n → ℤ)
    (ha : «Σ».IsStrictSupport (fun u => (a u : ℝ)))
    (hd : «Σ».IsStrictSupport (fun u => (d u : ℝ)))
    {e bound : ℕ} (he : 0 < e)
    (hedges : («Σ».supportLatticePolytope hpure a ha).EdgesAtLeast e)
    (T : Finset (Lattice n)) (h : Lattice n → ℝ)
    (hh : ∀ u ∈ T, 0 ≤ h u)
    (hdcoeff : (fun u => (d u : ℝ)) = displacedSupport (fun u => (a u : ℝ)) T h)
    (hbudget : (∑ u ∈ T, h u) ≤ e)
    (hbound : (bound : ℝ) ≤ (e : ℝ) - ∑ u ∈ T, h u) :
    («Σ».supportLatticePolytope hpure d hd).EdgesAtLeast bound := by
  have heR : (0 : ℝ) < e := by exact_mod_cast he
  have hdegree := «Σ».support_extremal_degree_lower_bound_of_edges hpure a ha hedges
  let c := 1 - (∑ u ∈ T, h u) / (e : ℝ)
  have hc : 0 ≤ c := by
    dsimp [c]
    exact sub_nonneg.mpr ((div_le_one heR).mpr hbudget)
  have hnef := «Σ».displacedSupport_nef_difference hpure a ha e heR hdegree T h hh
  rw [← hdcoeff] at hnef
  apply «Σ».support_edgesAtLeast_of_nef_difference hpure a d ha hd hedges c hc hnef
  have hcancel : c * (e : ℝ) = (e : ℝ) - ∑ u ∈ T, h u := by
    dsimp [c]
    rw [sub_mul, one_mul, div_mul_cancel₀ _ heR.ne']
  rwa [hcancel]

end SmoothCompleteFan

end PaperVerification.ToricGeometry
