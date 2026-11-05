module

public import PaperVerification.ToricFocusHeightDegrees
public import PaperVerification.ToricQuotientFacePolytopes

@[expose] public section

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
