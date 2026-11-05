module

public import VolumePolynomials.FixedFacetNormals
public import VolumePolynomials.LinearFrame

@[expose] public section
set_option autoImplicit false

/-!
# Fixed finite facet functionals in an arbitrary finite-dimensional space

The Euclidean halfspace representation is transported through an actual linear
equivalence. The retained data include nonzero functionals, their distinct
positive rays, the exact halfspace formula, and a relative interior witness on
each facet of the unweighted sum.
-/

noncomputable section
open Set Module
open scoped Pointwise RealInnerProductSpace BigOperators

namespace VolumePolynomials.PolytopeGeometry

open OAI.Paper092

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem image_weighted_sum {ι : Type*} [Fintype ι]
    (L : E →ₗ[ℝ] F) (A : ι → Set E) (t : ι → ℝ) :
    L '' (∑ i, t i • A i) = ∑ i, t i • (L '' A i) := by
  first
  | rw [Set.image_finsetSum]
    apply Finset.sum_congr rfl
    intro i hi
    exact Set.image_smul_comm L (t i) (A i) (fun x => L.map_smul (t i) x)

theorem support_image (L : E →L[ℝ] F) (A : Set E) (l : F →L[ℝ] ℝ) :
    SupportGeometry.support (L '' A) l = SupportGeometry.support A (l.comp L) := by
  first
  | unfold SupportGeometry.support
    rw [Set.image_image]
    rfl

structure FixedFacets {ι : Type*} [Fintype ι] (A : ι → Set E) where
  count : ℕ
  normal : Fin count → E →L[ℝ] ℝ
  normal_ne_zero : ∀ i, normal i ≠ 0
  positive_ray_injective : ∀ i j {c : ℝ}, 0 < c → normal i = c • normal j → i = j
  body_eq : ∀ t : ι → ℝ, (∀ j, 0 < t j) →
    (∑ j, t j • A j) =
      {x | ∀ i, normal i x ≤ ∑ j, t j * SupportGeometry.support (A j) (normal i)}
  strict_face_point : ∀ i, ∃ x : E,
    normal i x = ∑ j, SupportGeometry.support (A j) (normal i) ∧
    ∀ k, k ≠ i → normal k x < ∑ j, SupportGeometry.support (A j) (normal k)

/-- This proof-data object is constructed from the actual finite hulls. Its
halfspace identity is a conclusion, not an assumed geometric interface. -/
theorem exists_fixedFacets [FiniteDimensional ℝ E]
    {ι : Type*} [Fintype ι] (A : ι → Set E)
    (hA : ∀ i, IsFiniteHull (A i)) (hne : ∀ i, (A i).Nonempty)
    (hint : (interior (∑ i, A i)).Nonempty) : Nonempty (FixedFacets A) := by
  first
  | classical
    let e : E ≃L[ℝ] Euclidean (finrank ℝ E) :=
      ContinuousLinearEquiv.ofFinrankEq (by simp)
    let B : ι → Set (Euclidean (finrank ℝ E)) := fun i => e '' A i
    have hB : ∀ i, IsFiniteHull (B i) := fun i => (hA i).linear_image e.toLinearMap
    have hneB : ∀ i, (B i).Nonempty := fun i => (hne i).image e
    have hsum : (∑ i, B i) = e '' (∑ i, A i) := by
      rw [Set.image_finsetSum]
    have hintB : (interior (∑ i, B i)).Nonempty := by
      rw [hsum]
      change (interior (e.toHomeomorph '' (∑ i, A i))).Nonempty
      rw [← e.toHomeomorph.image_interior]
      exact hint.image e
    have hsumFinite : IsFiniteHull (∑ i, B i) :=
      IsFiniteHull.sum Finset.univ B (fun i _ => hB i)
    obtain ⟨k, P, hP, he⟩ := hsumFinite.has_irredundant_halfspaces hintB
    let l : Fin k → E →L[ℝ] ℝ := fun i => (innerSL ℝ (P.normal i)).comp e.toContinuousLinearMap
    have hsupport (i : Fin k) (j : ι) :
        SupportGeometry.support (B j) (innerSL ℝ (P.normal i)) =
          SupportGeometry.support (A j) (l i) :=
      support_image e.toContinuousLinearMap (A j) (innerSL ℝ (P.normal i))
    have hheight (i : Fin k) : P.offset i =
        ∑ j, SupportGeometry.support (A j) (l i) := by
      obtain ⟨x, hx, _⟩ := P.exists_strict_face_point_of_essential i (he i)
      have hs : SupportGeometry.support P.body (innerSL ℝ (P.normal i)) = P.offset i :=
        (P.offset_eq_support i ⟨x, hx⟩).symm
      rw [← hs, hP, SupportGeometry.support_sum Finset.univ B
        (fun j _ => (hB j).isCompact) (fun j _ => hneB j)]
      exact Finset.sum_congr rfl (fun j _ => hsupport i j)
    refine ⟨⟨k, l, ?_, ?_, ?_, ?_⟩⟩
    · intro i hi
      have h := congrArg (fun f : E →L[ℝ] ℝ => f (e.symm (P.normal i))) hi
      simpa only [l, ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
        ContinuousLinearEquiv.apply_symm_apply,
        innerSL_apply_apply, real_inner_self_eq_norm_sq, P.normal_unit,
        one_pow, ContinuousLinearMap.zero_apply, one_ne_zero] using h
    · intro i j c hc hij
      have hn : P.normal i = c • P.normal j := by
        apply ext_inner_right ℝ
        intro y
        have h := congrArg (fun f : E →L[ℝ] ℝ => f (e.symm y)) hij
        simpa only [l, ContinuousLinearMap.comp_apply,
          ContinuousLinearEquiv.coe_coe,
          ContinuousLinearEquiv.apply_symm_apply, ContinuousLinearMap.smul_apply,
          smul_eq_mul, innerSL_apply_apply, real_inner_smul_left] using h
      have hc1 : c = 1 := by
        have h := congrArg norm hn
        simpa only [P.normal_unit, norm_smul, Real.norm_eq_abs, abs_of_pos hc, mul_one]
          using h.symm
      apply P.normal_injective_of_essential he
      simpa only [hc1, one_smul] using hn
    · intro t ht
      have hBt := positive_sum_eq_fixed_halfspaces B hB hneB hintB P hP t ht
      have himage : e '' (∑ i, t i • A i) = ∑ i, t i • B i := by
        have hecoe : (e.toLinearMap : E → Euclidean (finrank ℝ E)) = e := rfl
        simpa only [B, hecoe]
          using image_weighted_sum e.toLinearMap A t
      ext x
      constructor
      · intro hx i
        have hxB : e x ∈ ∑ j, t j • B j := by
          rw [← himage]
          exact mem_image_of_mem e hx
        rw [hBt] at hxB
        simpa only [hsupport, l, ContinuousLinearMap.comp_apply,
          ContinuousLinearEquiv.coe_coe, innerSL_apply_apply]
          using hxB i
      · intro hx
        have hxB : e x ∈ ∑ j, t j • B j := by
          rw [hBt]
          intro i
          simpa only [hsupport, l, ContinuousLinearMap.comp_apply,
            ContinuousLinearEquiv.coe_coe, innerSL_apply_apply]
            using hx i
        rw [← himage] at hxB
        obtain ⟨y, hy, hyx⟩ := hxB
        exact e.injective hyx ▸ hy
    · intro i
      obtain ⟨x, hx, hstrict⟩ := P.exists_strict_face_point_of_essential i (he i)
      refine ⟨e.symm x, ?_, fun j hji => ?_⟩
      · simpa only [l, ContinuousLinearMap.comp_apply,
          ContinuousLinearEquiv.coe_coe,
          ContinuousLinearEquiv.apply_symm_apply, innerSL_apply_apply, hheight] using hx.2
      · simpa only [l, ContinuousLinearMap.comp_apply,
          ContinuousLinearEquiv.coe_coe,
          ContinuousLinearEquiv.apply_symm_apply, innerSL_apply_apply, hheight] using hstrict j hji

end VolumePolynomials.PolytopeGeometry
