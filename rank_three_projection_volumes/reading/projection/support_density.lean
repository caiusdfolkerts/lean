module

public import Projection.SupportFunctions
public import Projection.PositiveRepresentation
public import Mathlib.Analysis.Convex.Join
public import Mathlib.Topology.ContinuousMap.StoneWeierstrass
public import Mathlib.MeasureTheory.Integral.BoundedContinuousFunction
public import Mathlib.MeasureTheory.Measure.FiniteMeasure

@[expose] public section
set_option autoImplicit false
noncomputable section

open Set Metric MeasureTheory
open scoped Pointwise NNReal Topology

namespace RankThreeProjection
open VolumePolynomials

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

private theorem convexJoin_eq_image (A B : ConvexBody E) :
    convexJoin ℝ (A : Set E) (B : Set E) =
      (fun p : ℝ × E × E => (1 - p.1) • p.2.1 + p.1 • p.2.2) ''
        (Icc (0 : ℝ) 1 ×ˢ ((A : Set E) ×ˢ (B : Set E))) := by
  ext z
  constructor
  · intro hz
    obtain ⟨a, ha, b, hb, hz⟩ := mem_convexJoin.mp hz
    rw [segment_eq_image] at hz
    obtain ⟨t, ht, rfl⟩ := hz
    exact ⟨(t, a, b), ⟨ht, ha, hb⟩, rfl⟩
  · rintro ⟨⟨t, a, b⟩, ⟨ht, ha, hb⟩, rfl⟩
    apply mem_convexJoin.mpr
    refine ⟨a, ha, b, hb, ?_⟩
    rw [segment_eq_image]
    exact ⟨t, ht, rfl⟩

/-- The convex hull of the union of two actual compact convex bodies. -/
def joinBody (A B : ConvexBody E) : ConvexBody E where
  carrier := convexJoin ℝ (A : Set E) (B : Set E)
  convex' := A.convex.convexJoin B.convex
  isCompact' := by
    rw [convexJoin_eq_image]
    exact (isCompact_Icc.prod (A.isCompact.prod B.isCompact)).image (by fun_prop)
  nonempty' := A.nonempty.mono (subset_convexJoin_left B.nonempty)

theorem supportContinuous_join (A B : ConvexBody E) :
    supportContinuous (joinBody A B) = supportContinuous A ⊔ supportContinuous B := by
  ext u
  change BodySupport.support (joinBody A B) u.val =
    max (BodySupport.support A u.val) (BodySupport.support B u.val)
  apply le_antisymm
  · apply BodySupport.support_le
    intro z hz
    obtain ⟨a, ha, b, hb, r, t, hr, ht, hrt, rfl⟩ := mem_convexJoin.mp hz
    rw [map_add, map_smul, map_smul]
    change r * u.val a + t * u.val b ≤ _
    have ha' := (BodySupport.le_support A u.val ha).trans
      (le_max_left (BodySupport.support A u.val) (BodySupport.support B u.val))
    have hb' := (BodySupport.le_support B u.val hb).trans
      (le_max_right (BodySupport.support A u.val) (BodySupport.support B u.val))
    calc
      _ ≤ r * max (BodySupport.support A u.val) (BodySupport.support B u.val) +
          t * max (BodySupport.support A u.val) (BodySupport.support B u.val) :=
        add_le_add (mul_le_mul_of_nonneg_left ha' hr) (mul_le_mul_of_nonneg_left hb' ht)
      _ = _ := by rw [← add_mul, hrt, one_mul]
  · apply max_le
    · exact supportContinuous_mono (subset_convexJoin_left B.nonempty) u
    · exact supportContinuous_mono (subset_convexJoin_right A.nonempty) u

@[simp] theorem supportContinuous_point (v : E) (u : NormalSphere E) :
    supportContinuous (pointBody v) u = u.val v := by
  apply le_antisymm
  · apply BodySupport.support_le
    intro x hx
    have hx' : x = v := hx
    simp [hx']
  · exact BodySupport.le_support (pointBody v) u.val (show v ∈ pointBody v from rfl)

variable [FiniteDimensional ℝ E]

abbrev SupportSpace := PositiveRepresentation.differenceSpace (supportLinear (E := E))

private theorem max_difference (a b c d : ℝ) :
    max (a - b) (c - d) = max (a + d) (c + b) - (b + d) := by
  rcases le_total (a - b) (c - d) with h | h
  · rw [max_eq_right h, max_eq_right (by linarith : a + d ≤ c + b)]
    ring
  · rw [max_eq_left h, max_eq_left (by linarith : c + b ≤ a + d)]
    ring

theorem supportSpace_sup {f g : C(NormalSphere E, ℝ)}
    (hf : f ∈ SupportSpace (E := E)) (hg : g ∈ SupportSpace (E := E)) :
    f ⊔ g ∈ SupportSpace (E := E) := by
  obtain ⟨a, b, rfl⟩ := hf
  obtain ⟨c, d, rfl⟩ := hg
  refine ⟨joinBody (a + d) (c + b), b + d, ?_⟩
  change (supportContinuous a - supportContinuous b) ⊔
      (supportContinuous c - supportContinuous d) =
    supportContinuous (joinBody (a + d) (c + b)) - supportContinuous (b + d)
  simp only [supportContinuous_join, supportContinuous_add]
  ext u
  simp only [ContinuousMap.sub_apply, ContinuousMap.add_apply, ContinuousMap.sup_apply]
  exact max_difference _ _ _ _

theorem supportSpace_inf {f g : C(NormalSphere E, ℝ)}
    (hf : f ∈ SupportSpace (E := E)) (hg : g ∈ SupportSpace (E := E)) :
    f ⊓ g ∈ SupportSpace (E := E) := by
  have hs := supportSpace_sup ((SupportSpace (E := E)).neg_mem hf)
    ((SupportSpace (E := E)).neg_mem hg)
  have hn := (SupportSpace (E := E)).neg_mem hs
  simpa only [neg_sup, neg_neg] using hn

theorem one_mem_supportSpace : (1 : C(NormalSphere E, ℝ)) ∈ SupportSpace (E := E) :=
  ⟨unitBall, 0, by simp [supportLinear, supportContinuous_unitBall]⟩

private theorem supportSpace_strongly_separates :
    (SupportSpace (E := E) : Set C(NormalSphere E, ℝ)).SeparatesPointsStrongly := by
  intro v x y
  by_cases hxy : x = y
  · subst y
    refine ⟨v x • (1 : C(NormalSphere E, ℝ)),
      (SupportSpace (E := E)).smul_mem (v x) one_mem_supportSpace, ?_, ?_⟩ <;> simp
  · have hvals : x.val ≠ y.val := fun h => hxy (Subtype.ext h)
    obtain ⟨z, hz⟩ : ∃ z : E, x.val z ≠ y.val z := by
      by_contra hn
      push_neg at hn
      exact hvals (ContinuousLinearMap.ext hn)
    let f := supportContinuous (pointBody z)
    have hf : f ∈ SupportSpace (E := E) := ⟨pointBody z, 0, by simp [f, supportLinear]⟩
    have hdiff : f x - f y ≠ 0 := by
      simpa only [f, supportContinuous_point] using sub_ne_zero.mpr hz
    let c := (v y - v x) * (f x - f y)⁻¹
    let g : C(NormalSphere E, ℝ) := c • (f x • 1 - f) + v x • 1
    have hg : g ∈ SupportSpace (E := E) :=
      (SupportSpace (E := E)).add_mem
        ((SupportSpace (E := E)).smul_mem c
          ((SupportSpace (E := E)).sub_mem
            ((SupportSpace (E := E)).smul_mem (f x) one_mem_supportSpace) hf))
        ((SupportSpace (E := E)).smul_mem (v x) one_mem_supportSpace)
    refine ⟨g, hg, ?_, ?_⟩
    · simp [g]
    · simp [g, c, mul_assoc, inv_mul_cancel₀ hdiff]

/-- Differences of genuine support functions are uniformly dense among
continuous functions on the normal sphere. Smoothness is unnecessary here. -/
theorem dense_support_differences :
    Dense (PositiveRepresentation.differenceSpace (supportLinear (E := E)) :
      Set C(NormalSphere E, ℝ)) := by
  rw [dense_iff_closure_eq]
  exact ContinuousMap.sublattice_closure_eq_top _ ⟨0, (SupportSpace (E := E)).zero_mem⟩
    (fun _ hf _ hg => supportSpace_inf hf hg)
    (fun _ hf _ hg => supportSpace_sup hf hg) supportSpace_strongly_separates

section Measures
variable [MeasurableSpace (NormalSphere E)] [BorelSpace (NormalSphere E)]

/-- Integration on a compact space as a bounded linear functional. -/
def continuousIntegral (μ : Measure (NormalSphere E)) [IsFiniteMeasure μ] :
    C(NormalSphere E, ℝ) →L[ℝ] ℝ :=
  ({ toFun := fun f => ∫ x, f x ∂μ
     map_add' := by
       intro f g
       exact integral_add ((BoundedContinuousFunction.mkOfCompact f).integrable μ)
         ((BoundedContinuousFunction.mkOfCompact g).integrable μ)
     map_smul' := by
       intro r f
       exact integral_smul r f } : C(NormalSphere E, ℝ) →ₗ[ℝ] ℝ).mkContinuous
    (μ.real univ) (fun f => (BoundedContinuousFunction.mkOfCompact f).norm_integral_le_mul_norm μ)

/-- A finite Borel measure is determined by its integrals against actual
support functions, rather than by a stipulated uniqueness field. -/
theorem measure_eq_of_support_integrals
    (μ ν : Measure (NormalSphere E)) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (h : ∀ A : ConvexBody E,
      (∫ u, supportContinuous A u ∂μ) = ∫ u, supportContinuous A u ∂ν) : μ = ν := by
  have hclosed : IsClosed {f : C(NormalSphere E, ℝ) |
      continuousIntegral μ f = continuousIntegral ν f} :=
    isClosed_eq (continuousIntegral μ).continuous (continuousIntegral ν).continuous
  have hsub : (PositiveRepresentation.differenceSpace (supportLinear (E := E)) :
      Set C(NormalSphere E, ℝ)) ⊆ {f | continuousIntegral μ f = continuousIntegral ν f} := by
    rintro f ⟨A, B, rfl⟩
    change (∫ u, supportContinuous A u - supportContinuous B u ∂μ) =
      ∫ u, supportContinuous A u - supportContinuous B u ∂ν
    calc
      _ = (∫ u, supportContinuous A u ∂μ) - ∫ u, supportContinuous B u ∂μ :=
        integral_sub ((BoundedContinuousFunction.mkOfCompact (supportContinuous A)).integrable μ)
          ((BoundedContinuousFunction.mkOfCompact (supportContinuous B)).integrable μ)
      _ = (∫ u, supportContinuous A u ∂ν) - ∫ u, supportContinuous B u ∂ν :=
        congrArg₂ (· - ·) (h A) (h B)
      _ = _ :=
        (integral_sub ((BoundedContinuousFunction.mkOfCompact (supportContinuous A)).integrable ν)
          ((BoundedContinuousFunction.mkOfCompact (supportContinuous B)).integrable ν)).symm
  have hall : ∀ f : C(NormalSphere E, ℝ),
      continuousIntegral μ f = continuousIntegral ν f := by
    intro f
    exact closure_minimal hsub hclosed (dense_support_differences f)
  have heq : (⟨μ, inferInstance⟩ : FiniteMeasure (NormalSphere E)) = ⟨ν, inferInstance⟩ := by
    apply FiniteMeasure.ext_of_forall_integral_eq
    intro f
    exact hall f.toContinuousMap
  exact congrArg Subtype.val heq

end Measures
end RankThreeProjection
