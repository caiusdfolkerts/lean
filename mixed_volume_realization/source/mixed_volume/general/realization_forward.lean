module

public import mixed_volume.general.deficit_forcing

/-! The actual deficit body supplies the forward direction for the entire
homogeneous cubic.  Support identities are used only after they have been
proved from an equality of actual Minkowski sums. -/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace MixedVolume.GeneralRealization

open VolumePolynomials VolumePolynomials.Holonomy VolumePolynomials.BodySupport
open AutomatonWords AutomatonZonoids GeneralLabels GeneralTarget GeneralDeficit CanonicalGeometry
open Set MeasureTheory
open scoped BigOperators Pointwise

abbrev Plane := AutomatonWords.Plane
variable {s m : ℕ}

def withDeficit (A : Data s m) (hs : 0 < s) (D : ConvexBody Plane) : Label s m → Body 3
  | .inr (.inr (.inr _)) => mapBody embedXZ D
  | i => canonical A hs i

theorem support_deficit (A : Data s m) (hs : 0 < s) (p : Fin m → ℝ)
    (hp : ProbabilityRow p) (theta : ℝ) (htheta₀ : 0 < theta) (htheta₁ : theta < 1)
    (hcut : A.UniversalCutpoint p theta) (l : Space 3 →L[ℝ] ℝ) :
    support (mapBody embedXZ (deficitBody A hs p hp theta htheta₁ hcut)) l =
      ∑ j, targetDelta A p theta j * support (canonical A hs (stateLabel j)) l := by
  have h := congrArg (fun K : ConvexBody Plane => support K (l.comp embedXZ))
    (deficit_equation A hs p hp theta htheta₁ hcut)
  rw [initialBody_eq_combination,← stationary_scaled A hs theta,
    SeriesSupport.support_add,SeriesSupport.support_sum,SeriesSupport.support_sum] at h
  simp_rw [SeriesSupport.support_smul _ _ (hp.1 _),
    SeriesSupport.support_smul _ _ (stationaryWeights_nonneg A htheta₀ _)] at h
  simp only [canonical_state,SeriesSupport.support_map,targetDelta,
    sub_mul,Finset.sum_sub_distrib]
  exact eq_sub_of_add_eq h

theorem weighted_support_shift (δ : Fin m → ℝ) (w F : Label s m → ℝ) :
    (∑ i, shiftWeight δ w i * F i) =
      (∑ i, w i * F i) + w deficitLabel * ∑ j, δ j * F (stateLabel j) := by
  simp only [Fintype.sum_sum_type,Fintype.sum_prod_type,Fintype.sum_unique,
    shiftWeight,stateLabel,add_mul,Finset.sum_add_distrib,Finset.mul_sum,deficitLabel]
  have h : (∑ j, δ j * w (Sum.inr (Sum.inr (Sum.inr ()))) * F (Sum.inr (Sum.inl j))) =
      ∑ j, w (Sum.inr (Sum.inr (Sum.inr ()))) * (δ j * F (Sum.inr (Sum.inl j))) := by
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [h]
  ring

theorem weighted_support_replace (A : Data s m) (hs : 0 < s) (D : ConvexBody Plane)
    (w : Label s m → ℝ) (l : Space 3 →L[ℝ] ℝ) :
    (∑ i, w i * support (withDeficit A hs D i) l) =
      (∑ i, w i * support (canonical A hs i) l) + w deficitLabel * support (mapBody embedXZ D) l := by
  simp only [Fintype.sum_sum_type,Fintype.sum_prod_type,Fintype.sum_unique,
    withDeficit,canonical,SeriesSupport.support_zero,mul_zero,add_zero,deficitLabel]
  ring

theorem cutpoint_realizes_target (A : Data s m) (hs : 0 < s) (p : Fin m → ℝ)
    (hp : ProbabilityRow p) (theta : ℝ) (htheta₀ : 0 < theta) (htheta₁ : theta < 1)
    (hcut : A.UniversalCutpoint p theta) :
    RealizesTarget A hs (targetDelta A p theta)
      (withDeficit A hs (deficitBody A hs p hp theta htheta₁ hcut)) := by
  apply (realizesTarget_iff_safe _ _ _ _).mpr
  intro w hw hshift
  congr 1
  apply SeriesSupport.ext
  intro l
  rw [sumBody,sumBody,SeriesSupport.support_sum,SeriesSupport.support_sum]
  simp_rw [SeriesSupport.support_smul _ _ (hw _),SeriesSupport.support_smul _ _ (hshift _)]
  rw [weighted_support_replace,weighted_support_shift,support_deficit A hs p hp theta htheta₀ htheta₁ hcut]

theorem realization_iff_cutpoint (A : Data s m) (hs : 0 < s) (p : Fin m → ℝ)
    (hp : ProbabilityRow p) (theta : ℝ) (htheta₀ : 0 < theta) (htheta₁ : theta < 1) :
    (∃ K : Label s m → Body 3, RealizesTarget A hs (targetDelta A p theta) K) ↔
      A.UniversalCutpoint p theta := by
  constructor
  · rintro ⟨K,hK⟩
    exact realization_implies_cutpoint A hs p hp theta htheta₀ htheta₁ hK
  · intro hcut
    exact ⟨_,cutpoint_realizes_target A hs p hp theta htheta₀ htheta₁ hcut⟩

end MixedVolume.GeneralRealization

end
