module

public import TauCeti.AlgebraicGeometry.ProjectiveSpectrum.TwistingSheaf.LocalTriviality
public import TauCeti.AlgebraicGeometry.ProjectiveSpectrum.Basic

/-!
# Homogeneous fractions and the actual twisting-sheaf frame

On the standard open of a degree-one element `f`, the section `r/f` of the
structure sheaf becomes the homogeneous section `r` of `𝒪(1)` under the
canonical frame. This comparison is between the existing sheaf constructions.
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
open AlgebraicGeometry CategoryTheory

namespace PaperVerification.TwistingChartFractions

variable {A : Type*} {σ : Type*} [CommRing A] [SetLike σ A]
  [AddSubgroupClass σ A] {𝒜 : ℕ → σ} [GradedRing 𝒜]

/-- Dividing by the pivot and then applying the genuine `𝒪(1)` chart frame
recovers the original homogeneous section. -/
theorem chart_frame_fraction {f : A} (hf : f ∈ 𝒜 1) (r : 𝒜 1) :
    Proj.twistingSheaf.chartSectionsLinearEquiv (𝒜:=𝒜) 1 f hf
      (Proj.basicOpen 𝒜 f) le_rfl
      (Proj.awayToSection 𝒜 f
        (HomogeneousLocalization.Away.mk 𝒜 hf 1 r (by simpa using r.property))) =
      Proj.toTwistingSheaf 𝒜 rfl (Proj.basicOpen 𝒜 f) r := by
  apply Proj.twistingSheaf.ext
  intro x
  rw [Proj.twistingSheaf.chartSectionsLinearEquiv_apply_apply,
    Proj.val_awayToSection_mk_apply,
    Proj.twistingSheaf.chartGenerator_apply,
    Proj.toTwistingSheaf_apply_apply]
  rw [Localization.mk_mul]
  apply Localization.mk_eq_mk_iff.mpr
  apply Localization.r_of_eq
  simp [mul_comm]

end PaperVerification.TwistingChartFractions
