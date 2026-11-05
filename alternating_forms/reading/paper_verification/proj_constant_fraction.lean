module

public import PaperVerification.HomogeneousChartDehomogenization
public import TauCeti.AlgebraicGeometry.ProjectiveSpectrum.Basic

/-! # Degree-zero homogeneous fractions in actual chart sections -/

@[expose] public section
noncomputable section
set_option autoImplicit false

open AlgebraicGeometry

namespace PaperVerification.ProjConstantFraction

variable {A σ : Type*} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
  (𝒜 : ℕ → σ) [GradedRing 𝒜]

/-- A degree-zero homogeneous element gives its literal constant fraction.
The denominator equality is proved in the actual prime-complement submonoid. -/
theorem awayToSection_fraction_zero {f : A} (hf : f ∈ 𝒜 1) (a : 𝒜 0)
    (x : Proj.basicOpen 𝒜 f) :
    ((Proj.awayToSection 𝒜 f
      (HomogeneousChartDehomogenization.fraction 𝒜 hf 0 a)).1 x).val =
        Localization.mk (a : A) 1 := by
  rw [HomogeneousChartDehomogenization.fraction, Proj.val_awayToSection_mk_apply]
  apply congrArg (Localization.mk (a : A))
  apply Subtype.ext
  exact pow_zero f

end PaperVerification.ProjConstantFraction
