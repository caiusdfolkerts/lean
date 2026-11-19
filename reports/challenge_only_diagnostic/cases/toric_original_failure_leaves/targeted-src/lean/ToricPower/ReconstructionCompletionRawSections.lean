module

public import ToricPower.ArrangementCellularAffineSections
public import ToricPower.SchemeRestrictionBaseSections

/-! # Sections on the literal affine chart

These detectors use pullback to the chart spectrum. Their comparison
with the genuine image-open sections preserves the original functor.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TauCeti.Toric

namespace ToricPower

variable {N : Type} {V : Type*} [AddCommGroup N] [AddCommGroup V]
  [Module ℝ V] {i : N →+ V} (fan : Fan i)

/-- Sections on the literal pulled-back affine chart. -/
abbrev reconstructionRawSectionFunctor (σ : fan.cones) :
    QCoh fan.algebraicRealization ⥤ ModuleCat ℂ :=
  quasicoherentInclusion fan.algebraicRealization ⋙
    Scheme.Modules.pullback (fan.affineToricChartι σ) ⋙
      FiniteCover.schemeBaseSections ℂ (fan.affineToricChart σ) ⊤

/-- These are the same actual affine sections as the image-open detector. -/
def reconstructionRawSectionIso (σ : fan.cones) :
    reconstructionRawSectionFunctor fan σ ≅ arrangementAffineSectionFunctor fan σ :=
  Functor.isoWhiskerLeft (quasicoherentInclusion fan.algebraicRealization)
    (pullbackGlobalBaseSectionsIso ℂ (fan.affineToricChartι σ))

instance reconstructionRawSectionFunctor_preservesColimits (σ : fan.cones) :
    PreservesColimitsOfSize.{0,0} (reconstructionRawSectionFunctor fan σ) :=
  preservesColimits_of_natIso (reconstructionRawSectionIso fan σ).symm

end ToricPower

end
