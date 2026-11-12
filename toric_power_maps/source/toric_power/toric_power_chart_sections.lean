module

public import ToricPower.CechMeetInjectiveAssembly
public import ToricPower.FixedChartBaseSections
public import ToricPower.ToricCohomologyBound
public import ToricPower.DivisorWeightRationalPushforward

/-! # The actual section diagram is invariant under a positive toric power -/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory TauCeti.Toric

namespace ToricPower

variable {N : Type} {V : Type*} [AddCommGroup N] [AddCommGroup V]
  [Module ℝ V] {i : N →+ V} (fan : Fan i)

instance toricPowerMap_isOverComplex (ell : ℕ) :
    (toricPowerMap fan ell).IsOver (Spec (.of ℂ)) := by
  unfold toricPowerMap
  infer_instance

/-- The canonical comparison respects all chart arrows and all coefficients. -/
def toricPowerChartSectionsIso (regular : fan.IsRegular) (ell : ℕ) (positive : 0 < ell) :
    letI := toricPowerMap_finite fan regular ell positive
    quasicoherentAffinePushforward (toricPowerMap fan ell) ⋙
      FiniteCech.quasicoherentMeetSections ℂ fan.algebraicRealization
        (toricMeetChartOpenFunctor fan) ≅
    FiniteCech.quasicoherentMeetSections ℂ fan.algebraicRealization
      (toricMeetChartOpenFunctor fan) := by
  letI := toricPowerMap_finite fan regular ell positive
  exact quasicoherentFixedChartSectionsIso ℂ fan.algebraicRealization
    (toricPowerMap fan ell) (toricMeetChartOpenFunctor fan).op
    (fun b => toricPower_preimage_chartOpen fan ell positive (toricMeetChartEquiv fan b.unop))

end ToricPower

end
