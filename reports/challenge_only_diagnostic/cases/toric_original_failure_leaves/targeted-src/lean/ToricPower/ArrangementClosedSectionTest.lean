module

public import ToricPower.ArrangementClosedDerivedTest
public import ToricPower.QuasicoherentDerivedChainCohomology
public import ToricPower.ToricCohomologyBound

/-!
# The normalized closed-row test from the original chart-chain augmentation

This is the final derived adapter for the closed-subtorus calculation.
Its input is a quasi-isomorphism of the whole actual affine chart-section
chain diagram, together with nonzero ordinary cohomology of its actual
quasicoherent target. The entire derived-global and adjunction comparison
is proved here from the original cellular source.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TauCeti.Toric
open ToricPower.IntegralArrangement

namespace ToricPower

variable {N : Type} {V : Type*} [AddCommGroup N] [AddCommGroup V]
  [Module ℝ V] {i : N →+ V} (fan : Fan i) [nonempty : Nonempty fan.cones]
  (regular : fan.IsRegular) {n s : ℕ}
  (basis : Module.Basis (Fin n) ℤ (N →+ ℤ)) (rays : Fin s ≃ fan.Ray)

local notation "X" => fan.algebraicRealization
local notation "B" => ToricMeetChartIndex fan
local notation "S" => FiniteCech.quasicoherentMeetSections ℂ X (toricMeetChartOpenFunctor fan)

attribute [local instance] closedDerivedIntegral closedDerivedNoetherian closedDerivedSeparated
  closedDerivedBiproducts closedDerivedQCoh closedDerivedScalar closedDerivedAdditive
  closedDerivedDegreeLimits closedDerivedDegreeColimits

local instance closedSectionTestDerivedCharts :
    HasDerivedCategory.{1} (Bᵒᵖ ⥤ ModuleCat.{0} ℂ) := HasDerivedCategory.standard _

/-- Every original coefficient and chart restriction is retained in the
augmentation input. A genuine quasi-isomorphism and actual target
cohomology give the exact scalar test used in the generation theorem. -/
theorem normalizedClosedRowsTest_of_sectionAugmentation
    (b : fan.Ray → ℤ) (selected : Set (Fin s ⊕ Fin n)) (T : QCoh X)
    (augmentation : ((S).mapHomologicalComplex (.down ℕ)).obj
      ((arrangementClosedDualFunctor fan regular basis rays selected).obj
        (arrangementCartierCoefficient fan regular b)) ⟶
      (ChainComplex.single₀ (Bᵒᵖ ⥤ ModuleCat.{0} ℂ)).obj ((S).obj T))
    [QuasiIso augmentation]
    (cohomology : ∃ p : ℕ,
      Nontrivial (TauCeti.AlgebraicGeometry.Scheme.Modules.Cohomology T.obj p)) :
    NormalizedClosedRowsTest fan regular basis rays b selected := by
  let K := (arrangementClosedDualFunctor fan regular basis rays selected).obj
    (arrangementCartierCoefficient fan regular b)
  let C := arrangementClosedDualChainPlus fan regular basis rays selected
    (arrangementCartierCoefficient fan regular b)
  let sourceIso : C.obj ≅ K.extend ComplexShape.embeddingDownNat :=
    eqToIso (show C.obj = K.extend ComplexShape.embeddingDownNat from rfl)
  obtain ⟨p, nonzero⟩ := cohomology
  exact normalizedClosedRowsTest_of_dualCohomology fan regular basis rays b selected p
    (quasicoherentDerivedSectionsCohomologyOfChainAugmentation_nonzero ℂ X
      (toricMeetChartOpenFunctor fan)
      (fun a b => map_inf (toricMeetChartOpenHom fan) a b)
      (toricMeetChartOpen_covers fan) (toricMeetChartOpen_tupleMeet fan)
      (fun a => isAffineOpen_opensRange (fan.affineToricChartι (toricMeetChartEquiv fan a)))
      K C sourceIso T augmentation p nonzero)

end ToricPower
end
