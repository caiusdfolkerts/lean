module

public import ToricPower.ArrangementUniversalCartierSources
public import ToricPower.AffineRankOneSections
public import ToricPower.AffineInvertibleHomColimits
public import ToricPower.ToricAffineLabelHomExact
public import ToricPower.ArrangementThetaFanMorse
public import ToricPower.ArrangementMorseRankOneComparison

/-! # Actual affine coefficients in the universal local Morse calculation

The coefficient functor is the genuine affine tilde equivalence,
followed by the genuine open direct image and the complete Cartier Hom
diagram. Its rank-one value is identified with the unrestricted theta
diagram through the original projection formula. Exactness and
unrestricted coproduct preservation then extend the local calculation
to every module on the affine chart.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite
open TauCeti.Toric ToricPower.IntegralArrangement

attribute [local instance 2000] CommRing.toRing
attribute [local instance 2100] Complex.instRing
attribute [local instance 2000] Ring.toAddCommGroup
attribute [local instance 2000] Ring.toSemiring

namespace ToricPower

variable {N : Type} {V : Type*} [AddCommGroup N] [AddCommGroup V]
  [Module ℝ V] {i : N →+ V} (fan : Fan i)
  (nonempty : Nonempty fan.cones) (regular : fan.IsRegular)
  {n s : ℕ} (basis : Module.Basis (Fin n) ℤ (N →+ ℤ)) (rays : Fin s ≃ fan.Ray)
  (cone : fan.cones)

local notation "A" => fanArrangementMatrix fan basis rays
local notation "Cells" => UniversalIncidenceObject A
local notation "X" => fan.algebraicRealization
local notation "j" => fan.affineToricChartι cone
local notation "ChartRing" => affineCoordinateRing fan.lattice cone.val

local instance affineMorseChart_isAffineHom : IsAffineHom j := toricChartInclusion_isAffineHom fan cone

omit cone in
theorem universalCartierQuasicoherentSources_invertible (c : Cells) :
    TauCeti.AlgebraicGeometry.SheafOfModules.isInvertible X
      ((universalCartierQuasicoherentSources fan nonempty regular basis rays).obj (op c)).obj := by
  letI := toricSchemeIntegral fan nonempty
  change TauCeti.AlgebraicGeometry.SheafOfModules.isInvertible X
    (invariantCartierDivisor fan nonempty regular
      (-universalDualCoefficients fan basis rays c)).sheaf
  exact TauCeti.AlgebraicGeometry.Scheme.CartierDivisor.isInvertible_sheaf _

omit cone in
theorem universalDualCartierDiagram_invertible (c : Cells) :
    TauCeti.AlgebraicGeometry.SheafOfModules.isInvertible X
      ((universalDualCoefficientDiagram fan basis rays ⋙
        ToricMonomial.realization fan nonempty regular).obj c) := by
  letI := toricSchemeIntegral fan nonempty
  change TauCeti.AlgebraicGeometry.SheafOfModules.isInvertible X
    (invariantCartierDivisor fan nonempty regular
      (universalDualCoefficients fan basis rays c)).sheaf
  exact TauCeti.AlgebraicGeometry.Scheme.CartierDivisor.isInvertible_sheaf _

/-- The full actual rank-one Hom diagram is the full affine theta
diagram, naturally in every universal face arrow. -/
def universalAffineUnitHomThetaIso :
    (Cellular.homDiagram ℂ
      (universalCartierQuasicoherentSources fan nonempty regular basis rays)).obj
        (quasicoherentAffineUnitImage (U := Spec (CommRingCat.of ChartRing)) j) ≅
      universalCartierChartSections fan basis rays cone regular := by
  letI := toricSchemeIntegral fan nonempty
  exact quasicoherentHomOpenUnitSectionsIso ℂ (U := Spec (CommRingCat.of ChartRing)) j
    (universalDualQuasicoherentDiagram fan basis rays nonempty regular)
    (universalDualCartierDiagram_invertible fan nonempty regular basis rays)
    (Cellular.homDiagram ℂ
      (universalCartierQuasicoherentSources fan nonempty regular basis rays))
    (universalCartierHomSectionsIso fan nonempty regular basis rays)

/-- Arbitrary actual modules on the chosen toric affine chart, with
their genuine universal Cartier Hom diagram. -/
def universalAffineCoefficientDiagram : ModuleCat.{0} ChartRing ⥤ Cells ⥤ ModuleCat ℂ :=
  (tildeEquiv (R := CommRingCat.of ChartRing)).functor ⋙
    quasicoherentOpenIntrinsicLabelHom ℂ j
      (universalCartierQuasicoherentSources fan nonempty regular basis rays)

instance universalAffineCoefficientDiagram_additive :
    (universalAffineCoefficientDiagram fan nonempty regular basis rays cone).Additive := by
  unfold universalAffineCoefficientDiagram
  letI := (tildeEquiv (R := CommRingCat.of ChartRing)).functor.additive_of_preserves_binary_products
  infer_instance

theorem universalAffineCoefficientDiagram_exact :
    PreservesFiniteLimits
        (universalAffineCoefficientDiagram fan nonempty regular basis rays cone) ∧
      PreservesFiniteColimits
        (universalAffineCoefficientDiagram fan nonempty regular basis rays cone) := by
  letI := (quasicoherentOpenIntrinsicLabelHom_exact ℂ j
    (universalCartierQuasicoherentSources fan nonempty regular basis rays)
    (universalCartierQuasicoherentSources_invertible fan nonempty regular basis rays)).2
  unfold universalAffineCoefficientDiagram
  exact ⟨inferInstance,inferInstance⟩

theorem universalAffineCoefficientDiagram_preservesColimits :
    PreservesColimitsOfSize.{0,0}
      (universalAffineCoefficientDiagram fan nonempty regular basis rays cone) := by
  letI := toricSchemeIntegral fan nonempty
  letI := quasicoherentOpenIntrinsicLabelHom_preservesColimits ℂ X
    (universalCartierQuasicoherentSources fan nonempty regular basis rays) j
    (universalCartierQuasicoherentSources_invertible fan nonempty regular basis rays)
  unfold universalAffineCoefficientDiagram
  infer_instance

/-- The actual affine tilde equivalence sends the free rank-one module
to the unit sheaf; no presentation or chosen trivialization is assumed. -/
theorem universalAffineCoefficientDiagram_eq :
    universalAffineCoefficientDiagram fan nonempty regular basis rays cone =
      (tildeEquiv (R := CommRingCat.of ChartRing)).functor ⋙
        quasicoherentAffinePushforward j ⋙
          Cellular.homDiagram ℂ
            (universalCartierQuasicoherentSources fan nonempty regular basis rays) := rfl

/-- Evaluate the already identified whole coefficient functor before
composing the tilde-unit and theta comparisons. -/
def universalAffineRankOneThetaIso :
    (universalAffineCoefficientDiagram fan nonempty regular basis rays cone).obj
      (ModuleCat.of ChartRing ChartRing) ≅ universalCartierChartSections fan basis rays cone regular :=
  quasicoherentAffineRankOneComparison ChartRing j
    (Cellular.homDiagram ℂ (universalCartierQuasicoherentSources fan nonempty regular basis rays))
    (universalAffineCoefficientDiagram fan nonempty regular basis rays cone)
    (universalAffineCoefficientDiagram_eq fan nonempty regular basis rays cone)
    (universalCartierChartSections fan basis rays cone regular)
    (universalAffineUnitHomThetaIso fan nonempty regular basis rays cone)

end ToricPower

end
