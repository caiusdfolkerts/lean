module

public import ToricPower.ArrangementAffineMorseCoefficients
public import ToricPower.ArrangementMorseComplexIsoTransport

/-! # A sealed actual affine coefficient model

The affine tilde equivalence and complete intrinsic label-Hom functor
are typed on the literal toric affine chart before evaluating any
coefficient. This records their whole functor identity without changing
the underlying sheaves or coefficient maps.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open TauCeti.Toric ToricPower.IntegralArrangement

attribute [local instance 2000] CommRing.toRing
attribute [local instance 2100] Complex.instRing
attribute [local instance 2000] Ring.toAddCommGroup
attribute [local instance 2000] Ring.toSemiring
attribute [local instance 2000] Preadditive.preadditiveHasZeroMorphisms

namespace ToricPower

variable {N : Type} {V : Type*} [AddCommGroup N] [AddCommGroup V]
  [Module ℝ V] {i : N →+ V} (fan : Fan i)
  (nonempty : Nonempty fan.cones) (regular : fan.IsRegular)
  {n s : ℕ} (basis : Module.Basis (Fin n) ℤ (N →+ ℤ)) (rays : Fin s ≃ fan.Ray)
  (cone : fan.cones)

local instance actualAffineModelChart : IsAffineHom (fan.affineToricChartι cone) :=
  toricChartInclusion_isAffineHom fan cone

def universalAffineQuasicoherentDiagram :
    QCoh (fan.affineToricChart cone) ⥤
      UniversalIncidenceObject (fanArrangementMatrix fan basis rays) ⥤ ModuleCat ℂ :=
  quasicoherentOpenIntrinsicLabelHom ℂ (fan.affineToricChartι cone)
    (universalCartierQuasicoherentSources fan nonempty regular basis rays)

omit nonempty regular basis rays in
def toricChartTildeEquivalence :
    ModuleCat.{0} (affineCoordinateRing fan.lattice cone.val) ≌
      QCoh (fan.affineToricChart cone) :=
  tildeEquiv (R := CommRingCat.of (affineCoordinateRing fan.lattice cone.val))

theorem universalAffineCoefficientDiagram_chart_eq :
    universalAffineCoefficientDiagram fan nonempty regular basis rays cone =
      (toricChartTildeEquivalence fan cone).functor ⋙
        universalAffineQuasicoherentDiagram fan nonempty regular basis rays cone := rfl

theorem universalAffineQuasicoherentDiagram_eq :
    universalAffineQuasicoherentDiagram fan nonempty regular basis rays cone =
      quasicoherentAffinePushforward (fan.affineToricChartι cone) ⋙
        Cellular.homDiagram ℂ
          (universalCartierQuasicoherentSources fan nonempty regular basis rays) := rfl

end ToricPower

end

