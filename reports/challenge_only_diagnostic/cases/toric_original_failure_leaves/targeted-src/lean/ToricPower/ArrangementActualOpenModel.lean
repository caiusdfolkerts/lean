module

public import ToricPower.ArrangementActualAffineModel
public import ToricPower.ToricDerivedAffineCover
public import ToricPower.QuasicoherentOpenRangeCoefficient

/-! # Named coefficient models on the genuine image-open charts

Transport through the actual affine-chart/image-open isomorphism is
performed at the full functor level. No coefficient or incidence map
is replaced, and arbitrary quasicoherent coefficients are admitted.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TauCeti.Toric
open ToricPower.IntegralArrangement

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

local instance actualOpenNamedChart (cone : fan.cones) :
    IsAffineHom (fan.affineToricChartι cone) := toricChartInclusion_isAffineHom fan cone

local instance actualOpenNamedRange (cone : fan.cones) :
    IsAffineHom (fan.affineToricChartι cone).opensRange.ι :=
  toricDerivedChartOpen_isAffineHom fan cone

def universalChartOpenCoefficientDiagram (cone : fan.cones) :
    QCoh (toricDerivedChartOpen fan cone).toScheme ⥤
      UniversalIncidenceObject (fanArrangementMatrix fan basis rays) ⥤ ModuleCat ℂ :=
  quasicoherentOpenRangeCoefficient (fan.affineToricChartι cone)
    (universalAffineQuasicoherentDiagram fan nonempty regular basis rays cone)

def toricChartOpenCoefficientTransport (cone : fan.cones) :
    QCoh (toricDerivedChartOpen fan cone).toScheme ⥤ QCoh (fan.affineToricChart cone) :=
  quasicoherentAffinePushforward (fan.affineToricChartι cone).isoOpensRange.inv

theorem universalChartOpenCoefficientDiagram_composite_eq (cone : fan.cones) :
    universalChartOpenCoefficientDiagram fan nonempty regular basis rays cone =
      toricChartOpenCoefficientTransport fan cone ⋙
        universalAffineQuasicoherentDiagram fan nonempty regular basis rays cone := rfl

theorem universalChartOpenCoefficientDiagram_eq (cone : fan.cones) :
    universalChartOpenCoefficientDiagram fan nonempty regular basis rays cone =
      quasicoherentOpenRangeCoefficient (fan.affineToricChartι cone)
        (universalAffineQuasicoherentDiagram fan nonempty regular basis rays cone) := rfl

def universalChartOpenCoefficientDiagramIso (cone : fan.cones) :
    universalChartOpenCoefficientDiagram fan nonempty regular basis rays cone ≅
      quasicoherentAffinePushforward (toricDerivedChartOpen fan cone).ι ⋙
        Cellular.homDiagram ℂ
          (universalCartierQuasicoherentSources fan nonempty regular basis rays) :=
  quasicoherentOpenRangeCoefficientIso (fan.affineToricChartι cone)
    (universalAffineQuasicoherentDiagram fan nonempty regular basis rays cone)
    (Cellular.homDiagram ℂ
      (universalCartierQuasicoherentSources fan nonempty regular basis rays))
    (eqToIso (universalAffineQuasicoherentDiagram_eq fan nonempty regular basis rays cone))


end ToricPower

end
