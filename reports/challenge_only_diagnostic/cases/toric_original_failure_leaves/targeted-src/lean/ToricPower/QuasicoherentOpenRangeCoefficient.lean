module

public import ToricPower.QuasicoherentPushforwardComposition

/-! # Coefficients transported from a chart to its actual image open -/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

namespace ToricPower

universe u v w

variable {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
  [IsAffineHom j] [IsAffineHom j.opensRange.ι]
  {D : Type v} [Category.{w} D]

def quasicoherentOpenRangeCoefficient (G : QCoh U ⥤ D) : QCoh j.opensRange.toScheme ⥤ D :=
  quasicoherentAffinePushforward j.isoOpensRange.inv ⋙ G

/-- A property of every genuine chart coefficient survives transport
to the chart's image open. The large coefficient functor is kept abstract. -/
theorem quasicoherentOpenRangeCoefficient_property (G : QCoh U ⥤ D)
    (P : D → Prop) (every : ∀ M, P (G.obj M))
    (M : QCoh j.opensRange.toScheme) :
    P ((quasicoherentOpenRangeCoefficient j G).obj M) :=
  every ((quasicoherentAffinePushforward j.isoOpensRange.inv).obj M)

/-- Whole-functor equality transports the property without expanding
the geometric coefficient functor at a particular module. -/
theorem quasicoherentOpenRangeCoefficient_property_of_eq (G : QCoh U ⥤ D)
    (K : QCoh j.opensRange.toScheme ⥤ D)
    (same : K = quasicoherentOpenRangeCoefficient j G)
    (P : D → Prop) (every : ∀ M, P (G.obj M))
    (M : QCoh j.opensRange.toScheme) : P (K.obj M) := by
  subst K
  exact quasicoherentOpenRangeCoefficient_property j G P every M

def quasicoherentOpenRangeCoefficientIso (G : QCoh U ⥤ D) (H : QCoh X ⥤ D)
    (comparison : G ≅ quasicoherentAffinePushforward j ⋙ H) :
    quasicoherentOpenRangeCoefficient j G ≅ quasicoherentAffinePushforward j.opensRange.ι ⋙ H :=
  Functor.isoWhiskerLeft (quasicoherentAffinePushforward j.isoOpensRange.inv) comparison ≪≫
    Functor.isoWhiskerRight
      (quasicoherentPushforwardCompIso j.isoOpensRange.inv j ≪≫
        quasicoherentPushforwardCongrIso (Scheme.Hom.isoOpensRange_inv_comp j)) H

end ToricPower

end
