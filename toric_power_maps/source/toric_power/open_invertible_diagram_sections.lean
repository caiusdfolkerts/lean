module

public import ToricPower.SchemeProjectionNaturality
public import ToricPower.SchemeRestrictionBaseSections

/-! # Actual affine-unit coefficients for invertible source diagrams

The projection formula is an isomorphism for every invertible label.
Its proved source naturality identifies the entire global tensor-section
diagram with sections of those same labels on the actual open image.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory

namespace ToricPower

universe u

variable {U X : Scheme.{u}} (j : U ⟶ X)
  {C : Type u} [Category.{u} C] (P : C ⥤ X.Modules)
  (invertible : ∀ c, TauCeti.AlgebraicGeometry.SheafOfModules.isInvertible X (P.obj c))

/-- The full diagram comparison is the original projection map at every label. -/
def schemeProjectionInvertibleDiagramIso :
    P ⋙ tensorRight ((Scheme.Modules.pushforward j).obj (SheafOfModules.unit U.ringCatSheaf)) ≅
      P ⋙ Scheme.Modules.pullback j ⋙ Scheme.Modules.pushforward j :=
  NatIso.ofComponents (fun c => by
    letI := invertible c
    letI := BondalThomsen.schemeProjectionFormulaMap_isIso_of_isInvertible j (P.obj c)
    exact asIso (BondalThomsen.schemeProjectionFormulaMap j (P.obj c)))
    (fun f => schemeProjectionFormulaMap_natural j (P.map f))

variable (k : Type u) [Field k]
  [U.Over (Spec (.of k))] [X.Over (Spec (.of k))]
  [IsOpenImmersion j] [j.IsOver (Spec (.of k))]

/-- This is a scalar-linear natural isomorphism of whole diagrams,
with every actual label morphism and every lattice character retained. -/
def openInvertibleDiagramUnitSectionsIso :
    P ⋙ tensorRight ((Scheme.Modules.pushforward j).obj (SheafOfModules.unit U.ringCatSheaf)) ⋙
        FiniteCover.schemeBaseSections k X ⊤ ≅
      P ⋙ FiniteCover.schemeBaseSections k X j.opensRange :=
  Functor.isoWhiskerRight (schemeProjectionInvertibleDiagramIso j P invertible)
      (FiniteCover.schemeBaseSections k X ⊤) ≪≫
    Functor.isoWhiskerLeft (P ⋙ Scheme.Modules.pullback j)
      (pushforwardGlobalBaseSectionsIso k j) ≪≫
    Functor.isoWhiskerLeft P (pullbackGlobalBaseSectionsIso k j)

end ToricPower

end
