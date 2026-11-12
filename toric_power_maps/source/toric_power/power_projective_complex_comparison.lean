module

public import ToricPower.ArrangementPowerPostcompose
public import ToricPower.DiagramProjectiveCechDerived
public import ToricPower.LinearHomComplexExact

/-!
# Power comparison for an arbitrary projective coefficient model

The finite-sheet comparison commutes with the actual signed Hom
complex. Explicit composition isomorphisms keep the input coefficient
functor abstract; specializing this result does not normalize the
entire geometric construction of that functor.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor
open ToricPower.IntegralArrangement

namespace ToricPower

variable {n s : ℕ} (matrix : Fin s → Fin n → ℤ) (ell : ℕ) (positive : 0 < ell)
  (k : Type) [CommRing k]
  {Source : Type*} [Category.{0} Source] [Abelian Source]
  {Coefficients : Type*} [Category.{0} Coefficients] [Abelian Coefficients]
  [Linear k Coefficients] [HasCoproducts.{0} Coefficients] [AB4OfSize.{0} Coefficients]
  (S : Source ⥤ IncidenceObject matrix ⥤ Coefficients) [S.Additive]
  (T : Source ⥤ Source) [T.Additive]
  {Z : Coefficients} (P : ProjectiveResolution Z)

/-- The same given coefficient comparison on all unbounded complexes,
including its signs, differentials, and original incidence maps. -/
def powerProjectiveCoefficientComplexIso
    (comparison : S ⋙ powerDiagramPushdown matrix ell positive Coefficients ≅ T ⋙ S) :
    diagramProjectiveCoefficientComplexFunctor k S P ⋙
        (powerDiagramPushdown matrix ell positive (ModuleCat.{0} k)).mapHomologicalComplex (.up ℤ) ≅
      T.mapHomologicalComplex (.up ℤ) ⋙ diagramProjectiveCoefficientComplexFunctor k S P :=
  Functor.isoWhiskerLeft (S.mapHomologicalComplex (.up ℤ))
      (powerComplexFunctorIso matrix ell positive (.up ℤ)
        (linearHomComplexFunctor k (projectiveCochain P))).symm ≪≫
    Functor.isoWhiskerRight
      (Functor.mapHomologicalComplexCompIso comparison (.up ℤ) ≪≫
        (Functor.mapHomologicalComplexCompIso (Iso.refl (T ⋙ S)) (.up ℤ)).symm)
      (complexDiagramPostcompose (linearHomComplexFunctor k (projectiveCochain P)))

end ToricPower

end
