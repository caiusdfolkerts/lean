module

public import ToricPower.ArrangementMorseMappedComposition

/-! # A functorial shifted Hom model and its literal universal pullback

The construction and its Morse transport are checked with abstract
coefficient labels and an abstract resolution functor. The geometric
model is then an exact specialization, retaining all original maps.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

attribute [local instance 2000] Abelian.toPreadditive
attribute [local instance 2000] Preadditive.preadditiveHasZeroMorphisms

namespace ToricPower

variable {C : Type*} [Category.{0} C] [Preadditive C] [Linear ℂ C]
  {J U : Type} [Category.{0} J] [Category.{0} U]
  (P : Jᵒᵖ ⥤ C)

/-- Actual Hom applied to every degree of a specified complex replacement. -/
def homDiagramComplexModel (resolution : CochainComplex C ℤ ⥤ CochainComplex C ℤ) :
    CochainComplex C ℤ ⥤ CochainComplex (J ⥤ ModuleCat ℂ) ℤ :=
  resolution ⋙ (Cellular.homDiagram ℂ P).mapHomologicalComplex (.up ℤ)

/-- The specified source shift is applied before the replacement. -/
def shiftedHomDiagramComplexModel
    (shift resolution : CochainComplex C ℤ ⥤ CochainComplex C ℤ) :
    CochainComplex C ℤ ⥤ CochainComplex (J ⥤ ModuleCat ℂ) ℤ :=
  shift ⋙ homDiagramComplexModel P resolution

/-- Literal precomposition of every coefficient and differential. -/
def pulledShiftedHomDiagramComplexModel (projection : U ⥤ J)
    (shift resolution : CochainComplex C ℤ ⥤ CochainComplex C ℤ) :
    CochainComplex C ℤ ⥤ CochainComplex (U ⥤ ModuleCat ℂ) ℤ :=
  shiftedHomDiagramComplexModel P shift resolution ⋙
    ((Functor.whiskeringLeft U J (ModuleCat ℂ)).obj projection).mapHomologicalComplex (.up ℤ)

namespace IntegralArrangement

variable {n s : ℕ} (A : Fin s → Fin n → ℤ)
  (c : UniversalIncidenceObject A) (region : Set (Fin n → ℝ))
  (projection : UniversalIncidenceObject A ⥤ J)
  (shift resolution : CochainComplex C ℤ ⥤ CochainComplex C ℤ)

/-- Acyclicity of the original composite Hom diagram gives acyclicity
of the exact shifted model on every coefficient complex. -/
theorem universalLocalMorse_pulledShiftedHomDiagramModel_acyclic
    (vanishes : ∀ K : CochainComplex C ℤ,
      ((universalLocalMorse A ℂ c region).obj
        (((Cellular.homDiagram ℂ P ⋙
          (Functor.whiskeringLeft (UniversalIncidenceObject A) J (ModuleCat ℂ)).obj projection
          ).mapHomologicalComplex (.up ℤ)).obj (resolution.obj K))).Acyclic)
    (K : CochainComplex C ℤ) :
    ((universalLocalMorse A ℂ c region).obj
      ((pulledShiftedHomDiagramComplexModel P projection shift resolution).obj K)).Acyclic := by
  exact vanishes (shift.obj K)

end IntegralArrangement
end ToricPower
end
