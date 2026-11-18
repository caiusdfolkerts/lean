module

public import ToricPower.CellularConeKProjective
public import ToricPower.ResolutionDerivedUniversal

/-!
# The actual unbounded absolute left-derived cellular realization

The finite cone construction is a K-projective replacement on arbitrary
unbounded diagram complexes.  This file proves its genuine absolute
left-derived universal property.  It does not assume that a derived
functor exists, or replace that property by preservation of
quasi-isomorphisms alone.

The realization is allowed to take infinite-dimensional coefficient
vector spaces.  No properness, cohomological finiteness, unbounded
right-derived Hom, or diagonal counit theorem is asserted here.

-/

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor CochainComplex

namespace ToricPower.Cellular

universe u v w w'

variable (k : Type u) [Field k] {C : Type u} [Category.{u} C]
  {A : Type v} [Category.{u} A] [Abelian A]
  [HasDerivedCategory (C ⥤ ModuleCat.{u} k)] [HasDerivedCategory A]
  (H : (C ⥤ ModuleCat.{u} k) ⥤ A) [H.Additive]

/-- The literal comparison to applying the ordinary functor degreewise. -/
def finiteConeRealizationComparison (m : ℕ) :
    DerivedCategory.Q ⋙ finiteConeRealizationStageDerived k H m ⟶
      H.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q :=
  resolutionDerivedCounit (finiteConeResolution k m).functor
    (finiteConeResolution k m).augmentation DerivedCategory.Q
    (H.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
    (finiteConeRealizationStageDerived k H m)
    (finiteConeRealizationStageDerivedFactors k H m)

@[simp]
theorem finiteConeRealizationComparison_app (m : ℕ)
    (X : CochainComplex (C ⥤ ModuleCat.{u} k) ℤ) :
    (finiteConeRealizationComparison k H m).app X =
      (finiteConeRealizationStageDerivedFactors k H m).hom.app X ≫
        DerivedCategory.Q.map ((H.mapHomologicalComplex (.up ℤ)).map
          ((finiteConeResolution k m).augmentation.app X)) := by
  simp only [finiteConeRealizationComparison, resolutionDerivedCounit_app, Functor.comp_map]

/-- The actual localized cone construction satisfies the left-derived
universal property whenever the displayed augmentation has been proved
a quasi-isomorphism.  The later finite-grade theorem discharges this
condition for the actual incidence categories. -/
theorem finiteConeRealization_isLeftDerivedFunctor (m : ℕ)
    (hε : ∀ X : CochainComplex (C ⥤ ModuleCat.{u} k) ℤ,
      QuasiIso ((finiteConeResolution k m).augmentation.app X)) :
    (finiteConeRealizationStageDerived k H m).IsLeftDerivedFunctor
      (finiteConeRealizationComparison k H m)
      (HomologicalComplex.quasiIso (C ⥤ ModuleCat.{u} k) (.up ℤ)) := by
  apply resolution_isLeftDerivedFunctor
    (finiteConeResolution k m).functor (finiteConeResolution k m).augmentation
    DerivedCategory.Q (HomologicalComplex.quasiIso _ (.up ℤ))
    (fun X => by
      letI := hε X
      infer_instance)
    (finiteConeRealizationStageDerivedFactors k H m)
  exact finiteConeResolution_augmentationCoherence k H m hε

/-- The proved universal property is absolute: arbitrary
postcomposition retains the actual right-Kan comparison. -/
theorem finiteConeRealization_isAbsoluteLeftDerivedFunctor (m : ℕ)
    (hε : ∀ X : CochainComplex (C ⥤ ModuleCat.{u} k) ℤ,
      QuasiIso ((finiteConeResolution k m).augmentation.app X))
    {E : Type w} [Category.{w'} E] (T : DerivedCategory A ⥤ E) :
    (finiteConeRealizationStageDerived k H m ⋙ T).IsLeftDerivedFunctor
      ((Functor.associator DerivedCategory.Q (finiteConeRealizationStageDerived k H m) T).inv ≫
        whiskerRight (finiteConeRealizationComparison k H m) T)
      (HomologicalComplex.quasiIso (C ⥤ ModuleCat.{u} k) (.up ℤ)) := by
  apply resolution_isAbsoluteLeftDerivedFunctor
    (finiteConeResolution k m).functor (finiteConeResolution k m).augmentation
    DerivedCategory.Q (HomologicalComplex.quasiIso _ (.up ℤ))
    (fun X => by
      letI := hε X
      infer_instance)
    (finiteConeRealizationStageDerivedFactors k H m)
    (finiteConeResolution_augmentationCoherence k H m hε) T

/-- On actual K-projective inputs the derived comparison is an
isomorphism, because the augmentation is an actual homotopy equivalence. -/
theorem finiteConeRealizationComparison_isIso (m : ℕ)
    (hε : ∀ X : CochainComplex (C ⥤ ModuleCat.{u} k) ℤ,
      QuasiIso ((finiteConeResolution k m).augmentation.app X))
    (X : CochainComplex (C ⥤ ModuleCat.{u} k) ℤ) [X.IsKProjective] :
    IsIso ((finiteConeRealizationComparison k H m).app X) := by
  letI := finiteConeResolution_isKProjective k m X
  letI : CochainComplex.IsKProjective ((𝟭 (CochainComplex (C ⥤ ModuleCat.{u} k) ℤ)).obj X) :=
    inferInstanceAs X.IsKProjective
  have he := (CochainComplex.IsKProjective.quasiIso_iff
    ((finiteConeResolution k m).augmentation.app X)).1 (hε X)
  have heH := H.homotopyEquivalences_mapHomologicalComplex_map
    ((finiteConeResolution k m).augmentation.app X) he
  letI : QuasiIso ((H.mapHomologicalComplex (.up ℤ)).map
      ((finiteConeResolution k m).augmentation.app X)) :=
    homotopyEquivalences_le_quasiIso A (.up ℤ) _ heH
  rw [finiteConeRealizationComparison_app]
  infer_instance

/-- On a projective object placed in any single degree, the actual
derived functor agrees with the actual ordinary realization. -/
def finiteConeRealizationProjectiveIso (m : ℕ)
    (hε : ∀ X : CochainComplex (C ⥤ ModuleCat.{u} k) ℤ,
      QuasiIso ((finiteConeResolution k m).augmentation.app X))
    (V : C ⥤ ModuleCat.{u} k) [Projective V] (i : ℤ) :
    (finiteConeRealizationStageDerived k H m).obj
        ((DerivedCategory.singleFunctor (C ⥤ ModuleCat.{u} k) i).obj V) ≅
      (DerivedCategory.singleFunctor A i).obj (H.obj V) := by
  let K : CochainComplex (C ⥤ ModuleCat.{u} k) ℤ :=
    (HomologicalComplex.single (C ⥤ ModuleCat.{u} k) (.up ℤ) i).obj V
  letI : K.IsKProjective := CochainComplex.isKProjective_of_projective K i
  letI := finiteConeRealizationComparison_isIso k H m hε K
  exact asIso ((finiteConeRealizationComparison k H m).app K) ≪≫
    DerivedCategory.Q.mapIso
      ((HomologicalComplex.singleMapHomologicalComplex H (.up ℤ) i).app V)

section BoundedGrade

variable (grade : C → ℕ)
  (grade_le : ∀ {c d : C} (_ : c ⟶ d), grade c ≤ grade d)
  (eq_of_grade_eq : ∀ {c d : C} (_ : c ⟶ d), grade c = grade d → c = d)
  [∀ c : C, Subsingleton (c ⟶ c)]
  (N : ℕ) (hbound : ∀ c : C, grade c ≤ N)

include grade grade_le eq_of_grade_eq hbound

/-- The actual finite-grade endpoint, with the augmentation hypothesis
fully discharged by the proved support drop of the genuine vector cover. -/
theorem finiteGradeRealization_isLeftDerivedFunctor :
    (finiteConeRealizationStageDerived k H (N+1)).IsLeftDerivedFunctor
      (finiteConeRealizationComparison k H (N+1))
      (HomologicalComplex.quasiIso (C ⥤ ModuleCat.{u} k) (.up ℤ)) :=
  finiteConeRealization_isLeftDerivedFunctor k H (N+1)
    (finiteConeResolution_augmentation_quasiIso k grade grade_le eq_of_grade_eq N hbound)

/-- The finite-grade endpoint is absolute on the full unbounded
derived categories, with no finiteness condition on coefficient modules. -/
theorem finiteGradeRealization_isAbsoluteLeftDerivedFunctor
    {E : Type w} [Category.{w'} E] (T : DerivedCategory A ⥤ E) :
    (finiteConeRealizationStageDerived k H (N+1) ⋙ T).IsLeftDerivedFunctor
      ((Functor.associator DerivedCategory.Q (finiteConeRealizationStageDerived k H (N+1)) T).inv ≫
        whiskerRight (finiteConeRealizationComparison k H (N+1)) T)
      (HomologicalComplex.quasiIso (C ⥤ ModuleCat.{u} k) (.up ℤ)) :=
  finiteConeRealization_isAbsoluteLeftDerivedFunctor k H (N+1)
    (finiteConeResolution_augmentation_quasiIso k grade grade_le eq_of_grade_eq N hbound) T

end BoundedGrade

end ToricPower.Cellular

end
