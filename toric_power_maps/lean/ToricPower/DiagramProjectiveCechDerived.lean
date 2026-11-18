module

public import ToricPower.ProjectiveCechDerivedComparison
public import ToricPower.ComplexDiagramFunctor

/-!
# A natural derived Čech model for whole coefficient diagrams

The projective coefficient construction is applied to a full diagram,
including all of its arrows. Exactness and the injective augmentation
are verified by conservative evaluation; the resulting universal
property and natural isomorphism live in the derived category of the
whole diagram category.
-/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Functor CategoryTheory.Limits Opposite
open CochainComplex CochainComplex.HomComplex

namespace ToricPower

universe u v w
variable (R : Type v) [CommRing R]
  {A : Type u} [Category.{v} A] [Abelian A]
  {C : Type w} [Category.{v} C] [Abelian C] [Linear R C]
  {L : Type v} [Category.{v} L]
  (S : A ⥤ L ⥤ C) [S.Additive] {Z : C} (P : ProjectiveResolution Z)

/-- The ordinary full coefficient diagram, with literal label maps. -/
abbrev ordinaryDiagramProjectiveCoefficients : A ⥤ L ⥤ ModuleCat.{v} R :=
  S ⋙ (Functor.whiskeringRight L C (ModuleCat.{v} R)).obj
    ((linearCoyoneda R C).obj (op Z))

/-- The literal signed projective Hom complex of the whole diagram. -/
def diagramProjectiveCoefficientComplexFunctor :
    CochainComplex A ℤ ⥤ CochainComplex (L ⥤ ModuleCat.{v} R) ℤ :=
  S.mapHomologicalComplex (.up ℤ) ⋙
    complexDiagramPostcompose (linearHomComplexFunctor R (projectiveCochain P))

/-- The original augmentation is a natural chain transformation of
whole diagram complexes. -/
def diagramProjectiveCoefficientComplexUnit :
    (ordinaryDiagramProjectiveCoefficients R S (Z := Z)).mapHomologicalComplex (.up ℤ) ⟶
      diagramProjectiveCoefficientComplexFunctor R S P :=
  whiskerLeft (S.mapHomologicalComplex (.up ℤ))
    (complexDiagramPostcomposeNatTrans (L := L)
      (projectiveCoefficientComplexUnit R (𝟭 C) P))

/-- Exact evaluation recovers the actual scalar-valued projective model. -/
theorem diagramProjectiveCoefficientComplex_evaluation (l : L) :
    diagramProjectiveCoefficientComplexFunctor R S P ⋙
        ((evaluation L (ModuleCat.{v} R)).obj l).mapHomologicalComplex (.up ℤ) =
      projectiveCoefficientComplexFunctor R (S ⋙ (evaluation L C).obj l) P := rfl

variable [HasDerivedCategory A] [HasDerivedCategory C]
  [HasDerivedCategory (L ⥤ ModuleCat.{v} R)]
  [PreservesFiniteLimits S] [PreservesFiniteColimits S]

/-- The full diagram model preserves every quasi-isomorphism, proved
using its actual evaluation functors. -/
theorem diagramProjectiveCoefficientComplex_inverts :
    (HomologicalComplex.quasiIso A (.up ℤ)).IsInvertedBy
      (diagramProjectiveCoefficientComplexFunctor R S P ⋙ DerivedCategory.Q) := by
  intro K M f hf
  let : QuasiIso f := hf
  let : QuasiIso ((S.mapHomologicalComplex (.up ℤ)).map f) := inferInstance
  have : QuasiIso ((diagramProjectiveCoefficientComplexFunctor R S P).map f) := by
    rw [HomologicalComplex.quasiIso_iff_evaluation]
    intro l
    change QuasiIso (linearHomComplexMap R (projectiveCochain P)
      (((S ⋙ (evaluation L C).obj l).mapHomologicalComplex (.up ℤ)).map f))
    exact linearHomComplexMap_quasiIso R (projectiveCochain P) _
  exact inferInstanceAs (IsIso (DerivedCategory.Q.map
    ((diagramProjectiveCoefficientComplexFunctor R S P).map f)))

/-- Localization of the actual whole-diagram model. -/
def diagramProjectiveCoefficientDerived :
    DerivedCategory A ⥤ DerivedCategory (L ⥤ ModuleCat.{v} R) :=
  Localization.lift (diagramProjectiveCoefficientComplexFunctor R S P ⋙ DerivedCategory.Q)
    (diagramProjectiveCoefficientComplex_inverts R S P) DerivedCategory.Q

def diagramProjectiveCoefficientDerivedFactors :
    DerivedCategory.Q ⋙ diagramProjectiveCoefficientDerived R S P ≅
      diagramProjectiveCoefficientComplexFunctor R S P ⋙ DerivedCategory.Q :=
  Localization.fac _ (diagramProjectiveCoefficientComplex_inverts R S P) DerivedCategory.Q

/-- The derived comparison retains the original whole-diagram chain augmentation. -/
def diagramProjectiveCoefficientDerivedUnit :
    (ordinaryDiagramProjectiveCoefficients R S (Z := Z)).mapHomologicalComplex (.up ℤ) ⋙
        DerivedCategory.Q ⟶
      DerivedCategory.Q ⋙ diagramProjectiveCoefficientDerived R S P :=
  whiskerRight (diagramProjectiveCoefficientComplexUnit R S P) DerivedCategory.Q ≫
    (diagramProjectiveCoefficientDerivedFactors R S P).inv

variable [EnoughInjectives A]

/-- The same actual augmentation restricted to bounded-below inputs. -/
def diagramProjectiveCoefficientPlusUnit :
    (ordinaryDiagramProjectiveCoefficients R S (Z := Z)).mapCochainComplexPlus ⋙
        DerivedCategory.Plus.Q ⋙ DerivedCategory.Plus.ι ⟶
      DerivedCategory.Plus.Q ⋙ DerivedCategory.Plus.ι ⋙
        diagramProjectiveCoefficientDerived R S P where
  app K := (diagramProjectiveCoefficientDerivedUnit R S P).app K.obj
  naturality {_K _M} f := (diagramProjectiveCoefficientDerivedUnit R S P).naturality f.hom

/-- Actual injective resolutions derive this ordinary diagram functor. -/
theorem diagramProjectiveCoefficientPlus_derives :
    (CochainComplex.Plus.localizerMorphism A).Derives
      ((ordinaryDiagramProjectiveCoefficients R S (Z := Z)).mapCochainComplexPlus ⋙
        DerivedCategory.Plus.Q ⋙ DerivedCategory.Plus.ι) := by
  intro K M f hf
  let : IsIso (((ordinaryDiagramProjectiveCoefficients R S (Z := Z)).mapCochainComplexPlus ⋙
      DerivedCategory.Plus.Q).map ((CochainComplex.Plus.localizerMorphism A).functor.map f)) :=
    (CochainComplex.Plus.localizerMorphism_derives_mapCochainComplexPlus
      (ordinaryDiagramProjectiveCoefficients R S (Z := Z))) f hf
  change IsIso (DerivedCategory.Plus.ι.map
    (((ordinaryDiagramProjectiveCoefficients R S (Z := Z)).mapCochainComplexPlus ⋙
      DerivedCategory.Plus.Q).map ((CochainComplex.Plus.localizerMorphism A).functor.map f)))
  infer_instance

variable (acyclic : ∀ (J : A), Injective J → ∀ (l : L) (n : ℕ),
    (projectiveCoefficientComplex R P ((S.obj J).obj l)).ExactAt (n+1))

include acyclic in
/-- The full diagram augmentation is a quasi-isomorphism on every
bounded-below complex of actual injectives. -/
theorem diagramProjectiveCoefficientUnit_quasiIso
    (I : CochainComplex A ℤ) (d : ℤ) [I.IsStrictlyGE d] [∀ q, Injective (I.X q)] :
    QuasiIso ((diagramProjectiveCoefficientComplexUnit R S P).app I) := by
  rw [HomologicalComplex.quasiIso_iff_evaluation]
  intro l
  let J := ((S ⋙ (evaluation L C).obj l).mapHomologicalComplex (.up ℤ)).obj I
  let : CochainComplex.IsStrictlyGE J d := inferInstance
  have : QuasiIso (linearHomComplexPrecomp R (projectiveCochainAugmentation P) J) :=
    projective_linearHomPrecomp_quasiIso R P J d
      (fun q n => acyclic (I.X q) inferInstance l n)
  change QuasiIso ((linearHomFromSingleIso R Z J).inv ≫
    linearHomComplexPrecomp R (projectiveCochainAugmentation P) J)
  infer_instance

include acyclic in
/-- The literal model satisfies the actual right-derived universal
property in the whole derived diagram category. -/
theorem diagramProjectiveCoefficientPlus_isRightDerivedFunctor :
    (DerivedCategory.Plus.ι ⋙ diagramProjectiveCoefficientDerived R S P).IsRightDerivedFunctor
      (diagramProjectiveCoefficientPlusUnit R S P) (CochainComplex.Plus.quasiIso A) := by
  apply (diagramProjectiveCoefficientPlus_derives R S).isRightDerivedFunctor_of_isIso
  intro K
  let I : CochainComplex A ℤ :=
    ((InjectiveObject.ι A).mapHomologicalComplex (.up ℤ)).obj K.obj
  obtain ⟨d, hd⟩ := K.property
  let : K.obj.IsStrictlyGE d := hd
  let : I.IsStrictlyGE d := by dsimp [I]; infer_instance
  let : ∀ q, Injective (I.X q) := fun q => by dsimp [I]; infer_instance
  have : QuasiIso ((diagramProjectiveCoefficientComplexUnit R S P).app I) :=
    diagramProjectiveCoefficientUnit_quasiIso R S P acyclic I d
  change IsIso ((diagramProjectiveCoefficientDerivedUnit R S P).app I)
  dsimp only [diagramProjectiveCoefficientDerivedUnit, NatTrans.comp_app,
    Functor.whiskerRight_app]
  infer_instance

/-- The standard derived comparison, after inclusion into the full
unbounded derived diagram category. -/
def ordinaryDiagramProjectivePlusUnit :
    (ordinaryDiagramProjectiveCoefficients R S (Z := Z)).mapCochainComplexPlus ⋙
        DerivedCategory.Plus.Q ⋙ DerivedCategory.Plus.ι ⟶
      DerivedCategory.Plus.Q ⋙
        (ordinaryDiagramProjectiveCoefficients R S (Z := Z)).rightDerivedFunctorPlus ⋙
          DerivedCategory.Plus.ι :=
  whiskerRight (ordinaryDiagramProjectiveCoefficients R S (Z := Z)).rightDerivedFunctorPlusUnit
    DerivedCategory.Plus.ι ≫
      (Functor.associator DerivedCategory.Plus.Q
        (ordinaryDiagramProjectiveCoefficients R S (Z := Z)).rightDerivedFunctorPlus
        DerivedCategory.Plus.ι).hom

theorem ordinaryDiagramProjectivePlus_isRightDerivedFunctor :
    ((ordinaryDiagramProjectiveCoefficients R S (Z := Z)).rightDerivedFunctorPlus ⋙
      DerivedCategory.Plus.ι).IsRightDerivedFunctor
      (ordinaryDiagramProjectivePlusUnit R S) (CochainComplex.Plus.quasiIso A) := by
  apply (diagramProjectiveCoefficientPlus_derives R S).isRightDerivedFunctor_of_isIso
  intro K
  let : IsIso ((ordinaryDiagramProjectiveCoefficients R S (Z := Z)).rightDerivedFunctorPlusUnit.app
      ((CochainComplex.Plus.localizerMorphism A).functor.obj K)) :=
    inferInstanceAs (IsIso
      ((ordinaryDiagramProjectiveCoefficients R S (Z := Z)).rightDerivedFunctorPlusUnit.app
        ((InjectiveObject.ι A).mapCochainComplexPlus.obj K)))
  dsimp only [ordinaryDiagramProjectivePlusUnit, NatTrans.comp_app,
    Functor.whiskerRight_app, Functor.associator_hom_app]
  infer_instance

/-- A genuine natural derived isomorphism of full coefficient diagrams,
retaining every label incidence and every input morphism. -/
def diagramProjectiveCoefficientPlusNatIso :
    DerivedCategory.Plus.ι ⋙ diagramProjectiveCoefficientDerived R S P ≅
      (ordinaryDiagramProjectiveCoefficients R S (Z := Z)).rightDerivedFunctorPlus ⋙
        DerivedCategory.Plus.ι := by
  letI := diagramProjectiveCoefficientPlus_isRightDerivedFunctor R S P acyclic
  letI := ordinaryDiagramProjectivePlus_isRightDerivedFunctor R S (Z := Z)
  exact Functor.rightDerivedUnique _ _ (diagramProjectiveCoefficientPlusUnit R S P)
    (ordinaryDiagramProjectivePlusUnit R S) (CochainComplex.Plus.quasiIso A)

end ToricPower
