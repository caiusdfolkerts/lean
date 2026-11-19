module

public import ToricPower.DiagramProjectiveCechDerived
public import ToricPower.LinearHomToSingleExtension
public import ToricPower.RightDerivedPlusNatIso

/-!
# The full projective diagram model on a single coefficient

The comparison is made before localization, in the category of entire
complexes of diagrams. The sign normalization, source-label arrows,
and actual single-complex comparison are all retained explicitly.
-/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Functor CategoryTheory.Limits Opposite
open CochainComplex

namespace ToricPower

universe u v w
variable (R : Type v) [CommRing R]
  {C : Type w} [Category.{v} C] [Abelian C] [Linear R C]
  (K : ChainComplex C ℕ)

/-- Ordinary contravariant coefficients, functorial in every coefficient map. -/
def ordinaryChainCoefficientsFunctor : C ⥤ CochainComplex (ModuleCat.{v} R) ℕ where
  obj Y := ordinaryChainCoefficients R K Y
  map f := ordinaryChainCoefficientsMap R K f
  map_id Y := by
    apply HomologicalComplex.Hom.ext
    funext n
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    change x ≫ 𝟙 Y = x
    exact Category.comp_id x
  map_comp f g := by
    apply HomologicalComplex.Hom.ext
    funext n
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    change x ≫ (f ≫ g) = (x ≫ f) ≫ g
    exact (Category.assoc x f g).symm

/-- A natural isomorphism of whole complex functors, including the exact
signed Hom differential and every coefficient map. -/
def homToSingleNaturalIso :
    CochainComplex.singleFunctor C 0 ⋙
      linearHomComplexFunctor R (K.extend ComplexShape.embeddingDownNat) ≅
    ordinaryChainCoefficientsFunctor R K ⋙
      ComplexShape.embeddingUpNat.extendFunctor (ModuleCat.{v} R) :=
  NatIso.ofComponents (homToSingleExtendedIso R K)
    (fun f => homToSingleExtendedIso_naturality R K f)

section DiagramSingle
variable {L : Type*} [Category* L]

/-- Evaluation of the actual single complex is naturally the actual
single complex at each label. -/
def singleDiagramAsFunctorIso (F : L ⥤ C) :
    ((CochainComplex.singleFunctor (L ⥤ C) 0).obj F).asFunctor ≅
      F ⋙ CochainComplex.singleFunctor C 0 :=
  NatIso.ofComponents
    (fun l => (HomologicalComplex.singleMapHomologicalComplex
      ((evaluation L C).obj l) (.up ℤ) 0).app F)
    (by
      intro l m f
      apply HomologicalComplex.Hom.ext
      funext q
      by_cases hq : q = 0
      · subst q
        simp [HomologicalComplex.singleMapHomologicalComplex,
          CochainComplex.singleFunctor, HomologicalComplex.asFunctor,
          HomologicalComplex.single_map_f_self, HomologicalComplex.single,
          HomologicalComplex.singleObjXSelf, HomologicalComplex.singleObjXIsoOfEq]
      · apply (((evaluation L C).obj l).map_isZero
          (HomologicalComplex.isZero_single_obj_X (.up ℤ) 0 F q hq)).eq_of_src)

end DiagramSingle

variable {A : Type u} [Category.{v} A] [Abelian A]
  {L : Type v} [Category.{v} L]
  (S : A ⥤ L ⥤ C) [S.Additive] {Z : C} (P : ProjectiveResolution Z) (M : A)

/-- The ordinary all-label coefficient diagram for a single actual input. -/
def diagramOrdinaryProjectiveCoefficients : L ⥤ CochainComplex (ModuleCat.{v} R) ℕ :=
  S.obj M ⋙ ordinaryChainCoefficientsFunctor R P.complex

/-- The actual projective Hom model on a single input is isomorphic to
the extended ordinary coefficient complex of the entire label diagram.
This is a chain isomorphism, not merely a coordinatewise cohomology comparison. -/
def diagramProjectiveSingleIso :
    (diagramProjectiveCoefficientComplexFunctor R S P).obj
        ((CochainComplex.singleFunctor A 0).obj M) ≅
      complexDiagramTranspose
        (diagramOrdinaryProjectiveCoefficients R S P M ⋙
          ComplexShape.embeddingUpNat.extendFunctor (ModuleCat.{v} R)) :=
  (complexDiagramPostcompose (linearHomComplexFunctor R (projectiveCochain P))).mapIso
      ((HomologicalComplex.singleMapHomologicalComplex S (.up ℤ) 0).app M) ≪≫
    complexDiagramTransposeFunctor.mapIso
      (Functor.isoWhiskerRight (singleDiagramAsFunctorIso (S.obj M))
          (linearHomComplexFunctor R (projectiveCochain P)) ≪≫
        Functor.associator (S.obj M) (CochainComplex.singleFunctor C 0)
          (linearHomComplexFunctor R (projectiveCochain P)) ≪≫
        Functor.isoWhiskerLeft (S.obj M) (homToSingleNaturalIso R P.complex) ≪≫
        (Functor.associator (S.obj M) (ordinaryChainCoefficientsFunctor R P.complex)
          (ComplexShape.embeddingUpNat.extendFunctor (ModuleCat.{v} R))).symm)

/-- An arbitrary genuine coefficient-diagram isomorphism may be
composed with the single-input calculation without unfolding its data. -/
def diagramProjectiveSingleIsoOfIso
    {F : L ⥤ CochainComplex (ModuleCat.{v} R) ℕ}
    (e : diagramOrdinaryProjectiveCoefficients R S P M ≅ F) :
    (diagramProjectiveCoefficientComplexFunctor R S P).obj
        ((CochainComplex.singleFunctor A 0).obj M) ≅
      complexDiagramTranspose
        (F ⋙ ComplexShape.embeddingUpNat.extendFunctor (ModuleCat.{v} R)) :=
  diagramProjectiveSingleIso R S P M ≪≫
    complexDiagramTransposeFunctor.mapIso
      (Functor.isoWhiskerRight e (ComplexShape.embeddingUpNat.extendFunctor (ModuleCat.{v} R)))

variable [HasDerivedCategory A] [HasDerivedCategory C]
  [HasDerivedCategory (L ⥤ ModuleCat.{v} R)] [EnoughInjectives A]
  [PreservesFiniteLimits S] [PreservesFiniteColimits S]
  (acyclic : ∀ (J : A), Injective J → ∀ (l : L) (n : ℕ),
    (projectiveCoefficientComplex R P ((S.obj J).obj l)).ExactAt (n+1))

/-- The complete single-input dictionary for the actual projective
derived model and its ordinary coefficient complex. -/
def diagramProjectivePlusSingleIso :
    ((ordinaryDiagramProjectiveCoefficients R S (Z := Z)).rightDerivedFunctorPlus ⋙
      DerivedCategory.Plus.ι).obj ((DerivedCategory.Plus.singleFunctor A 0).obj M) ≅
    DerivedCategory.Q.obj (complexDiagramTranspose
      (diagramOrdinaryProjectiveCoefficients R S P M ⋙
        ComplexShape.embeddingUpNat.extendFunctor (ModuleCat.{v} R))) :=
  ((diagramProjectiveCoefficientPlusNatIso R S P acyclic).app
      ((DerivedCategory.Plus.singleFunctor A 0).obj M)).symm ≪≫
    (diagramProjectiveCoefficientDerived R S P).mapIso
      ((DerivedCategory.Plus.singleFunctorιIso A 0).app M) ≪≫
    (diagramProjectiveCoefficientDerivedFactors R S P).app
      ((CochainComplex.singleFunctor A 0).obj M) ≪≫
    DerivedCategory.Q.mapIso (diagramProjectiveSingleIso R S P M)

/-- Ordinary Hom and coefficient-complex comparisons transport through
the genuine derived dictionary, retaining both complete diagrams. -/
def diagramProjectivePlusSingleIsoOfComparisons
    {H : A ⥤ L ⥤ ModuleCat.{v} R} [H.Additive]
    (homComparison : H ≅ ordinaryDiagramProjectiveCoefficients R S (Z := Z))
    {F : L ⥤ CochainComplex (ModuleCat.{v} R) ℕ}
    (coefficientComparison : diagramOrdinaryProjectiveCoefficients R S P M ≅ F) :
    (H.rightDerivedFunctorPlus ⋙ DerivedCategory.Plus.ι).obj
        ((DerivedCategory.Plus.singleFunctor A 0).obj M) ≅
      DerivedCategory.Q.obj (complexDiagramTranspose
        (F ⋙ ComplexShape.embeddingUpNat.extendFunctor (ModuleCat.{v} R))) :=
  DerivedCategory.Plus.ι.mapIso
      ((rightDerivedPlusNatIso homComparison).app ((DerivedCategory.Plus.singleFunctor A 0).obj M)) ≪≫
    diagramProjectivePlusSingleIso R S P M acyclic ≪≫
    DerivedCategory.Q.mapIso (complexDiagramTransposeFunctor.mapIso
      (Functor.isoWhiskerRight coefficientComparison
        (ComplexShape.embeddingUpNat.extendFunctor (ModuleCat.{v} R))))

end ToricPower
