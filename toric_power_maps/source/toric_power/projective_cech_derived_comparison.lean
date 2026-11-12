module

public import ToricPower.RelativeHomPrecompQuasiIso
public import ToricPower.DerivedHomPlusExt
public import Mathlib.CategoryTheory.Localization.DerivabilityStructure.Derives

/-!
# Natural derived comparison from exact coefficient rows

An exact diagram-valued functor and an actual projective resolution
produce a concrete derived Hom model. If injective source objects have
acyclic positive coefficient rows, its literal augmentation computes
the bounded-below right-derived functor of ordinary coefficient Hom.
The conclusion is a natural isomorphism on the full bounded-below
derived category, not only a family of homology isomorphisms.
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
  (S : A ⥤ C) [S.Additive] {Z : C} (P : ProjectiveResolution Z)

instance projectiveCochain_isKProjective : (projectiveCochain P).IsKProjective := by
  unfold projectiveCochain
  infer_instance

/-- The ordinary Hom functor whose derived value is being calculated. -/
abbrev ordinaryProjectiveCoefficients : A ⥤ ModuleCat.{v} R :=
  S ⋙ (linearCoyoneda R C).obj (op Z)

/-- Naturality of the literal single-source Hom comparison, including
the actual signed Hom differential. -/
theorem linearHomFromSingleIso_inv_naturality
    {K L : CochainComplex C ℤ} (f : K ⟶ L) :
    (((linearCoyoneda R C).obj (op Z)).mapHomologicalComplex (.up ℤ)).map f ≫
        (linearHomFromSingleIso R Z L).inv =
      (linearHomFromSingleIso R Z K).inv ≫
        linearHomComplexMap R ((CochainComplex.singleFunctor C 0).obj Z) f := by
  apply HomologicalComplex.Hom.ext
  funext n
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro z
  change Cochain.fromSingleMk (z ≫ f.f n) (zero_add n) =
    (Cochain.fromSingleMk z (zero_add n)).comp (Cochain.ofHom f) (add_zero n)
  exact Cochain.fromSingleMk_postcomp z (zero_add n) f

/-- The actual projective Hom model before localization. -/
def projectiveCoefficientComplexFunctor :
    CochainComplex A ℤ ⥤ CochainComplex (ModuleCat.{v} R) ℤ :=
  S.mapHomologicalComplex (.up ℤ) ⋙ linearHomComplexFunctor R (projectiveCochain P)

/-- The actual augmentation comparison is a natural transformation of
complete complex functors. -/
def projectiveCoefficientComplexUnit :
    (ordinaryProjectiveCoefficients R S (Z := Z)).mapHomologicalComplex (.up ℤ) ⟶
      projectiveCoefficientComplexFunctor R S P where
  app K :=
    (linearHomFromSingleIso R Z ((S.mapHomologicalComplex (.up ℤ)).obj K)).inv ≫
      linearHomComplexPrecomp R (projectiveCochainAugmentation P)
        ((S.mapHomologicalComplex (.up ℤ)).obj K)
  naturality {K L} f := by
    change (((linearCoyoneda R C).obj (op Z)).mapHomologicalComplex (.up ℤ)).map
      ((S.mapHomologicalComplex (.up ℤ)).map f) ≫ _ = _
    rw [← Category.assoc, linearHomFromSingleIso_inv_naturality,
      Category.assoc, linearHomComplexPrecomp_naturality, ← Category.assoc]
    rfl

variable [HasDerivedCategory A] [HasDerivedCategory C]
  [HasDerivedCategory (ModuleCat.{v} R)]
  [PreservesFiniteLimits S] [PreservesFiniteColimits S]

/-- Exact chart coefficients and the genuine K-projective source invert
every actual quasi-isomorphism, without bounds on its inputs. -/
theorem projectiveCoefficientComplex_inverts :
    (HomologicalComplex.quasiIso A (.up ℤ)).IsInvertedBy
      (projectiveCoefficientComplexFunctor R S P ⋙ DerivedCategory.Q) := by
  intro K L f hf
  let : QuasiIso f := hf
  let : QuasiIso ((S.mapHomologicalComplex (.up ℤ)).map f) := inferInstance
  let := linearHomComplexMap_quasiIso R (projectiveCochain P)
    ((S.mapHomologicalComplex (.up ℤ)).map f)
  exact inferInstanceAs (IsIso (DerivedCategory.Q.map
    (linearHomComplexMap R (projectiveCochain P) ((S.mapHomologicalComplex (.up ℤ)).map f))))

/-- Localization of the actual projective coefficient model. -/
def projectiveCoefficientDerived : DerivedCategory A ⥤ DerivedCategory (ModuleCat.{v} R) :=
  Localization.lift (projectiveCoefficientComplexFunctor R S P ⋙ DerivedCategory.Q)
    (projectiveCoefficientComplex_inverts R S P) DerivedCategory.Q

def projectiveCoefficientDerivedFactors :
    DerivedCategory.Q ⋙ projectiveCoefficientDerived R S P ≅
      projectiveCoefficientComplexFunctor R S P ⋙ DerivedCategory.Q :=
  Localization.fac _ (projectiveCoefficientComplex_inverts R S P) DerivedCategory.Q

/-- The actual derived augmentation, retaining its original chain map. -/
def projectiveCoefficientDerivedUnit :
    (ordinaryProjectiveCoefficients R S (Z := Z)).mapHomologicalComplex (.up ℤ) ⋙
        DerivedCategory.Q ⟶
      DerivedCategory.Q ⋙ projectiveCoefficientDerived R S P :=
  whiskerRight (projectiveCoefficientComplexUnit R S P) DerivedCategory.Q ≫
    (projectiveCoefficientDerivedFactors R S P).inv

variable [EnoughInjectives A]

/-- Restrict the actual augmentation to bounded-below inputs. -/
def projectiveCoefficientPlusUnit :
    (ordinaryProjectiveCoefficients R S (Z := Z)).mapCochainComplexPlus ⋙
        DerivedCategory.Plus.Q ⋙ DerivedCategory.Plus.ι ⟶
      DerivedCategory.Plus.Q ⋙ DerivedCategory.Plus.ι ⋙
        projectiveCoefficientDerived R S P where
  app K := (projectiveCoefficientDerivedUnit R S P).app K.obj
  naturality {_K _L} f := (projectiveCoefficientDerivedUnit R S P).naturality f.hom

/-- The usual injective derivability structure also derives the target
functor after inclusion into the full derived category. -/
theorem projectiveCoefficientPlus_derives :
    (CochainComplex.Plus.localizerMorphism A).Derives
      ((ordinaryProjectiveCoefficients R S (Z := Z)).mapCochainComplexPlus ⋙
        DerivedCategory.Plus.Q ⋙ DerivedCategory.Plus.ι) := by
  intro K L f hf
  let : IsIso (((ordinaryProjectiveCoefficients R S (Z := Z)).mapCochainComplexPlus ⋙
      DerivedCategory.Plus.Q).map ((CochainComplex.Plus.localizerMorphism A).functor.map f)) :=
    (CochainComplex.Plus.localizerMorphism_derives_mapCochainComplexPlus
      (ordinaryProjectiveCoefficients R S (Z := Z))) f hf
  change IsIso (DerivedCategory.Plus.ι.map
    (((ordinaryProjectiveCoefficients R S (Z := Z)).mapCochainComplexPlus ⋙
      DerivedCategory.Plus.Q).map ((CochainComplex.Plus.localizerMorphism A).functor.map f)))
  infer_instance

variable (acyclic : ∀ (J : A), Injective J → ∀ n : ℕ,
    (projectiveCoefficientComplex R P (S.obj J)).ExactAt (n+1))

include acyclic in
/-- Exact rows on actual injectives prove the genuine right-derived
universal property by the injective derivability structure. -/
theorem projectiveCoefficientPlus_isRightDerivedFunctor :
    (DerivedCategory.Plus.ι ⋙ projectiveCoefficientDerived R S P).IsRightDerivedFunctor
      (projectiveCoefficientPlusUnit R S P) (CochainComplex.Plus.quasiIso A) := by
  apply (projectiveCoefficientPlus_derives R S).isRightDerivedFunctor_of_isIso
  intro K
  let I : CochainComplex A ℤ :=
    ((InjectiveObject.ι A).mapHomologicalComplex (.up ℤ)).obj K.obj
  obtain ⟨d, hd⟩ := K.property
  let : K.obj.IsStrictlyGE d := hd
  have : I.IsStrictlyGE d := by dsimp [I]; infer_instance
  have : CochainComplex.IsStrictlyGE ((S.mapHomologicalComplex (.up ℤ)).obj I) d := inferInstance
  have : QuasiIso (linearHomComplexPrecomp R (projectiveCochainAugmentation P)
      ((S.mapHomologicalComplex (.up ℤ)).obj I)) :=
    projective_linearHomPrecomp_quasiIso R P _ d
      (fun q n => acyclic (I.X q) (by dsimp [I]; infer_instance) n)
  have : QuasiIso ((projectiveCoefficientComplexUnit R S P).app I) := by
    dsimp only [projectiveCoefficientComplexUnit]
    infer_instance
  change IsIso ((projectiveCoefficientDerivedUnit R S P).app I)
  dsimp only [projectiveCoefficientDerivedUnit, NatTrans.comp_app, Functor.whiskerRight_app]
  infer_instance

/-- The usual bounded-below derived comparison, with its output in the
full derived category of coefficient modules. -/
def ordinaryProjectivePlusUnit :
    (ordinaryProjectiveCoefficients R S (Z := Z)).mapCochainComplexPlus ⋙
        DerivedCategory.Plus.Q ⋙ DerivedCategory.Plus.ι ⟶
      DerivedCategory.Plus.Q ⋙
        (ordinaryProjectiveCoefficients R S (Z := Z)).rightDerivedFunctorPlus ⋙
          DerivedCategory.Plus.ι :=
  whiskerRight (ordinaryProjectiveCoefficients R S (Z := Z)).rightDerivedFunctorPlusUnit
    DerivedCategory.Plus.ι ≫
      (Functor.associator DerivedCategory.Plus.Q
        (ordinaryProjectiveCoefficients R S (Z := Z)).rightDerivedFunctorPlus
        DerivedCategory.Plus.ι).hom

/-- Its actual right-derived universal property survives the target inclusion. -/
theorem ordinaryProjectivePlus_isRightDerivedFunctor :
    ((ordinaryProjectiveCoefficients R S (Z := Z)).rightDerivedFunctorPlus ⋙
      DerivedCategory.Plus.ι).IsRightDerivedFunctor
      (ordinaryProjectivePlusUnit R S) (CochainComplex.Plus.quasiIso A) := by
  apply (projectiveCoefficientPlus_derives R S).isRightDerivedFunctor_of_isIso
  intro K
  let : IsIso ((ordinaryProjectiveCoefficients R S (Z := Z)).rightDerivedFunctorPlusUnit.app
      ((CochainComplex.Plus.localizerMorphism A).functor.obj K)) :=
    inferInstanceAs (IsIso
      ((ordinaryProjectiveCoefficients R S (Z := Z)).rightDerivedFunctorPlusUnit.app
        ((InjectiveObject.ι A).mapCochainComplexPlus.obj K)))
  dsimp only [ordinaryProjectivePlusUnit, NatTrans.comp_app,
    Functor.whiskerRight_app, Functor.associator_hom_app]
  infer_instance

/-- The actual projective coefficient model and the actual right-derived
ordinary Hom functor are naturally isomorphic on every bounded-below
object and every morphism. -/
def projectiveCoefficientPlusNatIso :
    DerivedCategory.Plus.ι ⋙ projectiveCoefficientDerived R S P ≅
      (ordinaryProjectiveCoefficients R S (Z := Z)).rightDerivedFunctorPlus ⋙
        DerivedCategory.Plus.ι := by
  letI := projectiveCoefficientPlus_isRightDerivedFunctor R S P acyclic
  letI := ordinaryProjectivePlus_isRightDerivedFunctor R S (Z := Z)
  exact Functor.rightDerivedUnique _ _ (projectiveCoefficientPlusUnit R S P)
    (ordinaryProjectivePlusUnit R S) (CochainComplex.Plus.quasiIso A)

end ToricPower
