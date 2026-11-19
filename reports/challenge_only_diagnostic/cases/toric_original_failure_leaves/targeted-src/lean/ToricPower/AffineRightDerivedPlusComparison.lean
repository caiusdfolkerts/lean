module

public import ToricPower.AffineRightDerivedInjective
public import Mathlib.CategoryTheory.Localization.DerivabilityStructure.Derives

/-!
# Natural comparison with the bounded-below right-derived functor

The unbounded affine coresolution comparison is invertible on actual
bounded-below injective complexes. The injective derivability structure
therefore proves its right-derived universal property after restriction
to bounded-below inputs. The usual bounded-below derived functor followed
by its actual inclusion has the same universal property. Their uniqueness
gives a natural isomorphism retaining all coefficient morphisms.

No existence of arbitrary unbounded injective resolutions is used.
-/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory CategoryTheory.Functor CategoryTheory.Limits
  CochainComplex TopologicalSpace

namespace ToricPower

universe u v w z

local instance affinePlusDerivedCategory (X : Scheme.{u}) :
    HasDerivedCategory.{u+1} (QCoh X) := HasDerivedCategory.standard _

variable {X : Scheme.{u}} [EnoughInjectives (QCoh X)]
  {I : Type v} (V : I → X.Opens) [∀ i, IsAffineHom (V i).ι]
  (hV : IsOpenCover V)
  {D : Type w} [Category.{z} D] [Abelian D] [HasDerivedCategory D]
  (H : QCoh X ⥤ D) [H.Additive]
  [∀ i, PreservesFiniteLimits (quasicoherentOpenLocalization (V i).ι ⋙ H)]
  [∀ i, PreservesFiniteColimits (quasicoherentOpenLocalization (V i).ι ⋙ H)]
  (l : List I) (hl : ∀ i, i ∈ l)

/-- Restrict the actual unbounded affine right-derived comparison to
bounded-below complexes, retaining its original component maps. -/
def affineRightDerivedPlusUnit :
    H.mapCochainComplexPlus ⋙ DerivedCategory.Plus.Q ⋙ DerivedCategory.Plus.ι ⟶
      DerivedCategory.Plus.Q ⋙ DerivedCategory.Plus.ι ⋙ affineConeDerivedStage V H l where
  app K := (affineRightDerivedUnit V H l).app K.obj
  naturality {K L} f := (affineRightDerivedUnit V H l).naturality f.hom

/-- The usual bounded-below derived comparison, with its output viewed
in the actual full derived category. -/
def rightDerivedPlusUnderlyingUnit :
    H.mapCochainComplexPlus ⋙ DerivedCategory.Plus.Q ⋙ DerivedCategory.Plus.ι ⟶
      DerivedCategory.Plus.Q ⋙ H.rightDerivedFunctorPlus ⋙ DerivedCategory.Plus.ι :=
  whiskerRight H.rightDerivedFunctorPlusUnit DerivedCategory.Plus.ι ≫
    (Functor.associator DerivedCategory.Plus.Q H.rightDerivedFunctorPlus
      DerivedCategory.Plus.ι).hom

/-- Injective replacement derives the actual termwise functor also
when the target is the full derived category. -/
theorem mapPlusUnderlying_derives :
    (CochainComplex.Plus.localizerMorphism (QCoh X)).Derives
      (H.mapCochainComplexPlus ⋙ DerivedCategory.Plus.Q ⋙ DerivedCategory.Plus.ι) := by
  intro K L f hf
  letI : IsIso ((H.mapCochainComplexPlus ⋙ DerivedCategory.Plus.Q).map
      ((CochainComplex.Plus.localizerMorphism (QCoh X)).functor.map f)) :=
    (CochainComplex.Plus.localizerMorphism_derives_mapCochainComplexPlus H) f hf
  change IsIso (DerivedCategory.Plus.ι.map
    ((H.mapCochainComplexPlus ⋙ DerivedCategory.Plus.Q).map
      ((CochainComplex.Plus.localizerMorphism (QCoh X)).functor.map f)))
  infer_instance

include hV hl in
/-- The actual affine functor restricted to bounded-below inputs has
the same right-derived universal property, proved on actual injectives. -/
theorem affineRightDerivedOnPlus_isRightDerivedFunctor :
    (DerivedCategory.Plus.ι ⋙ affineConeDerivedStage V H l).IsRightDerivedFunctor
      (affineRightDerivedPlusUnit V H l) (CochainComplex.Plus.quasiIso (QCoh X)) := by
  apply (mapPlusUnderlying_derives H).isRightDerivedFunctor_of_isIso
  intro K
  change IsIso ((affineRightDerivedUnit V H l).app
    (((InjectiveObject.ι (QCoh X)).mapHomologicalComplex (.up ℤ)).obj K.obj))
  exact affineRightDerivedUnit_isIso_of_isKInjective V hV H l hl _

/-- The usual bounded-below right-derived functor retains its universal
property after the actual inclusion of its output in the full derived category. -/
theorem rightDerivedPlusUnderlying_isRightDerivedFunctor :
    (H.rightDerivedFunctorPlus ⋙ DerivedCategory.Plus.ι).IsRightDerivedFunctor
      (rightDerivedPlusUnderlyingUnit H) (CochainComplex.Plus.quasiIso (QCoh X)) := by
  apply (mapPlusUnderlying_derives H).isRightDerivedFunctor_of_isIso
  intro K
  letI : IsIso (H.rightDerivedFunctorPlusUnit.app
      ((CochainComplex.Plus.localizerMorphism (QCoh X)).functor.obj K)) :=
    inferInstanceAs (IsIso (H.rightDerivedFunctorPlusUnit.app
      ((InjectiveObject.ι (QCoh X)).mapCochainComplexPlus.obj K)))
  dsimp only [rightDerivedPlusUnderlyingUnit, NatTrans.comp_app, Functor.whiskerRight_app,
    Functor.associator_hom_app]
  infer_instance

/-- A genuine natural isomorphism compares the actual unbounded affine
construction with the ordinary bounded-below right-derived functor on
all bounded-below inputs and all their morphisms. -/
def affineRightDerivedPlusNatIso :
    DerivedCategory.Plus.ι ⋙ affineConeDerivedStage V H l ≅
      H.rightDerivedFunctorPlus ⋙ DerivedCategory.Plus.ι := by
  letI := affineRightDerivedOnPlus_isRightDerivedFunctor V hV H l hl
  letI := rightDerivedPlusUnderlying_isRightDerivedFunctor H
  exact Functor.rightDerivedUnique _ _ (affineRightDerivedPlusUnit V H l)
    (rightDerivedPlusUnderlyingUnit H) (CochainComplex.Plus.quasiIso (QCoh X))

end ToricPower
