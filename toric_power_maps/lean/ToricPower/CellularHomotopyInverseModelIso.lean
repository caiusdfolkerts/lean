module

public import ToricPower.CellularFiniteHomotopyModel
public import ToricPower.HomotopyDerivedComplexComparison
public import ToricPower.MappedCochainComplexPresentation
public import ToricPower.HomotopyModelPostcomposition

/-!
# Actual finite-model comparison for the homotopy inverse-Nakayama functor

The comparison is ordinary additive functoriality of complexes followed
by actual localization. Its naturality follows from the unique lift in
the K-injective homotopy category. No right-derived comparison is assumed.
-/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits CochainComplex

namespace ToricPower.Cellular

universe u w
variable (k : Type u) [Field k] {C : Type u} [Category.{u} C]
  [Finite C] [∀ c d : C, Finite (c ⟶ d)]
  [HasDerivedCategory.{w} (C ⥤ ModuleCat.{u} k)]

attribute [local instance 2000] Abelian.toPreadditive
attribute [local instance 2000] Preadditive.preadditiveHasZeroMorphisms

/-- The chosen homotopy object is exactly the original finite model. -/
theorem finiteHomotopyFunctor_obj_value (X : FiniteDerivedDiagrams k (C := C)) :
    ((finiteHomotopyFunctor k).obj X).obj =
      (HomotopyCategory.quotient (C ⥤ ModuleCat k) (.up ℤ)).obj
        (finiteChosenModel k X).complex := rfl

/-- The composite is exposed before any concrete object is evaluated. -/
theorem finiteInverseNakayama_eq :
    finiteInverseNakayama k (C := C) =
      (finiteHomotopyFunctor k ⋙ kInjectiveHomotopyInclusion (C ⥤ ModuleCat k)) ⋙
        additiveHomotopyDerived (inverseNakayama k) := by
  exact congrArg (fun H : HomotopyCategory (C ⥤ ModuleCat k) (.up ℤ) ⥤
      DerivedCategory (C ⥤ ModuleCat k) =>
    (finiteHomotopyFunctor k ⋙ kInjectiveHomotopyInclusion (C ⥤ ModuleCat k)) ⋙ H)
      (additiveHomotopyDerived_eq_of_eq (sealedInverseNakayama k) (inverseNakayama k)
        (sealedInverseNakayama_eq k))

theorem finiteHomotopyInclusion_obj (Y : KInjectiveHomotopy (C ⥤ ModuleCat k)) :
    (kInjectiveHomotopyInclusion (C ⥤ ModuleCat k)).obj Y = Y.obj := rfl

/-- Object presentation before applying the quotient comparison. -/
theorem finiteInverseNakayama_obj (X : FiniteDerivedDiagrams k (C := C)) :
    (finiteInverseNakayama k).obj X =
      (additiveHomotopyDerived (inverseNakayama k)).obj
        ((HomotopyCategory.quotient (C ⥤ ModuleCat k) (.up ℤ)).obj
          (finiteChosenModel k X).complex) :=
  (congrArg (fun F : FiniteDerivedDiagrams k (C := C) ⥤
      DerivedCategory (C ⥤ ModuleCat k) => F.obj X) (finiteInverseNakayama_eq k)).trans
    ((CategoryTheory.Functor.comp_obj
      (finiteHomotopyFunctor k ⋙ kInjectiveHomotopyInclusion (C ⥤ ModuleCat k))
      (additiveHomotopyDerived (inverseNakayama k)) X).trans
        (congrArg (additiveHomotopyDerived (inverseNakayama k)).obj
          ((CategoryTheory.Functor.comp_obj (finiteHomotopyFunctor k)
            (kInjectiveHomotopyInclusion (C ⥤ ModuleCat k)) X).trans
              ((finiteHomotopyInclusion_obj k ((finiteHomotopyFunctor k).obj X)).trans
                (finiteHomotopyFunctor_obj_value k X)))))

/-- The mapped-complex wrapper has exactly the ordinary mapped complex. -/
theorem finiteChosenInverseComplex_eq (X : FiniteDerivedDiagrams k (C := C)) :
    (((inverseNakayama k).mapHomologicalComplex (.up ℤ)).obj
      (finiteChosenModel k X).complex) = (finiteChosenModel k X).inverseComplex :=
  SerrePairing.mappedCochainComplex_eq (inverseNakayama k) (finiteChosenModel k X).complex

/-- The model comparison is formed in the ordinary homotopy category
before any concrete coefficient functor is applied. -/
def finiteHomotopyModelIso (X : FiniteDerivedDiagrams k (C := C)) :
    (finiteHomotopyFunctor k ⋙ kInjectiveHomotopyInclusion (C ⥤ ModuleCat k)).obj X ≅
      (HomotopyCategory.quotient (C ⥤ ModuleCat k) (.up ℤ)).obj
        (finiteChosenModel k X).complex := Iso.refl _

/-- The reassociation comparison is natural as a whole functor. -/
def finiteInverseNakayamaPresentationIso :
    finiteInverseNakayama k (C := C) ≅
      (finiteHomotopyFunctor k ⋙ kInjectiveHomotopyInclusion (C ⥤ ModuleCat k)) ⋙
        additiveHomotopyDerived (inverseNakayama k) :=
  eqToIso (finiteInverseNakayama_eq k)

/-- The comparison to the stored finite projective model is useful for
compactness, where the model's projectivity and bounds are already bundled. -/
def finiteInverseModelIso (X : FiniteDerivedDiagrams k (C := C)) :
    (finiteInverseNakayama k).obj X ≅
      DerivedCategory.Q.obj (finiteChosenModel k X).inverseComplex :=
  eqToIso ((finiteInverseNakayama_obj k X).trans
    ((additiveHomotopyDerived_obj_quotient (inverseNakayama k)
      (finiteChosenModel k X).complex).trans
        (congrArg DerivedCategory.Q.obj (finiteChosenInverseComplex_eq k X))))

end ToricPower.Cellular
end
