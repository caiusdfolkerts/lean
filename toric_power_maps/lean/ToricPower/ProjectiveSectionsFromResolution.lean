module

public import ToricPower.ProjectiveSectionsInjectiveComparison
public import ToricPower.MappedSingleAugmentationInteger
public import ToricPower.InjectiveResolutionMap

/-! # Canonical projective sections from an actual injective resolution -/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits Opposite CochainComplex

namespace ToricPower

section Extension
variable {A D : Type*} [Category* A] [Category* D] [Abelian A] [Abelian D]
  {Z : A} {I : CochainComplex A ℕ}

instance extendedSingleAugmentation_quasiIso
    (ι : (CochainComplex.single₀ A).obj Z ⟶ I) [QuasiIso ι] :
    QuasiIso (extendedSingleAugmentation ι) := by
  unfold extendedSingleAugmentation
  infer_instance

theorem integerMappedSingleAugmentation_quasiIso
    (F : A ⥤ D) [F.Additive] {V : D} (a : V ⟶ F.obj Z)
    (ι : (CochainComplex.single₀ A).obj Z ⟶ I)
    [QuasiIso (mappedSingleAugmentation F a ι)] :
    QuasiIso (integerMappedSingleAugmentation F a ι) := by
  haveI : QuasiIso (integerMappedSingleAugmentation F a ι ≫
      (mapExtendIso F I ComplexShape.embeddingUpNat).hom) := by
    rw [integerMappedSingleAugmentation_comparison]
    infer_instance
  exact quasiIso_of_comp_right _ (mapExtendIso F I ComplexShape.embeddingUpNat).hom
end Extension

universe u v
variable (R : Type v) [CommRing R]
  {A : Type u} [Category.{v} A] [Abelian A] [Linear R A]
  {Z M : A} (P : ProjectiveResolution Z) {V : ModuleCat.{v} R}

def singleCoefficientSection
    (a : V ⟶ ((linearCoyoneda R A).obj (op Z)).obj M) :
    (CochainComplex.singleFunctor (ModuleCat.{v} R) 0).obj V ⟶
      (((linearCoyoneda R A).obj (op Z)).mapHomologicalComplex (.up ℤ)).obj
        ((CochainComplex.singleFunctor A 0).obj M) :=
  (CochainComplex.singleFunctor (ModuleCat.{v} R) 0).map a ≫
    (HomologicalComplex.singleMapHomologicalComplex
      ((linearCoyoneda R A).obj (op Z)) (.up ℤ) 0).inv.app M

def scalarProjectiveSectionMap
    (a : V ⟶ ((linearCoyoneda R A).obj (op Z)).obj M) :
    (CochainComplex.singleFunctor (ModuleCat.{v} R) 0).obj V ⟶
      (projectiveCoefficientComplexFunctor R (𝟭 A) P).obj
        ((CochainComplex.singleFunctor A 0).obj M) :=
  singleCoefficientSection R a ≫ (projectiveCoefficientComplexUnit R (𝟭 A) P).app _

variable [HasDerivedCategory A]

theorem scalarProjectiveSectionMap_quasiIso_of_resolution
    (a : V ⟶ ((linearCoyoneda R A).obj (op Z)).obj M) (J : InjectiveResolution M)
    [QuasiIso (mappedSingleAugmentation ((linearCoyoneda R A).obj (op Z)) a J.ι)] :
    QuasiIso (scalarProjectiveSectionMap R P a) := by
  letI : ∀ n, Injective (J.cocomplex.X n) := J.injective
  haveI : CochainComplex.IsKInjective
      (J.cocomplex.extend ComplexShape.embeddingUpNat) := inferInstance
  haveI : CochainComplex.IsKInjective
      ((𝟭 (CochainComplex A ℤ)).obj (J.cocomplex.extend ComplexShape.embeddingUpNat)) :=
    inferInstanceAs (CochainComplex.IsKInjective
      (J.cocomplex.extend ComplexShape.embeddingUpNat))
  haveI : CochainComplex.IsKInjective
      (((𝟭 A).mapHomologicalComplex (.up ℤ)).obj
        (J.cocomplex.extend ComplexShape.embeddingUpNat)) :=
    CochainComplex.isKInjective_of_iso
      ((Functor.mapHomologicalComplexIdIso A (.up ℤ)).app
        (J.cocomplex.extend ComplexShape.embeddingUpNat)).symm
  haveI := integerMappedSingleAugmentation_quasiIso
    ((linearCoyoneda R A).obj (op Z)) a J.ι
  haveI : QuasiIso (singleCoefficientSection R a ≫
      ((ordinaryProjectiveCoefficients R (𝟭 A) (Z := Z)).mapHomologicalComplex
        (.up ℤ)).map (extendedSingleAugmentation J.ι)) := by
    change QuasiIso (integerMappedSingleAugmentation
      ((linearCoyoneda R A).obj (op Z)) a J.ι)
    infer_instance
  exact projectiveSectionMap_quasiIso_of_injective_comparison R (𝟭 A) P
    (extendedSingleAugmentation J.ι) (singleCoefficientSection R a)

end ToricPower

end
