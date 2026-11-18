module

public import ToricPower.KInjectiveLocalization
public import ToricPower.AdditiveHomotopyDerivedFunctor
public import ToricPower.CellularFiniteModelData
public import ToricPower.CellularFiniteDerivedCategory
public import ToricPower.CellularSealedInverseNakayama
public import Mathlib.Algebra.Homology.HomotopyCategory.Pretriangulated

/-!
# A genuine homotopy model functor for finite incidence-derived objects

Chosen finite injective models are lifted through the actual fully
faithful K-injective localization. This proves functoriality and
exactness before applying ordinary inverse Nakayama. The construction
uses neither an assumed derived comparison nor arbitrary choices of
morphism representatives without a proof of their compatibility.
-/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits CochainComplex

namespace ToricPower.Cellular

universe u w
variable (k : Type u) [Field k] {C : Type u} [Category.{u} C]
  [HasDerivedCategory.{w} (C ⥤ ModuleCat.{u} k)]

attribute [local instance 2000] Abelian.toPreadditive
attribute [local instance 2000] Preadditive.preadditiveHasZeroMorphisms

local notation "Diag" => C ⥤ ModuleCat k
local notation "Loc" => kInjectiveLocalization Diag

abbrev finiteChosenModel (X : FiniteDerivedDiagrams k (C := C)) :=
  chooseFiniteInjectiveModel k X.property

def finiteHomotopyObject (X : FiniteDerivedDiagrams k (C := C)) :
    KInjectiveHomotopy Diag :=
  ⟨(HomotopyCategory.quotient Diag (.up ℤ)).obj (finiteChosenModel k X).complex,
    CochainComplex.IsKInjective.rightOrthogonal _⟩

def finiteHomotopyObjectIso (X : FiniteDerivedDiagrams k (C := C)) :
    (kInjectiveLocalization (C ⥤ ModuleCat k)).obj (finiteHomotopyObject k X) ≅ X.obj :=
  (DerivedCategory.quotientCompQhIso Diag).app (finiteChosenModel k X).complex ≪≫
    (finiteChosenModel k X).iso

/-- The map is the unique genuine homotopy-class lift of the original
actual derived map, transported along the specified model isomorphisms. -/
def finiteHomotopyFunctor : FiniteDerivedDiagrams k (C := C) ⥤ KInjectiveHomotopy Diag where
  obj := finiteHomotopyObject k
  map {X Y} f := (kInjectiveLocalization (C ⥤ ModuleCat k)).preimage
    ((finiteHomotopyObjectIso k X).hom ≫ f.hom ≫ (finiteHomotopyObjectIso k Y).inv)
  map_id X := by
    apply (kInjectiveLocalization (C ⥤ ModuleCat k)).map_injective
    simp only [Functor.map_preimage, ObjectProperty.FullSubcategory.id_hom,
      Category.id_comp, Iso.hom_inv_id]
    exact (CategoryTheory.Functor.map_id _ _).symm
  map_comp {X Y Z} f g := by
    apply (kInjectiveLocalization (C ⥤ ModuleCat k)).map_injective
    simp only [Functor.map_preimage, Functor.map_comp,
      ObjectProperty.FullSubcategory.comp_hom, Category.assoc, Iso.inv_hom_id_assoc]

def finiteHomotopyFunctorIso :
    finiteHomotopyFunctor k (C := C) ⋙ Loc ≅ finiteDerivedInclusion k :=
  NatIso.ofComponents (finiteHomotopyObjectIso k) (by
    intro X Y f
    change (kInjectiveLocalization (C ⥤ ModuleCat k)).map ((kInjectiveLocalization (C ⥤ ModuleCat k)).preimage _) ≫ (finiteHomotopyObjectIso k Y).hom =
      (finiteHomotopyObjectIso k X).hom ≫ f.hom
    rw [Functor.map_preimage]
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id])

instance finiteHomotopyFunctor_commShift : (finiteHomotopyFunctor k (C := C)).CommShift ℤ :=
  Functor.CommShift.ofComp (finiteHomotopyFunctorIso k) ℤ

instance finiteHomotopyFunctorIso_commShift :
    NatTrans.CommShift (finiteHomotopyFunctorIso k (C := C)).hom ℤ :=
  Functor.CommShift.ofComp_compatibility _ _

instance finiteHomotopyFunctor_isTriangulated : (finiteHomotopyFunctor k (C := C)).IsTriangulated := by
  rw [Functor.isTriangulated_iff_comp_right (finiteHomotopyFunctorIso k)]
  infer_instance

instance finiteHomotopyFunctor_linear : (finiteHomotopyFunctor k (C := C)).Linear k where
  map_smul {X Y} f a := by
    apply (kInjectiveLocalization (C ⥤ ModuleCat k)).map_injective
    change (kInjectiveLocalization (C ⥤ ModuleCat k)).map ((kInjectiveLocalization (C ⥤ ModuleCat k)).preimage _) = (kInjectiveLocalization (C ⥤ ModuleCat k)).map (a • (kInjectiveLocalization (C ⥤ ModuleCat k)).preimage _)
    rw [Functor.map_smul, Functor.map_preimage, Functor.map_preimage]
    change (finiteHomotopyObjectIso k X).hom ≫ (a • f.hom) ≫
        (finiteHomotopyObjectIso k Y).inv =
      a • ((finiteHomotopyObjectIso k X).hom ≫ f.hom ≫ (finiteHomotopyObjectIso k Y).inv)
    simp only [Linear.comp_smul, Linear.smul_comp]

/-- Ordinary inverse Nakayama applied on actual homotopy models and then
localized. This is a genuine exact functor on the finite derived source. -/
abbrev finiteInverseNakayama :
    FiniteDerivedDiagrams k (C := C) ⥤ DerivedCategory Diag :=
  (finiteHomotopyFunctor k ⋙ kInjectiveHomotopyInclusion Diag) ⋙
    additiveHomotopyDerived (sealedInverseNakayama k (C := C))

instance finiteInverseNakayama_commShift : (finiteInverseNakayama k (C := C)).CommShift ℤ := by
  unfold finiteInverseNakayama
  infer_instance

instance finiteInverseNakayama_isTriangulated : (finiteInverseNakayama k (C := C)).IsTriangulated := by
  unfold finiteInverseNakayama
  infer_instance

instance finiteInverseNakayama_linear : (finiteInverseNakayama k (C := C)).Linear k := by
  unfold finiteInverseNakayama
  infer_instance

end ToricPower.Cellular
end
