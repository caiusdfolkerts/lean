module

public import ToricPower.CellularFiniteHomotopyModel
public import ToricPower.HomotopyDerivedMapFormula

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

theorem finiteHomotopyFunctor_map_eq
    {X Y : FiniteDerivedDiagrams k (C := C)} (f : X ⟶ Y)
    (h : (finiteChosenModel k X).complex ⟶ (finiteChosenModel k Y).complex)
    (lifts : DerivedCategory.Q.map h =
      ((finiteChosenModel k X).iso.hom ≫ f.hom) ≫ (finiteChosenModel k Y).iso.inv) :
    (finiteHomotopyFunctor k).map f = ObjectProperty.homMk
      ((HomotopyCategory.quotient (C ⥤ ModuleCat k) (.up ℤ)).map h) := by
  apply (kInjectiveLocalization (C ⥤ ModuleCat k)).map_injective
  change (kInjectiveLocalization (C ⥤ ModuleCat k)).map ((finiteHomotopyFunctor k).map f) =
    DerivedCategory.Qh.map ((HomotopyCategory.quotient (C ⥤ ModuleCat k) (.up ℤ)).map h)
  calc
    (kInjectiveLocalization (C ⥤ ModuleCat k)).map
        ((finiteHomotopyFunctor k).map f) =
        (finiteHomotopyObjectIso k X).hom ≫ f.hom ≫
          (finiteHomotopyObjectIso k Y).inv :=
      CategoryTheory.Functor.map_preimage _ _
    _ = ((DerivedCategory.quotientCompQhIso (C ⥤ ModuleCat k)).app
          (finiteChosenModel k X).complex).hom ≫ DerivedCategory.Q.map h ≫
        ((DerivedCategory.quotientCompQhIso (C ⥤ ModuleCat k)).app
          (finiteChosenModel k Y).complex).inv := by
      simp only [finiteHomotopyObjectIso, Iso.trans_hom, Iso.trans_inv,
        lifts, Category.assoc]
    _ = DerivedCategory.Qh.map
        ((HomotopyCategory.quotient (C ⥤ ModuleCat k) (.up ℤ)).map h) :=
      (derivedQh_map_quotient_formula h).symm

end ToricPower.Cellular
end
