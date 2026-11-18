module

public import ToricPower.CellularFiniteHomotopyModel
public import ToricPower.CellularHomotopyPairingModelIso
public import ToricPower.CellularFiniteHomotopyMaps

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

theorem finiteInversePairingModelIso_naturality
    {X Y : FiniteDerivedDiagrams k (C := C)} (f : X ⟶ Y)
    (h : (finiteChosenModel k X).complex ⟶ (finiteChosenModel k Y).complex)
    (lifts : DerivedCategory.Q.map h =
      ((finiteChosenModel k X).iso.hom ≫ f.hom) ≫ (finiteChosenModel k Y).iso.inv) :
    (finiteInverseNakayama k).map f ≫ (finiteInversePairingModelIso k Y).hom =
      (finiteInversePairingModelIso k X).hom ≫
        DerivedCategory.Q.map (((sealedInverseNakayama k).mapHomologicalComplex (.up ℤ)).map h) := by
  have lifting :
      (finiteHomotopyFunctor k ⋙ kInjectiveHomotopyInclusion (C ⥤ ModuleCat k)).map f ≫
          (finiteHomotopyModelIso k Y).hom =
        (finiteHomotopyModelIso k X).hom ≫
          (HomotopyCategory.quotient (C ⥤ ModuleCat k) (.up ℤ)).map h := by
    change ((finiteHomotopyFunctor k).map f).hom ≫ 𝟙 _ = 𝟙 _ ≫ _
    rw [finiteHomotopyFunctor_map_eq k f h lifts]
    simp only [ObjectProperty.homMk_hom, Category.comp_id, Category.id_comp]
  exact presentedMappedHomotopyModelIso_naturality (sealedInverseNakayama k)
    (finiteHomotopyFunctor k ⋙ kInjectiveHomotopyInclusion (C ⥤ ModuleCat k))
    (fun X => (finiteChosenModel k X).complex) (finiteHomotopyModelIso k)
    (finiteInverseNakayama k) (finiteInverseNakayamaSealedPresentationIso k) f h lifting


theorem finiteInversePairingModelIso_inv_naturality
    {X Y : FiniteDerivedDiagrams k (C := C)} (f : X ⟶ Y)
    (h : (finiteChosenModel k X).complex ⟶ (finiteChosenModel k Y).complex)
    (lifts : DerivedCategory.Q.map h =
      ((finiteChosenModel k X).iso.hom ≫ f.hom) ≫ (finiteChosenModel k Y).iso.inv) :
    (finiteInversePairingModelIso k X).inv ≫ (finiteInverseNakayama k).map f =
      DerivedCategory.Q.map (((sealedInverseNakayama k).mapHomologicalComplex (.up ℤ)).map h) ≫
        (finiteInversePairingModelIso k Y).inv := by
  have equation := finiteInversePairingModelIso_naturality k f h lifts
  have transported := congrArg
    (fun f => ((finiteInversePairingModelIso k X).inv ≫ f) ≫ (finiteInversePairingModelIso k Y).inv) equation
  simpa only [Category.assoc, Iso.hom_inv_id_assoc, Iso.inv_hom_id_assoc,
    Iso.hom_inv_id, Category.comp_id] using transported

end ToricPower.Cellular
end
