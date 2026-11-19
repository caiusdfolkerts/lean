module

public import ToricPower.ArrangementTopCofaceSupport

/-!
# The original top support map in the represented coordinates

The top characteristic-cell generator goes to its actual coface basis
vector, with its coefficient and orientation unchanged.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits
open scoped Classical

namespace ToricPower.IntegralArrangement

variable {n s : ℕ} (A : Fin s → Fin n → ℤ) (S : Set (Fin s))
  (c : IncidenceObject A) (m : Fin n → ℤ) (k : Type) [Field k]

theorem representedTopCofaceMap_coordinates
    (p : RepresentableCostalkIndex A c S m n) (a : k) :
    representedWeightCellularCoordinates A S c m k n
      ((representedTopCofaceMap A k S c m p).f n
        ((HomologicalComplex.singleObjXSelf (.up ℕ) n (ModuleCat.of k k)).inv a)) =
      Finsupp.single p a := by
  let d := representedTopCofaceCell A S c m p
  let h := topCellSupport_le_of_center A d.val d.property
  let e := representedWeightCostalkComplexIso A S c m k ≪≫
    representableCostalkCochainIso k A c S m ≪≫
      representedCostalkOpenSupportIso A S c m k
  let x := (topCellCochainSingleMap A k d.val).f n
    ((HomologicalComplex.singleObjXSelf (.up ℕ) n (ModuleCat.of k k)).inv a)
  let y := (openSupportCochainExtension A k h).f n x
  have transport : openSupportCochainCoordinates A k (representedCostalkSupport A S c m) n y =
      Finsupp.mapDomain (representedCostalkSupportIndexEquiv A S c m n).symm
        (representedWeightCellularCoordinates A S c m k n (e.inv.f n y)) := by
    have value := representedCostalkCochainCoordinates_support A S c m k n
      ((representedWeightCostalkComplexIso A S c m k).hom.f n (e.inv.f n y))
    change openSupportCochainCoordinates A k (representedCostalkSupport A S c m) n
        (e.hom.f n (e.inv.f n y)) = _ at value
    have cancel : e.hom.f n (e.inv.f n y) = y := by
      have actual := ConcreteCategory.congr_hom (congrArg (fun f => f.f n) e.inv_hom_id) y
      simpa only [HomologicalComplex.comp_f, HomologicalComplex.id_f,
        ModuleCat.comp_apply, ModuleCat.id_apply] using actual
    rw [cancel] at value
    change openSupportCochainCoordinates A k (representedCostalkSupport A S c m) n y =
      Finsupp.mapDomain (representedCostalkSupportIndexEquiv A S c m n).symm
        ((representableCostalkCochainCoordinates k A c S m n)
          ((representableCostalkCochainCoordinates k A c S m n).symm
            ((representedWeightCellularCoordinates A S c m k n) (e.inv.f n y)))) at value
    simpa only [LinearEquiv.apply_symm_apply] using value
  have coordinates : openSupportCochainCoordinates A k (representedCostalkSupport A S c m) n y =
      Finsupp.single ((representedCostalkSupportIndexEquiv A S c m n).symm p) a := by
    rw [openSupportCochainExtension_coordinates A k h n x,
      topCellCochainSingleMap_coordinates, Finsupp.mapDomain_single]
    rfl
  have result : representedWeightCellularCoordinates A S c m k n (e.inv.f n y) =
      Finsupp.single p a := by
    apply (Finsupp.mapDomain.linearEquiv k k
      (representedCostalkSupportIndexEquiv A S c m n).symm).injective
    change Finsupp.mapDomain (representedCostalkSupportIndexEquiv A S c m n).symm _ =
      Finsupp.mapDomain (representedCostalkSupportIndexEquiv A S c m n).symm (Finsupp.single p a)
    rw [← transport, coordinates, Finsupp.mapDomain_single]
  exact result

theorem representedTopCofaceMap_generator
    (p : RepresentableCostalkIndex A c S m n) (a : k) :
    (representedTopCofaceMap A k S c m p).f n
        ((HomologicalComplex.singleObjXSelf (.up ℕ) n (ModuleCat.of k k)).inv a) =
      (representedWeightCellularCoordinates A S c m k n).symm (Finsupp.single p a) := by
  apply (representedWeightCellularCoordinates A S c m k n).injective
  rw [representedTopCofaceMap_coordinates, LinearEquiv.apply_symm_apply]

end ToricPower.IntegralArrangement

end
