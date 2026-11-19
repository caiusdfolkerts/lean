module

public import ToricPower.ClosedDualCellularAugmentation
public import ToricPower.ClosedDualAugmentationCoordinates

/-! # Every original vertex of the complete component augmentation

The full augmentation sends an original Laurent vertex to the basis
vector of its actual integral slice component, with the same scalar.
This formula fixes the entire map and is independent of any choice of
vertex or contraction within a component.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits
open scoped Classical

namespace ToricPower.IntegralArrangement

variable {n s : ℕ} (A : Fin s → Fin n → ℤ)
  (selected : Set (Fin s ⊕ Fin n)) (S : Set (Fin s)) (b : Fin s → ℤ)
  (covered : ∀ {q : ℕ} (c : Cell (augmentedForms A) q), selected ⊆ c.val.2 →
    ∃ a : Fin n → ℤ, cellCenter (augmentedForms A) c-latticeLift a ∈
      arrangementZeroSlice (augmentedForms A) selected)
  (k : Type) [CommRing k]

theorem closedDualCellularComponentIso_generator (q : ℕ)
    (p : ClosedDualCellularIndex A selected S b q) (r : k) :
    (closedDualCellularComponentIso A selected S b covered k).hom.f q
      ((closedDualCellularCoordinates A selected S b k q).symm (Finsupp.single p r)) =
      DFinsupp.single (closedDualLaurentComponentsEquiv A selected S b covered q p).1
        ((closedDualComponentCoordinates A selected S b
          (closedDualLaurentComponentsEquiv A selected S b covered q p).1 k q).symm
            (Finsupp.single (closedDualLaurentComponentsEquiv A selected S b covered q p).2 r)) := by
  change (closedDualComponentSumCoordinates A selected S b k q).symm
    (Finsupp.mapDomain (closedDualLaurentComponentsEquiv A selected S b covered q)
      ((closedDualCellularCoordinates A selected S b k q)
        ((closedDualCellularCoordinates A selected S b k q).symm (Finsupp.single p r)))) = _
  rw [LinearEquiv.apply_symm_apply,Finsupp.mapDomain_single]
  exact ModuleChainDirectSum.coordinates_symm_single k
    (fun value => closedDualComponentComplex A selected S b value k)
    (ClosedDualComponentCell A selected S b)
    (fun value => closedDualComponentCoordinates A selected S b value k) q _ _ r

omit covered in
theorem closedDualComponentAugmentationSum_generator
    (value : IntegralSliceValue A selected)
    (p : ClosedDualComponentCell A selected S b value 0) (r : k) :
    ((HomologicalComplex.singleObjXSelf (.down ℕ) 0
      (closedDualAugmentationModule A selected S b k)).hom
      ((closedDualComponentAugmentationSum A selected S b k).f 0
        (DFinsupp.single value ((closedDualComponentCoordinates A selected S b value k 0).symm
          (Finsupp.single p r))))).val = Finsupp.single value r := by
  simp only [closedDualComponentAugmentationSum,HomologicalComplex.comp_f,
    ModuleCat.comp_apply,
    ModuleChainDirectSum.singleSumIso_f_zero,
    ChainComplex.single₀_map_f_zero]
  erw [ModuleCat.id_apply,ModuleChainDirectSum.map_single]
  change (MorseCoefficients.scalarSum k (closedDualAllowedComponent A selected S b)
    (DFinsupp.single value
      ((closedDualComponentAugmentation A selected S b value k).f 0
        ((closedDualComponentCoordinates A selected S b value k 0).symm
          (Finsupp.single p r))))).val = _
  change ((DFinsupp.lsum k (MorseCoefficients.scalarMonomial k
    (closedDualAllowedComponent A selected S b)))
      (DFinsupp.single value
        ((closedDualComponentAugmentation A selected S b value k).f 0
          ((closedDualComponentCoordinates A selected S b value k 0).symm
            (Finsupp.single p r))))).val = _
  erw [DFinsupp.lsum_single]
  change Finsupp.single value
    (((closedDualComponentAugmentation A selected S b value k).f 0
      ((closedDualComponentCoordinates A selected S b value k 0).symm
        (Finsupp.single p r))).val) = _
  congr 1
  exact closedDualComponentAugmentation_coordinates_vertex A selected S b value k p r

theorem closedDualCellularAugmentation_generator
    (p : ClosedDualCellularIndex A selected S b 0) (r : k) :
    ((HomologicalComplex.singleObjXSelf (.down ℕ) 0
      (closedDualAugmentationModule A selected S b k)).hom
      ((closedDualCellularAugmentation A selected S b covered k).f 0
        ((closedDualCellularCoordinates A selected S b k 0).symm
          (Finsupp.single p r)))).val =
      Finsupp.single (closedDualLaurentComponentsEquiv A selected S b covered 0 p).1 r := by
  simp only [closedDualCellularAugmentation,HomologicalComplex.comp_f,ModuleCat.comp_apply]
  rw [closedDualCellularComponentIso_generator]
  exact closedDualComponentAugmentationSum_generator A selected S b k _ _ r

end ToricPower.IntegralArrangement

end
