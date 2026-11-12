module

public import ToricPower.ClosedDualSliceComponents

/-! # Original vertex coordinates of the closed dual augmentation

The comparison with a nonempty convex component uses its ordinary
singular augmentation. Consequently every original characteristic
vertex has coefficient one. This fixes the map, rather than merely
identifying its one-dimensional zeroth homology.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits Topology
open scoped Classical

namespace ToricPower.IntegralArrangement

variable {n s : ℕ} (A : Fin s → Fin n → ℤ)
  (selected : Set (Fin s ⊕ Fin n)) (S : Set (Fin s)) (b : Fin s → ℤ)
  (value : IntegralSliceValue A selected) (k : Type) [CommRing k]

local instance dualAugmentationAmbientCW : CWComplex (arrangementCarrier A) :=
  periodicArrangementCWComplex A
local instance dualAugmentationComponentCW :
    CWComplex (closedDualComponentRegion A selected S b value) :=
  inferInstanceAs (CWComplex
    (closedDualComponentSubcomplex A selected S b value : Set (Fin n → ℝ)))

theorem closedDualComponentZeroIso_hom_present
    (present : (closedDualComponentRegion A selected S b value).Nonempty) :
    (closedDualComponentZeroIso A selected S b value k).hom ≫
        (MorseCoefficients.openScalarPresentIso k present).hom =
      (absoluteCellularSingularIso (closedDualComponentRegion A selected S b value)
        (ModuleCat.of k k) 0).hom ≫
          (TopCat.of (closedDualComponentRegion A selected S b value)).singularHomology₀ε
            (ModuleCat.of k k) := by
  letI := (closedDualComponentRegion_convex A selected S b value).contractibleSpace present
  simp only [closedDualComponentZeroIso,dif_pos present,Iso.trans_hom,Iso.symm_hom,
    Category.assoc,Iso.inv_hom_id,Category.comp_id]
  exact contractibleCellularHomologyZeroIso_hom _ _ _

@[reassoc]
theorem closedDualComponentAugmentation_zero_present
    (present : (closedDualComponentRegion A selected S b value).Nonempty) :
    eqToHom (TauCeti.cellularChainComplex_X
        (closedDualComponentRegion A selected S b value) (ModuleCat.of k k) 0).symm ≫
      (closedDualComponentAugmentation A selected S b value k).f 0 ≫
      (HomologicalComplex.singleObjXSelf (.down ℕ) 0
        (ModuleCat.of k (MorseCoefficients.openScalar k
          (¬ (closedDualComponentRegion A selected S b value).Nonempty)))).hom ≫
      (MorseCoefficients.openScalarPresentIso k present).hom =
        cellularZeroAugmentation (ModuleCat.of k k)
          (closedDualComponentRegion A selected S b value) := by
  rw [closedDualComponentAugmentation,
    ← Category.assoc ((augmentationOfHomologyZero _ _).f 0),
    augmentationOfHomologyZero_f_zero]
  simp only [Category.assoc]
  rw [closedDualComponentZeroIso_hom_present]
  rfl

/-- Every original vertex is sent to its literal scalar coefficient. -/
theorem closedDualComponentAugmentation_coordinates_vertex
    (vertex : ClosedDualComponentCell A selected S b value 0) (r : k) :
    ((HomologicalComplex.singleObjXSelf (.down ℕ) 0
      (ModuleCat.of k (MorseCoefficients.openScalar k
        (¬ (closedDualComponentRegion A selected S b value).Nonempty)))).hom
      ((closedDualComponentAugmentation A selected S b value k).f 0
        ((closedDualComponentCoordinates A selected S b value k 0).symm
          (Finsupp.single vertex r)))).val = r := by
  have present : (closedDualComponentRegion A selected S b value).Nonempty :=
    ⟨cellCenter (augmentedForms A) vertex.val,
      (closedIntegralLevelSlice_cell_iff A selected value.val vertex.val
        (cellCenter_mem _ vertex.val)).mpr vertex.property.1,vertex.property.2⟩
  change (eqToHom (TauCeti.cellularChainComplex_X
      (closedDualComponentRegion A selected S b value) (ModuleCat.of k k) 0).symm ≫
    (closedDualComponentAugmentation A selected S b value k).f 0 ≫
    (HomologicalComplex.singleObjXSelf (.down ℕ) 0 _).hom ≫
    (MorseCoefficients.openScalarPresentIso k present).hom)
      ((closedDualComponentBasis A selected S b value k 0).repr.symm
        (Finsupp.single vertex r)) = r
  rw [closedDualComponentAugmentation_zero_present]
  simp only [Module.Basis.repr_symm_single,closedDualComponentBasis,
    Module.Basis.reindex_apply,map_smul,cellularZeroAugmentation_basis,
    smul_eq_mul,mul_one]
  rw [cellularZeroAugmentation_basis, mul_one]

end ToricPower.IntegralArrangement

end
