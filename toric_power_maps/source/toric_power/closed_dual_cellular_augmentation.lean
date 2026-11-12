module

public import ToricPower.ClosedDualCellularComponents
public import ToricPower.ModuleChainDirectSumMap

/-! # The genuine augmentation of all closed dual components

The actual original Laurent-cellular chain complex maps to the full
module of allowed integral components. The map is assembled from the
original vertex augmentations on every convex component, including the
zero modules of empty components. Its quasi-isomorphism is kernel checked
without imposing a finite character or component cutoff.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits

namespace ToricPower.IntegralArrangement

variable {n s : ℕ} (A : Fin s → Fin n → ℤ)
  (selected : Set (Fin s ⊕ Fin n)) (S : Set (Fin s)) (b : Fin s → ℤ)
  (covered : ∀ {q : ℕ} (c : Cell (augmentedForms A) q), selected ⊆ c.val.2 →
    ∃ a : Fin n → ℤ, cellCenter (augmentedForms A) c-latticeLift a ∈
      arrangementZeroSlice (augmentedForms A) selected)
  (k : Type) [CommRing k]

def closedDualAllowedComponent (value : IntegralSliceValue A selected) : Prop :=
  (closedDualComponentRegion A selected S b value).Nonempty

def closedDualAugmentationModule : ModuleCat.{0} k :=
  ModuleCat.of k (MorseCoefficients.LaurentSupport k (closedDualAllowedComponent A selected S b))

def closedDualComponentAugmentationSum :
    closedDualComponentSum A selected S b k ⟶
      (ChainComplex.single₀ (ModuleCat k)).obj (closedDualAugmentationModule A selected S b k) :=
  ModuleChainDirectSum.map k (fun value =>
      closedDualComponentAugmentation A selected S b value k) ≫
    (ModuleChainDirectSum.singleSumIso k (fun value => ModuleCat.of k
      (MorseCoefficients.openScalar k (¬ closedDualAllowedComponent A selected S b value)))).hom ≫
    (ChainComplex.single₀ (ModuleCat k)).map
      (MorseCoefficients.scalarSumLinearEquiv k
        (closedDualAllowedComponent A selected S b)).toModuleIso.hom

instance closedDualComponentAugmentationSum_quasiIso :
    QuasiIso (closedDualComponentAugmentationSum A selected S b k) := by
  letI (value : IntegralSliceValue A selected) :
      QuasiIso (closedDualComponentAugmentation A selected S b value k) :=
    closedDualComponentAugmentation_quasiIso A selected S b value k
  unfold closedDualComponentAugmentationSum
  infer_instance

def closedDualCellularAugmentation :
    closedDualCellularComplex A selected S b k ⟶
      (ChainComplex.single₀ (ModuleCat k)).obj (closedDualAugmentationModule A selected S b k) :=
  (closedDualCellularComponentIso A selected S b covered k).hom ≫
    closedDualComponentAugmentationSum A selected S b k

instance closedDualCellularAugmentation_quasiIso :
    QuasiIso (closedDualCellularAugmentation A selected S b covered k) := by
  unfold closedDualCellularAugmentation
  infer_instance

end ToricPower.IntegralArrangement

end

