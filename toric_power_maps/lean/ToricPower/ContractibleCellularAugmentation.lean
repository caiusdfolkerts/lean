module

public import ToricPower.CellularVertexAugmentation
public import ToricPower.DiagonalAugmentation

/-! # The canonical augmentation of a contractible CW complex

This is the original cellular differential and its ordinary augmentation.
Every characteristic vertex has coefficient one. The result applies to
arbitrary module coefficients and does not require a finite cell set.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits Topology AlgebraicTopology

namespace ToricPower

universe u

variable {k : Type u} [Ring k] (M : ModuleCat.{u} k)
  {E : Type u} [TopologicalSpace E] [T2Space E]
  (C : Set E) [CWComplex C] [ContractibleSpace C] (point : C)

def contractibleCellularHomologyZeroIso :
    (TauCeti.cellularChainComplex C M).homology 0 ≅ M :=
  absoluteCellularSingularIso C M 0 ≪≫
    TauCeti.singularHomology₀SplitIso M point ≪≫
      (isoZeroBiprod (TauCeti.isZero_reducedSingularHomologyFunctor_of_contractibleSpace
        M (TopCat.of C) 0)).symm

theorem contractibleCellularHomologyZeroIso_hom :
    (contractibleCellularHomologyZeroIso M C point).hom =
      (absoluteCellularSingularIso C M 0).hom ≫ (TopCat.of C).singularHomology₀ε M := by
  simp only [contractibleCellularHomologyZeroIso,Iso.trans_hom,Iso.symm_hom,
    isoZeroBiprod_inv,Category.assoc,TauCeti.singularHomology₀SplitIso_hom_snd]

omit point in
theorem contractibleCellular_exactAt (q : ℕ) (positive : q ≠ 0) :
    (TauCeti.cellularChainComplex C M).ExactAt q := by
  apply (HomologicalComplex.exactAt_iff_isZero_homology _ _).mpr
  exact (TauCeti.isZero_singularHomologyFunctor_of_contractibleSpace M
    (TopCat.of C) positive).of_iso (absoluteCellularSingularIso C M q)

/-- The actual augmentation, with its fixed coefficient-one normalization. -/
def contractibleCellularAugmentation :
    TauCeti.cellularChainComplex C M ⟶ (ChainComplex.single₀ (ModuleCat k)).obj M :=
  augmentationOfHomologyZero (TauCeti.cellularChainComplex C M)
    (contractibleCellularHomologyZeroIso M C point).hom

theorem contractibleCellularAugmentation_quasiIso :
    QuasiIso (contractibleCellularAugmentation M C point) :=
  augmentationOfHomologyZero_quasiIso _
    (contractibleCellularHomologyZeroIso M C point)
    (contractibleCellular_exactAt M C)

@[reassoc]
theorem contractibleCellularAugmentation_zero :
    eqToHom (TauCeti.cellularChainComplex_X C M 0).symm ≫
      (contractibleCellularAugmentation M C point).f 0 ≫
      (HomologicalComplex.singleObjXSelf (.down ℕ) 0 M).hom =
        cellularZeroAugmentation M C := by
  rw [contractibleCellularAugmentation,augmentationOfHomologyZero_f_zero,
    contractibleCellularHomologyZeroIso_hom]
  rfl

@[reassoc]
theorem contractibleCellularAugmentation_vertex (vertex : RelCWComplex.cell C 0) :
    Sigma.ι (fun _ : RelCWComplex.cell C 0 => M) vertex ≫
      (TauCeti.cellularChainGroupIso C M 0).inv ≫
      eqToHom (TauCeti.cellularChainComplex_X C M 0).symm ≫
      (contractibleCellularAugmentation M C point).f 0 ≫
      (HomologicalComplex.singleObjXSelf (.down ℕ) 0 M).hom = 𝟙 M := by
  rw [contractibleCellularAugmentation_zero,cellularZeroAugmentation_vertex]

end ToricPower

end
