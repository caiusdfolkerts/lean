module

public import ToricPower.CWRelativeCellularBoundary

/-!
# Relative cellular maps in their actual characteristic bases

An ambient cellular map preserving the characteristic disk of a cell
sends the corresponding relative basis vector to that same target cell
when it survives, and to zero when it belongs to the target base.
The proof uses the actual commuting quotient square on cellular chain
groups. It includes cells absorbed by the relative base.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits Topology Topology.RelCWComplex Set
open scoped Classical

namespace ToricPower

universe w

variable {X Y : Type w} [TopologicalSpace X] [T2Space X]
  [TopologicalSpace Y] [T2Space Y]
  (C : Set X) (D : Set Y) [CWComplex C] [CWComplex D]
  (A : CWComplex.Subcomplex C) (B : CWComplex.Subcomplex D)
  (f : TopCat.of C ⟶ TopCat.of D) (hf : TauCeti.IsCellular C D f)
  (base : ∀ x : C, x.val ∈ A → (f x).val ∈ B)
  (R : Type w) [Ring R]

/-- The actual relative map commutes with both quotient maps from the
ambient cellular chain groups. -/
theorem relativeCWChainGroupMap_quotient_square (q : ℕ) :
    TauCeti.cellularChainGroupMap C (relativeCWCarrier A)
        (absoluteToRelativeCWMap_cellular C A) (ModuleCat.of R R) q ≫
      TauCeti.cellularChainGroupMap (relativeCWCarrier A) (relativeCWCarrier B)
        (relativeCWMap_cellular A B f hf base) (ModuleCat.of R R) q =
    TauCeti.cellularChainGroupMap C D hf (ModuleCat.of R R) q ≫
      TauCeti.cellularChainGroupMap D (relativeCWCarrier B)
        (absoluteToRelativeCWMap_cellular D B) (ModuleCat.of R R) q := by
  rw [← TauCeti.cellularChainGroupMap_comp C (relativeCWCarrier A)
    (absoluteToRelativeCWMap_cellular C A) (relativeCWCarrier B)
    (relativeCWMap_cellular A B f hf base) (ModuleCat.of R R) q]
  rw [← TauCeti.cellularChainGroupMap_comp C D hf (relativeCWCarrier B)
    (absoluteToRelativeCWMap_cellular D B) (ModuleCat.of R R) q]

/-- A surviving target cell retains its literal characteristic-disk
generator and its original orientation under the relative map. -/
theorem relativeCWChainGroupMap_basis_survives (q : ℕ)
    (i : cell (relativeCWCarrier A) q) (j : cell (relativeCWCarrier B) q)
    (characteristic : TauCeti.characteristicCellPairMap C i.val ≫
      TauCeti.skeletonPairMap C D hf q = TauCeti.characteristicCellPairMap D j.val) :
    TauCeti.cellularChainGroupMap (relativeCWCarrier A) (relativeCWCarrier B)
        (relativeCWMap_cellular A B f hf base) (ModuleCat.of R R) q
        (TauCeti.cellularChainBasis (relativeCWCarrier A) R q i) =
      TauCeti.cellularChainBasis (relativeCWCarrier B) R q j := by
  have square := ConcreteCategory.congr_hom
    (relativeCWChainGroupMap_quotient_square C D A B f hf base R q)
    (TauCeti.cellularChainBasis C R q i.val)
  simp only [ConcreteCategory.comp_apply] at square
  rw [absoluteToRelative_basis_survives C A R i,
    cellularChainGroupMap_basis_of_characteristic C D hf R i.val j.val characteristic,
    absoluteToRelative_basis_survives D B R j] at square
  exact square

/-- A target characteristic disk contained in the base gives zero.
No basis vector is silently retained after it is absorbed. -/
theorem relativeCWChainGroupMap_basis_absorbed (q : ℕ)
    (i : cell (relativeCWCarrier A) q) (j : cell D q) (absorbed : j ∈ B.I q)
    (characteristic : TauCeti.characteristicCellPairMap C i.val ≫
      TauCeti.skeletonPairMap C D hf q = TauCeti.characteristicCellPairMap D j) :
    TauCeti.cellularChainGroupMap (relativeCWCarrier A) (relativeCWCarrier B)
        (relativeCWMap_cellular A B f hf base) (ModuleCat.of R R) q
        (TauCeti.cellularChainBasis (relativeCWCarrier A) R q i) = 0 := by
  have square := ConcreteCategory.congr_hom
    (relativeCWChainGroupMap_quotient_square C D A B f hf base R q)
    (TauCeti.cellularChainBasis C R q i.val)
  simp only [ConcreteCategory.comp_apply] at square
  rw [absoluteToRelative_basis_survives C A R i,
    cellularChainGroupMap_basis_of_characteristic C D hf R i.val j characteristic,
    absoluteToRelative_basis_absorbed D B R j absorbed] at square
  exact square

/-- The full coefficient of a preserved characteristic disk is its
literal cell Kronecker coefficient. This formula handles both surviving
and absorbed target cells without a premise excluding either case. -/
theorem relativeCWChainGroupMap_basis_coefficient (q : ℕ)
    (i : cell (relativeCWCarrier A) q) (j : cell (relativeCWCarrier B) q)
    (target : cell D q)
    (characteristic : TauCeti.characteristicCellPairMap C i.val ≫
      TauCeti.skeletonPairMap C D hf q = TauCeti.characteristicCellPairMap D target) :
    (TauCeti.cellularChainBasis (relativeCWCarrier B) R q).repr
        (TauCeti.cellularChainGroupMap (relativeCWCarrier A) (relativeCWCarrier B)
          (relativeCWMap_cellular A B f hf base) (ModuleCat.of R R) q
          (TauCeti.cellularChainBasis (relativeCWCarrier A) R q i)) j =
      if target = j.val then 1 else 0 := by
  by_cases absorbed : target ∈ B.I q
  · rw [relativeCWChainGroupMap_basis_absorbed C D A B f hf base R q
      i target absorbed characteristic, map_zero]
    have different : target ≠ j.val := fun equal => j.property (equal ▸ absorbed)
    rw [if_neg different]
    rfl
  · rw [relativeCWChainGroupMap_basis_survives C D A B f hf base R q
      i ⟨target, absorbed⟩ characteristic, Module.Basis.repr_self, Finsupp.single_apply]
    have equal : (⟨target, absorbed⟩ : cell (relativeCWCarrier B) q) = j ↔ target = j.val :=
      Subtype.ext_iff
    simp only [equal]

end ToricPower
