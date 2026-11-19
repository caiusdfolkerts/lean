module

public import ToricPower.CWRelativeCellularBasisMap
public import Mathlib.Topology.CWComplex.Classical.Subcomplex

/-! # The original characteristic disks under a subcomplex inclusion

The inclusion is a genuine cellular map. It preserves the entire
characteristic disk, and hence its original oriented chain generator.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Topology Topology.RelCWComplex Set

namespace ToricPower

universe w

variable {X : Type w} [TopologicalSpace X] [T2Space X]
  {C : Set X} [CWComplex C] (S : CWComplex.Subcomplex C)

def subcomplexInclusion : TopCat.of (S : Set X) ⟶ TopCat.of C :=
  TopCat.ofHom ⟨fun x => ⟨x.val,S.subset_complex x.property⟩,by fun_prop⟩

theorem subcomplexInclusion_cellular :
    TauCeti.IsCellular (S : Set X) C (subcomplexInclusion S) := by
  intro n x hx
  obtain inBase | ⟨q,below,j,point⟩ := RelCWComplex.mem_skeletonLT_iff.mp hx
  · exact inBase.elim
  · exact RelCWComplex.mem_skeletonLT_iff.mpr (Or.inr ⟨q,below,j.val,point⟩)

theorem subcomplexInclusion_skeleton_value (q : ℕ) (x : TauCeti.skeletonObj (S : Set X) q) :
    ((TauCeti.skeletonMap (S : Set X) C (subcomplexInclusion_cellular S) q).hom x).val =
      x.val := by
  exact congrArg (fun y : TauCeti.skeletonObj C q => y.val)
    (TauCeti.skeletonMap_apply (S : Set X) C (subcomplexInclusion_cellular S) q x)

theorem subcomplexInclusion_characteristic (q : ℕ) (j : S.I q) :
    TauCeti.characteristicCellPairMap (S : Set X) j ≫
        TauCeti.skeletonPairMap (S : Set X) C (subcomplexInclusion_cellular S) q =
      TauCeti.characteristicCellPairMap C j.val := by
  apply TopPair.hom_ext_of_fst
  ext x
  apply Subtype.ext
  change (TopPair.Hom.fst
    (TauCeti.skeletonPairMap (S : Set X) C (subcomplexInclusion_cellular S) q)
      (TopPair.Hom.fst (TauCeti.characteristicCellPairMap (S : Set X) j) x)).val = _
  rw [TauCeti.skeletonPairMap_fst]
  refine (subcomplexInclusion_skeleton_value S (q+1) _).trans ?_
  exact (TauCeti.coe_characteristicCellPairMap_fst_apply (S : Set X) j x).trans
    (TauCeti.coe_characteristicCellPairMap_fst_apply C j.val x).symm

theorem subcomplexInclusion_chainGenerator (R : Type w) [Ring R]
    (q : ℕ) (j : S.I q) :
    TauCeti.cellularChainGroupMap (S : Set X) C (subcomplexInclusion_cellular S)
        (ModuleCat.of R R) q (TauCeti.cellularChainBasis (S : Set X) R q j) =
      TauCeti.cellularChainBasis C R q j.val :=
  cellularChainGroupMap_basis_of_characteristic (S : Set X) C
    (subcomplexInclusion_cellular S) R j j.val
    (subcomplexInclusion_characteristic S q j)

end ToricPower

end
