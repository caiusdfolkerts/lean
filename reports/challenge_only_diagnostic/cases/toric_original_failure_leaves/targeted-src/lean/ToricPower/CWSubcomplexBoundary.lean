module

public import ToricPower.CWSubcomplexInclusion

/-! # The original incidence coefficients inside a closed subcomplex

The comparison is induced by the actual cellular inclusion and its
preserved characteristic disks. In particular, the subcomplex boundary
has the original ambient signs; no independent boundary is assigned.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits Topology Topology.RelCWComplex Set

namespace ToricPower

universe w

variable {X : Type w} [TopologicalSpace X] [T2Space X]
  {C : Set X} [CWComplex C] (S : CWComplex.Subcomplex C)
  (R : Type w) [Ring R]

theorem subcomplexInclusion_coordinates (q : ℕ)
    (v : (TauCeti.cellularChainGroup (S : Set X) (ModuleCat.of R R) q : ModuleCat R)) :
    (TauCeti.cellularChainBasis C R q).repr
        (TauCeti.cellularChainGroupMap (S : Set X) C (subcomplexInclusion_cellular S)
          (ModuleCat.of R R) q v) =
      Finsupp.mapDomain (Subtype.val : S.I q → cell C q)
        ((TauCeti.cellularChainBasis (S : Set X) R q).repr v) := by
  have linear :
      (TauCeti.cellularChainBasis C R q).repr.toLinearMap.comp
        (TauCeti.cellularChainGroupMap (S : Set X) C (subcomplexInclusion_cellular S)
          (ModuleCat.of R R) q).hom =
        (Finsupp.lmapDomain (R := R) (M := R) (Subtype.val : S.I q → cell C q)).comp
          (TauCeti.cellularChainBasis (S : Set X) R q).repr.toLinearMap := by
    apply (TauCeti.cellularChainBasis (S : Set X) R q).ext
    intro j
    change (TauCeti.cellularChainBasis C R q).repr
      (TauCeti.cellularChainGroupMap (S : Set X) C (subcomplexInclusion_cellular S)
        (ModuleCat.of R R) q (TauCeti.cellularChainBasis (S : Set X) R q j)) = _
    rw [subcomplexInclusion_chainGenerator,Module.Basis.repr_self]
    change Finsupp.single j.val (1 : R) =
      Finsupp.mapDomain Subtype.val
        ((TauCeti.cellularChainBasis (S : Set X) R q).repr
          (TauCeti.cellularChainBasis (S : Set X) R q j))
    rw [Module.Basis.repr_self,Finsupp.mapDomain_single]
  exact LinearMap.congr_fun linear v

theorem subcomplexBoundaryColumn (q : ℕ) (j : S.I (q+1)) :
    Finsupp.mapDomain (Subtype.val : S.I q → cell C q)
        (TauCeti.cellularBoundaryColumn (S : Set X) R q j) =
      TauCeti.cellularBoundaryColumn C R q j.val := by
  have square := ConcreteCategory.congr_hom
    (TauCeti.cellularChainGroupMap_comp_cellularDifferential (S : Set X) C
      (subcomplexInclusion_cellular S) (ModuleCat.of R R) q)
    (TauCeti.cellularChainBasis (S : Set X) R (q+1) j)
  simp only [ConcreteCategory.comp_apply,subcomplexInclusion_chainGenerator] at square
  rw [TauCeti.cellularBoundaryColumn_def,TauCeti.cellularBoundaryColumn_def,
    square,subcomplexInclusion_coordinates]

theorem subcomplexCellularIncidence (q : ℕ) (i : S.I q) (j : S.I (q+1)) :
    TauCeti.cellularIncidence (S : Set X) R q i j =
      TauCeti.cellularIncidence C R q i.val j.val := by
  have equality := congrArg (fun f => f i.val) (subcomplexBoundaryColumn S R q j)
  rw [Finsupp.mapDomain_apply_of_injective Subtype.val_injective] at equality
  exact (TauCeti.cellularBoundaryColumn_apply (S : Set X) R q i j).symm.trans
    (equality.trans (TauCeti.cellularBoundaryColumn_apply C R q i.val j.val))

end ToricPower

end
