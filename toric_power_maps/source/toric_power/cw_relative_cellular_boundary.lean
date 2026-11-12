module

public import ToricPower.CWRelativeCellularMap
public import ToricPower.CellularIncidenceNaturality

/-!
# The actual cellular quotient by a subcomplex

The ambient identity maps the absolute CW complex to its relative pair.
It preserves the original characteristic disks of the remaining cells,
and the disks of cells in the base factor through the relative base.
Consequently the induced cellular map keeps the surviving generators
and kills exactly the generators absorbed by the base.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits Topology Topology.RelCWComplex Set
open scoped Classical

namespace ToricPower

universe w

variable {X : Type w} [TopologicalSpace X] [T2Space X]
  (C : Set X) [CWComplex C] (A : CWComplex.Subcomplex C)

/-- The actual ambient identity, read as a map to the relative pair. -/
def absoluteToRelativeCWMap : TopCat.of C ⟶ TopCat.of (relativeCWCarrier A) := 𝟙 _

theorem absoluteToRelativeCWMap_cellular :
    TauCeti.IsCellular C (relativeCWCarrier A) (absoluteToRelativeCWMap C A) := by
  intro n x hx
  obtain ⟨d, lower, i, point⟩ := CWComplex.mem_skeletonLT_iff.mp hx
  by_cases absorbed : i ∈ A.I d
  · exact RelCWComplex.mem_skeletonLT_iff.mpr
      (Or.inl (A.openCell_subset_of_mem absorbed point))
  · exact RelCWComplex.mem_skeletonLT_iff.mpr
      (Or.inr ⟨d, lower, ⟨i, absorbed⟩, point⟩)

/-- A surviving characteristic disk is unchanged by the actual quotient
of the base. In particular, its orientation is unchanged. -/
theorem absoluteToRelative_characteristic {n : ℕ}
    (i : Topology.RelCWComplex.cell (relativeCWCarrier A) n) :
    TauCeti.characteristicCellPairMap C i.val ≫
        TauCeti.skeletonPairMap C (relativeCWCarrier A)
          (absoluteToRelativeCWMap_cellular C A) n =
      TauCeti.characteristicCellPairMap (relativeCWCarrier A) i := by
  apply TopPair.hom_ext_of_fst
  rw [TopPair.Hom.fst_comp, TauCeti.skeletonPairMap_fst]
  ext z
  erw [ConcreteCategory.comp_apply]
  apply Subtype.ext
  let p : TauCeti.skeletonObj C (n + 1) :=
    TopPair.Hom.fst (TauCeti.characteristicCellPairMap C i.val) z
  have point := congrArg Subtype.val
    (TauCeti.skeletonMap_apply C (relativeCWCarrier A)
      (absoluteToRelativeCWMap_cellular C A) (n + 1) p)
  change _ = (p : X) at point
  refine point.trans ?_
  change (TopPair.Hom.fst (TauCeti.characteristicCellPairMap C i.val) z).val =
    (TopPair.Hom.fst (TauCeti.characteristicCellPairMap (relativeCWCarrier A) i) z).val
  erw [TauCeti.coe_characteristicCellPairMap_fst_apply,
    TauCeti.coe_characteristicCellPairMap_fst_apply]
  rfl

/-- The whole characteristic disk of a base cell lies in the actual
subcomplex, including its boundary. -/
theorem characteristicCellPairMap_mem_base {n : ℕ} (i : cell C n) (member : i ∈ A.I n)
    (z : TopCat.disk.{w} n) :
    (TopPair.Hom.fst (TauCeti.characteristicCellPairMap C i) z).val ∈ (A : Set X) := by
  apply A.closedCell_subset_of_mem member
  erw [TauCeti.coe_characteristicCellPairMap_fst_apply]
  exact ⟨_, ((EuclideanSpace.equiv (Fin n) ℝ).image_unitBallHomeomorph_closedBall ▸
    Set.mem_image_of_mem _ z.down.2), rfl⟩

variable (R : Type w) [Ring R]

/-- A cell absorbed by the relative base gives the zero homology map,
because its actual characteristic map factors through the subspace. -/
theorem absoluteToRelative_characteristic_homology_zero {n : ℕ}
    (i : cell C n) (member : i ∈ A.I n) :
    TopPair.singularHomologyMap
      (TauCeti.characteristicCellPairMap C i ≫
        TauCeti.skeletonPairMap C (relativeCWCarrier A)
          (absoluteToRelativeCWMap_cellular C A) n) (ModuleCat.of R R) n = 0 := by
  let g : TopCat.disk.{w} n ⟶ TauCeti.skeletonObj (relativeCWCarrier A) n :=
    TopCat.ofHom
      ⟨fun z => ⟨(TopPair.Hom.fst (TauCeti.characteristicCellPairMap C i) z).val,
        RelCWComplex.mem_skeletonLT_iff.mpr
          (Or.inl (characteristicCellPairMap_mem_base C A i member z))⟩,
        (continuous_subtype_val.comp
          (TopPair.Hom.fst (TauCeti.characteristicCellPairMap C i)).hom.continuous).subtype_mk _⟩
  apply TopPair.singularHomologyMap_eq_zero_of_fac _ (ModuleCat.of R R) g
  ext z
  apply Subtype.ext
  rw [TopPair.Hom.fst_comp, TauCeti.skeletonPairMap_fst]
  erw [ConcreteCategory.comp_apply, ConcreteCategory.comp_apply]
  exact (congrArg Subtype.val (TauCeti.skeletonMap_apply C (relativeCWCarrier A)
    (absoluteToRelativeCWMap_cellular C A) (n + 1)
      (TopPair.Hom.fst (TauCeti.characteristicCellPairMap C i) z))).symm

/-- The genuine relative quotient keeps a surviving cellular basis
vector with its original characteristic-disk orientation. -/
theorem absoluteToRelative_basis_survives {n : ℕ}
    (i : Topology.RelCWComplex.cell (relativeCWCarrier A) n) :
    TauCeti.cellularChainGroupMap C (relativeCWCarrier A)
        (absoluteToRelativeCWMap_cellular C A) (ModuleCat.of R R) n
        (TauCeti.cellularChainBasis C R n i.val) =
      TauCeti.cellularChainBasis (relativeCWCarrier A) R n i :=
  cellularChainGroupMap_basis_of_characteristic C (relativeCWCarrier A)
    (absoluteToRelativeCWMap_cellular C A) R i.val i (absoluteToRelative_characteristic C A i)

/-- The genuine relative quotient kills the cellular generators in the
base, by the preceding actual factorization of characteristic maps. -/
theorem absoluteToRelative_basis_absorbed {n : ℕ} (i : cell C n) (member : i ∈ A.I n) :
    TauCeti.cellularChainGroupMap C (relativeCWCarrier A)
        (absoluteToRelativeCWMap_cellular C A) (ModuleCat.of R R) n
        (TauCeti.cellularChainBasis C R n i) = 0 := by
  rw [TauCeti.cellularChainBasis_apply, ← ModuleCat.comp_apply,
    ← ModuleCat.comp_apply,
    TauCeti.ι_cellularChainGroupIso_inv_eq_singularHomologyMap_characteristicCellPairMap_assoc,
    TauCeti.cellularChainGroupMap_def,
    ← TopPair.singularHomologyMap_comp,
    absoluteToRelative_characteristic_homology_zero C A R i member, comp_zero]
  rfl

/-- In the actual characteristic-disk bases, the relative quotient
simply restricts coordinates to cells outside the base. -/
theorem absoluteToRelative_coordinates (n : ℕ)
    (v : (TauCeti.cellularChainGroup C (ModuleCat.of R R) n : ModuleCat R)) :
    (TauCeti.cellularChainBasis (relativeCWCarrier A) R n).repr
        (TauCeti.cellularChainGroupMap C (relativeCWCarrier A)
          (absoluteToRelativeCWMap_cellular C A) (ModuleCat.of R R) n v) =
      Finsupp.subtypeDomain (fun i => i ∉ A.I n)
        ((TauCeti.cellularChainBasis C R n).repr v) := by
  have linear :
      (TauCeti.cellularChainBasis (relativeCWCarrier A) R n).repr.toLinearMap.comp
          (TauCeti.cellularChainGroupMap C (relativeCWCarrier A)
            (absoluteToRelativeCWMap_cellular C A) (ModuleCat.of R R) n).hom =
        (Finsupp.lsubtypeDomain (R := R) (M := R) {i : cell C n | i ∉ A.I n}).comp
          (TauCeti.cellularChainBasis C R n).repr.toLinearMap := by
    apply (TauCeti.cellularChainBasis C R n).ext
    intro j
    change (TauCeti.cellularChainBasis (relativeCWCarrier A) R n).repr
        (TauCeti.cellularChainGroupMap C (relativeCWCarrier A)
          (absoluteToRelativeCWMap_cellular C A) (ModuleCat.of R R) n
          (TauCeti.cellularChainBasis C R n j)) =
      (Finsupp.lsubtypeDomain (R := R) (M := R) {i : cell C n | i ∉ A.I n})
        ((TauCeti.cellularChainBasis C R n).repr (TauCeti.cellularChainBasis C R n j))
    by_cases member : j ∈ A.I n
    · rw [absoluteToRelative_basis_absorbed C A R j member, map_zero,
        Module.Basis.repr_self]
      ext i
      have different : j ≠ i.val := fun equal => i.property (equal ▸ member)
      change (0 : R) = Finsupp.single j (1 : R) i.val
      rw [Finsupp.single_apply, if_neg different]
    · rw [absoluteToRelative_basis_survives C A R ⟨j, member⟩,
        Module.Basis.repr_self, Module.Basis.repr_self]
      ext i
      change Finsupp.single (⟨j, member⟩ : cell (relativeCWCarrier A) n) (1 : R) i =
        Finsupp.single j (1 : R) i.val
      rw [Finsupp.single_apply, Finsupp.single_apply]
      have same : (⟨j, member⟩ : cell (relativeCWCarrier A) n) = i ↔ j = i.val :=
        Subtype.ext_iff
      simp only [same]
  exact LinearMap.congr_fun linear v

/-- The relative cellular boundary is the actual absolute boundary with
the base rows removed. It retains every surviving incidence coefficient. -/
theorem relativeCellularBoundaryColumn (n : ℕ)
    (j : cell (relativeCWCarrier A) (n + 1)) :
    TauCeti.cellularBoundaryColumn (relativeCWCarrier A) R n j =
      Finsupp.subtypeDomain (fun i => i ∉ A.I n)
        (TauCeti.cellularBoundaryColumn C R n j.val) := by
  have square := ConcreteCategory.congr_hom
    (TauCeti.cellularChainGroupMap_comp_cellularDifferential C (relativeCWCarrier A)
      (absoluteToRelativeCWMap_cellular C A) (ModuleCat.of R R) n)
    (TauCeti.cellularChainBasis C R (n + 1) j.val)
  simp only [ConcreteCategory.comp_apply, absoluteToRelative_basis_survives C A R j] at square
  rw [TauCeti.cellularBoundaryColumn_def, square, absoluteToRelative_coordinates,
    TauCeti.cellularBoundaryColumn_def]

/-- Every actual relative incidence coefficient is exactly the ambient
coefficient between the same two original characteristic cells. -/
theorem relativeCellularIncidence (n : ℕ)
    (i : cell (relativeCWCarrier A) n) (j : cell (relativeCWCarrier A) (n + 1)) :
    TauCeti.cellularIncidence (relativeCWCarrier A) R n i j =
      TauCeti.cellularIncidence C R n i.val j.val := by
  have equality := congrArg (fun f => f i) (relativeCellularBoundaryColumn C A R n j)
  change TauCeti.cellularBoundaryColumn (relativeCWCarrier A) R n j i =
    TauCeti.cellularBoundaryColumn C R n j.val i.val at equality
  exact (TauCeti.cellularBoundaryColumn_apply (relativeCWCarrier A) R n i j).symm.trans
    (equality.trans (TauCeti.cellularBoundaryColumn_apply C R n i.val j.val))

end ToricPower
