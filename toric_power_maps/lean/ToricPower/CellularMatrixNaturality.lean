module

public import ToricPower.CellularIncidenceNaturality

/-!
# Cellular coordinates under maps which preserve characteristic disks

The cell map need not be bijective.  This version is needed for a chart
monomial, which sends a weight strip into a possibly larger strip.
The whole boundary column, including the vanishing of every coefficient
outside the image, is transported by an actual cellular map.

Candidate until ordinary checking of the cellular dependency closure.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Topology Topology.RelCWComplex
open scoped Classical

namespace ToricPower

universe w

variable {X Y : Type w} [TopologicalSpace X] [T2Space X]
  [TopologicalSpace Y] [T2Space Y] {D : Set X} {E : Set Y}
  (C : Set X) [RelCWComplex C D] (C' : Set Y) [RelCWComplex C' E]
  {f : TopCat.of C ⟶ TopCat.of C'} (hf : TauCeti.IsCellular C C' f)
  (R : Type w) [Ring R]
  (g : ∀ d, cell C d → cell C' d)
  (hχ : ∀ d j, TauCeti.characteristicCellPairMap C j ≫
      TauCeti.skeletonPairMap C C' hf d =
        TauCeti.characteristicCellPairMap C' (g d j))

include hf hχ

/-- Coordinates of the actual cellular map are the pushforward of the
finite-support coefficient function along the actual cell map. -/
theorem cellularChainGroupMap_coordinates_of_map
    (d : ℕ) (v : (TauCeti.cellularChainGroup C (ModuleCat.of R R) d : ModuleCat R)) :
    (TauCeti.cellularChainBasis C' R d).repr
      (TauCeti.cellularChainGroupMap C C' hf (ModuleCat.of R R) d v) =
        Finsupp.mapDomain (g d) ((TauCeti.cellularChainBasis C R d).repr v) := by
  have hlin :
      (TauCeti.cellularChainBasis C' R d).repr.toLinearMap.comp
        (TauCeti.cellularChainGroupMap C C' hf (ModuleCat.of R R) d).hom =
      (Finsupp.lmapDomain R R (g d)).comp
        (TauCeti.cellularChainBasis C R d).repr.toLinearMap := by
    apply (TauCeti.cellularChainBasis C R d).ext
    intro j
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe,
      cellularChainGroupMap_basis_of_characteristic C C' hf R j (g d j) (hχ d j),
      Module.Basis.repr_self, Finsupp.lmapDomain_apply, Finsupp.mapDomain_single]
  exact DFunLike.congr_fun hlin v

/-- Naturality of the actual differential transports an entire boundary
column; no support or incidence assumption is added to the construction. -/
theorem cellularBoundaryColumn_naturality (d : ℕ) (j : cell C (d+1)) :
    TauCeti.cellularBoundaryColumn C' R d (g (d+1) j) =
      Finsupp.mapDomain (g d) (TauCeti.cellularBoundaryColumn C R d j) := by
  have hd := ConcreteCategory.congr_hom
    (TauCeti.cellularChainGroupMap_comp_cellularDifferential C C' hf
      (ModuleCat.of R R) d) (TauCeti.cellularChainBasis C R (d+1) j)
  simp only [ConcreteCategory.comp_apply,
    cellularChainGroupMap_basis_of_characteristic C C' hf R j
      (g (d+1) j) (hχ (d+1) j)] at hd
  rw [TauCeti.cellularBoundaryColumn_def, hd,
    cellularChainGroupMap_coordinates_of_map C C' hf R g hχ,
    TauCeti.cellularBoundaryColumn_def]

end ToricPower
