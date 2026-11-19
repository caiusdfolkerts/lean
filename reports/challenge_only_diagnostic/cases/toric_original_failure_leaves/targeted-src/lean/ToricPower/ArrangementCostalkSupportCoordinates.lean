module

public import ToricPower.ArrangementRepresentedDualStrip

/-!
# The same characteristic cells in the represented and open-support bases

The independently defined representable matrix and the genuine relative
CW complex use the same characteristic disks. This file identifies their
literal coordinates before taking homology. Consequently the specified
represented map into the full dual strip sends every generator to the
actual translated cell, with its original coefficient unchanged.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits Topology Set
open scoped Classical

namespace ToricPower.IntegralArrangement

variable {n s : ℕ} (A : Fin s → Fin n → ℤ) (S : Set (Fin s))
  (c : IncidenceObject A) (m : Fin n → ℤ)

local instance costalkSupportCoordinatesPeriodicCW : CWComplex (arrangementCarrier A) :=
  periodicArrangementCWComplex A

local notation "U" => representedCostalkSupport A S c m

/-- This is the original costalk indexing equivalence, with its source
displayed as the actual open-support cell subtype. -/
def representedCostalkSupportIndexEquiv (q : ℕ) :
    OpenSupportCell A U q ≃ RepresentableCostalkIndex A c S m q :=
  costalkCellIndexEquiv A c S m q

instance representedCostalkSupport_cellsFinite (q : ℕ) :
    Finite (OpenSupportCell A U q) :=
  Finite.of_equiv (RepresentableCostalkIndex A c S m q)
    (representedCostalkSupportIndexEquiv A S c m q).symm

variable (k : Type) [Field k]

/-- The two chain coordinate systems have literally the same
coefficient on each original characteristic cell. -/
theorem representedCostalkChainCoordinates_support (q : ℕ)
    (v : (openSupportChainComplex A (ModuleCat.of k k) U).X q)
    (d : OpenSupportCell A U q) :
    representableCostalkChainCoordinates A c S m k q v
        (representedCostalkSupportIndexEquiv A S c m q d) =
      openSupportChainCoordinates A k U q v d := by
  simp only [representableCostalkChainCoordinates, openSupportChainCoordinates,
    LinearEquiv.trans_apply, representableCostalkBasis, openSupportBasis,
    Module.Basis.repr_reindex_apply]
  change (TauCeti.cellularChainBasis
      (relativeCWCarrier (openSupportComplement A U)) k q).repr
      ((eqToIso (TauCeti.cellularChainComplex_X
        (relativeCWCarrier (openSupportComplement A U)) (ModuleCat.of k k) q)).hom v)
      ((periodicCostalkCellSupportEquiv A (Sum.inl '' S)
        (augmentedLatticePairing A m) (incidenceCellCenter A c) q).symm
        ((costalkCellIndexEquiv A c S m q).symm
          (costalkCellIndexEquiv A c S m q d))) = _
  rw [Equiv.symm_apply_apply]
  rfl

/-- The same statement on a single chain generator, including the
canonical skeletal term transports in both coordinate systems. -/
theorem representedCostalkChainCoordinates_support_single (q : ℕ)
    (d : OpenSupportCell A U q) (a : k) :
    representableCostalkChainCoordinates A c S m k q
        ((openSupportChainCoordinates A k U q).symm (Finsupp.single d a)) =
      Finsupp.single (representedCostalkSupportIndexEquiv A S c m q d) a := by
  ext p
  obtain ⟨e, rfl⟩ := (representedCostalkSupportIndexEquiv A S c m q).surjective p
  rw [representedCostalkChainCoordinates_support, LinearEquiv.apply_symm_apply]
  simp only [Finsupp.single_apply,
    (representedCostalkSupportIndexEquiv A S c m q).injective.eq_iff]

/-- Scalar duality retains the exact characteristic-cell coordinate;
this is the component of the actual chain isomorphism. -/
theorem representedCostalkCochainCoordinates_support_apply (q : ℕ)
    (φ : (representableCostalkCochainComplex k A c S m).X q)
    (d : OpenSupportCell A U q) :
    openSupportCochainCoordinates A k U q
        ((representedCostalkOpenSupportIso A S c m k).hom.f q
          ((representableCostalkCochainIso k A c S m).hom.f q φ)) d =
      representableCostalkCochainCoordinates k A c S m q φ
        (representedCostalkSupportIndexEquiv A S c m q d) := by
  change (ModuleCat.of k (RepresentableCostalkIndex A c S m q →₀ k) ⟶
    ModuleCat.of k k) at φ
  change φ
      (representableCostalkChainCoordinates A c S m k q
        ((openSupportChainCoordinates A k U q).symm (Finsupp.single d 1))) =
    φ (Finsupp.single (representedCostalkSupportIndexEquiv A S c m q d) 1)
  rw [representedCostalkChainCoordinates_support_single]

/-- The complete scalar cochain comparison is the actual reindexing
of these cells, with no choice of a cohomology basis. -/
theorem representedCostalkCochainCoordinates_support (q : ℕ)
    (φ : (representableCostalkCochainComplex k A c S m).X q) :
    openSupportCochainCoordinates A k U q
        ((representedCostalkOpenSupportIso A S c m k).hom.f q
          ((representableCostalkCochainIso k A c S m).hom.f q φ)) =
      Finsupp.mapDomain (representedCostalkSupportIndexEquiv A S c m q).symm
        (representableCostalkCochainCoordinates k A c S m q φ) := by
  ext d
  rw [representedCostalkCochainCoordinates_support_apply,
    Finsupp.mapDomain_equiv_apply, Equiv.symm_symm]

variable (rightFrame : Fin n → ℤ)
  (frame : ∀ i ∈ S, rayPairing A rightFrame i = -c.2.val.val.1 (.inl i))

/-- The literal dual-strip cell of a represented monomial generator. -/
def representedDualStripCell (q : ℕ) :
    RepresentableCostalkIndex A c S m q →
      DualDiagonalStripCell A S S (m + rightFrame) q :=
  dualDiagonalTranslatedSupportCell A S S (m + rightFrame) U (-m)
      (representedCostalkWindow A S c m rightFrame frame)
      (representedCostalkWindow_contains A S c m rightFrame frame) q ∘
    (representedCostalkSupportIndexEquiv A S c m q).symm

/-- The cell is exactly the normalized coface translated by the
negative full character `m + incidence`, as in the actual evaluation. -/
theorem representedDualStripCell_val (q : ℕ)
    (p : RepresentableCostalkIndex A c S m q) :
    (representedDualStripCell A S c m rightFrame frame q p).val =
      translateCell A (-(m + p.val.2.val)) p.val.1.val := by
  change translateCell A (-m)
      (translateCell A (-p.val.2.val) p.val.1.val) = _
  rw [translateCell_add]
  congr 1
  abel

/-- All coefficients of the original represented-to-strip map are
those of the literal translated characteristic cells. -/
theorem representedWeightDualStripMap_coordinates (q : ℕ)
    (v : (representedWeightCellularComplex A S c m k).X q) :
    dualDiagonalWeightCoordinates A S S (m + rightFrame) k q
        ((representedWeightDualStripMap A S c m rightFrame frame k).f q v) =
      Finsupp.mapDomain (representedDualStripCell A S c m rightFrame frame q)
        (representedWeightCellularCoordinates A S c m k q v) := by
  change dualDiagonalWeightCoordinates A S S (m + rightFrame) k q
      ((dualDiagonalTranslatedSupportMap A S S (m + rightFrame) U (-m) k
        (representedCostalkWindow A S c m rightFrame frame)
        (representedCostalkWindow_contains A S c m rightFrame frame)).f q
        ((representedCostalkOpenSupportIso A S c m k).hom.f q
          ((representableCostalkCochainIso k A c S m).hom.f q
            ((representedWeightCostalkComplexIso A S c m k).hom.f q v)))) = _
  rw [dualDiagonalTranslatedSupportMap_coordinates,
    representedCostalkCochainCoordinates_support, ← Finsupp.mapDomain_comp]
  change Finsupp.mapDomain (representedDualStripCell A S c m rightFrame frame q)
      ((representableCostalkCochainCoordinates k A c S m q)
        ((representableCostalkCochainCoordinates k A c S m q).symm
          (representedWeightCellularCoordinates A S c m k q v))) = _
  rw [LinearEquiv.apply_symm_apply]

end ToricPower.IntegralArrangement

end
