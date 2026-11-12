module

public import ToricPower.DualDiagonalTranslatedSupport
public import ToricPower.ArrangementWeightCostalkComparison

/-!
# The actual costalk-to-dual-strip map of a representable character

The source is the literal bounded open star cut out by the monomial
inequalities. Translation by the negative character puts it in the full
dual strip, with total weight equal to that character plus the right
Cartier frame. The original relative cellular map therefore computes
the actual dual-strip complex, preserving the fixed ambient top class.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits Set
open scoped Classical

namespace ToricPower.IntegralArrangement

variable {n s : ℕ} (A : Fin s → Fin n → ℤ) (S : Set (Fin s))
  (c : IncidenceObject A) (m : Fin n → ℤ)

/-- The literal geometric support of this arbitrary integral character. -/
def representedCostalkSupport : OpenCellSupport A :=
  ⟨⟨costalkRegion (augmentedForms A) (Sum.inl '' S)
      (augmentedLatticePairing A m) (incidenceCellCenter A c),
    costalkRegion_isOpen _ _ _ _⟩, costalkRegion_cellwise _ _ _ _⟩

/-- Coordinate augmentation bounds this actual costalk, independently
of the selected toric ray set and of the character. -/
theorem representedCostalkSupport_bounded :
    Bornology.IsBounded ((representedCostalkSupport A S c m).val : Set (Fin n → ℝ)) :=
  augmentedCostalkRegion_bounded A _ _ _

variable (rightFrame : Fin n → ℤ)
  (frame : ∀ i ∈ S, rayPairing A rightFrame i = -c.2.val.val.1 (.inl i))

include frame in
/-- These are the exact two strict strip inequalities. The lower one
comes from the original open star and the literal right-label frame. -/
theorem representedCostalkSupport_translated_subset :
    translatedRegion ((representedCostalkSupport A S c m).val : Set (Fin n → ℝ))
      (latticeLift (-m)) ⊆ dualDiagonalStrip A S S (m + rightFrame) := by
  have lift (z : Fin n → ℤ) (i : Fin s) :
      integralRowForm A i (latticeLift z) = (rayPairing A z i : ℝ) :=
    augmentedForms_latticeLift A z (.inl i)
  rintro _ ⟨x, hx, rfl⟩
  constructor
  · intro i hi
    have upper := hx.2 (.inl i) ⟨i, hi, rfl⟩
    change integralRowForm A i x < (rayPairing A m i : ℝ) + 1 at upper
    rw [map_add, lift]
    have negative : rayPairing A (-m) i = -rayPairing A m i := by
      simpa using rayPairing_sub A 0 m i
    rw [negative, Int.cast_neg]
    linarith
  · intro i hi
    have lower := (hx.1 (.inl i)).1
    change (⌈augmentedForms A (.inl i) (cellCenter (augmentedForms A) c.2.val)⌉ : ℝ) - 1 <
      integralRowForm A i x at lower
    rw [ceil_eq_of_mem_cell (augmentedForms A) _ _
      (cellCenter_mem (augmentedForms A) c.2.val) (.inl i)] at lower
    change (c.2.val.val.1 (.inl i) : ℝ) - 1 < integralRowForm A i x at lower
    rw [map_add, lift, rayPairing_add, frame i hi]
    have negative : rayPairing A (-m) i = -rayPairing A m i := by
      simpa using rayPairing_sub A 0 m i
    rw [negative, Int.cast_add, Int.cast_neg, Int.cast_neg]
    linarith

/-- The bounded source enters one actual window of the full strip. -/
def representedCostalkWindow : ℕ :=
  (translatedSupport_exists_dualDiagonalWindow A S S (m + rightFrame)
    (representedCostalkSupport A S c m) (-m)
    (representedCostalkSupport_bounded A S c m)
    (representedCostalkSupport_translated_subset A S c m rightFrame frame)).choose

theorem representedCostalkWindow_contains :
    translatedRegion ((representedCostalkSupport A S c m).val : Set (Fin n → ℝ))
      (latticeLift (-m)) ⊆ dualDiagonalWindow A S S (m + rightFrame)
        (representedCostalkWindow A S c m rightFrame frame) :=
  (translatedSupport_exists_dualDiagonalWindow A S S (m + rightFrame)
    (representedCostalkSupport A S c m) (-m)
    (representedCostalkSupport_bounded A S c m)
    (representedCostalkSupport_translated_subset A S c m rightFrame frame)).choose_spec

variable (k : Type) [Field k]

/-- Both sides use the very same relative CW structure and scalar dual. -/
def representedCostalkOpenSupportIso :
    periodicCostalkCochainComplex A (Sum.inl '' S) (augmentedLatticePairing A m)
        (incidenceCellCenter A c) k ≅
      openSupportCochainComplex A k (representedCostalkSupport A S c m) := Iso.refl _

/-- The whole original character complex, with its independently
verified differential, maps into the original full dual strip. -/
def representedWeightDualStripMap :
    representedWeightCellularComplex A S c m k ⟶
      dualDiagonalWeightComplex A S S (m + rightFrame) k :=
  (representedWeightCostalkComplexIso A S c m k).hom ≫
    (representableCostalkCochainIso k A c S m).hom ≫
      (representedCostalkOpenSupportIso A S c m k).hom ≫
        dualDiagonalTranslatedSupportMap A S S (m + rightFrame)
          (representedCostalkSupport A S c m) (-m) k
          (representedCostalkWindow A S c m rightFrame frame)
          (representedCostalkWindow_contains A S c m rightFrame frame)

/-- Every permitted character is computed by this specified map; the
character is arbitrary and the target strip need not be bounded. -/
theorem representedWeightDualStripMap_quasiIso
    (nonempty : ((representedCostalkSupport A S c m).val : Set (Fin n → ℝ)).Nonempty) :
    QuasiIso (representedWeightDualStripMap A S c m rightFrame frame k) := by
  haveI := dualDiagonalTranslatedSupportMap_quasiIso A S S (m + rightFrame)
    (representedCostalkSupport A S c m) (-m) k
    (representedCostalkWindow A S c m rightFrame frame)
    (representedCostalkWindow_contains A S c m rightFrame frame)
    (costalkRegion_convex _ _ _ _) nonempty
    (representedCostalkSupport_bounded A S c m)
  unfold representedWeightDualStripMap
  infer_instance

end ToricPower.IntegralArrangement

end
