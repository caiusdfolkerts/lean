module

public import ToricPower.ArrangementRepresentedDualStrip

/-!
# Every character in the represented dual-strip comparison

A strictly positive direction for the selected cone identifies the empty
characters on the two sides. Consequently the specified geometric map
is a quasi-isomorphism for every integral character, including forbidden
characters. Actual toric cones provide this direction independently.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits Set
open scoped Classical

namespace ToricPower.IntegralArrangement

variable {n s : ℕ} (A : Fin s → Fin n → ℤ) (S : Set (Fin s))
  (c : IncidenceObject A) (m rightFrame : Fin n → ℤ)
  (frame : ∀ i ∈ S, rayPairing A rightFrame i = -c.2.val.val.1 (.inl i))
  (strictDirection : ∃ v : Fin n → ℝ, ∀ i ∈ Sum.inl '' S,
    0 < augmentedForms A i v)

include frame strictDirection in
/-- The literal source and target have exactly the same allowed weights. -/
theorem representedCostalkSupport_nonempty_iff_dualStrip :
    ((representedCostalkSupport A S c m).val : Set (Fin n → ℝ)).Nonempty ↔
      (dualDiagonalStrip A S S (m + rightFrame)).Nonempty := by
  constructor
  · rintro ⟨x, hx⟩
    exact ⟨x + latticeLift (-m),
      representedCostalkSupport_translated_subset A S c m rightFrame frame ⟨x, hx, rfl⟩⟩
  · rintro ⟨x, hx⟩
    apply (costalkRegion_nonempty_iff_integer (augmentedForms A) (Sum.inl '' S)
      (augmentedLatticePairing A m) (incidenceCellCenter A c) strictDirection).mpr
    rintro _ ⟨i, hi, rfl⟩
    change ⌈augmentedForms A (.inl i) (cellCenter (augmentedForms A) c.2.val)⌉ - 1 ≤
      rayPairing A m i
    rw [ceil_eq_of_mem_cell (augmentedForms A) _ _
      (cellCenter_mem (augmentedForms A) c.2.val) (.inl i)]
    change c.2.val.val.1 (.inl i) - 1 ≤ rayPairing A m i
    have upper := hx.1 i hi
    have lower := hx.2 i hi
    rw [rayPairing_add, frame i hi, Int.cast_add, Int.cast_neg] at lower
    have inequality : (c.2.val.val.1 (.inl i) : ℝ) - 2 <
        (rayPairing A m i : ℝ) := by linarith
    have integral : c.2.val.val.1 (.inl i) - 2 < rayPairing A m i := by
      exact_mod_cast inequality
    omega

include frame strictDirection in
/-- No permitted-character hypothesis remains on this actual chain map. -/
theorem representedWeightDualStripMap_quasiIso_all (k : Type) [Field k] :
    QuasiIso (representedWeightDualStripMap A S c m rightFrame frame k) := by
  by_cases nonempty : ((representedCostalkSupport A S c m).val : Set (Fin n → ℝ)).Nonempty
  · exact representedWeightDualStripMap_quasiIso A S c m rightFrame frame k nonempty
  · have empty : costalkRegion (augmentedForms A) (Sum.inl '' S)
        (augmentedLatticePairing A m) (incidenceCellCenter A c) = ∅ :=
      Set.not_nonempty_iff_eq_empty.mp nonempty
    have stripEmpty : dualDiagonalStrip A S S (m + rightFrame) = ∅ := by
      apply Set.not_nonempty_iff_eq_empty.mp
      exact fun h => nonempty
        ((representedCostalkSupport_nonempty_iff_dualStrip A S c m rightFrame
          frame strictDirection).mpr h)
    rw [quasiIso_iff]
    intro q
    rw [quasiIsoAt_iff_isIso_homologyMap]
    exact (representedWeightCellularComplex_isZero_homology_of_empty A S c m k empty q).isIso
      (dualDiagonalWeightComplex_isZero_homology_of_empty A S S (m + rightFrame) k stripEmpty q) _

end ToricPower.IntegralArrangement

end
