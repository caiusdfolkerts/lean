module

public import ToricPower.ArrangementRepresentedAllWeightMap
public import ToricPower.DualDiagonalFramedTopGenerators

/-!
# Every original weight inclusion in the full represented comparison

The unrestricted coproduct construction retains its original inclusions.
The identity below is an equality of whole complex maps: each original
represented character maps by the specified relative-cell comparison
into exactly the translated total character of the genuine dual kernel.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits
open scoped Classical

namespace ToricPower.IntegralArrangement

variable {n s : ℕ} (A : Fin s → Fin n → ℤ) (S : Set (Fin s))
  (c : IncidenceObject A) (rightFrame : Fin n → ℤ)
  (frame : ∀ i ∈ S, rayPairing A rightFrame i = -c.2.val.val.1 (.inl i))
  (k : Type) [Field k]

/-- The actual full-character inclusion, through the original Laurent
complex's proved decomposition. -/
def representedLaurentWeightInclusion (m : Fin n → ℤ) :
    representedWeightCellularComplex A S c m k ⟶
      representableLaurentCellularComplex A S k c :=
  ModuleDirectSum.complexInclusion k
      (fun u => representedWeightCellularComplex A S c u k) m ≫
    (representableCellularWeightSumIso A S c k).inv

@[reassoc]
theorem dualDiagonalTranslatedWeightColimitIso_inclusion (m : Fin n → ℤ) :
    colimit.ι (Discrete.functor (fun u : Fin n → ℤ =>
        dualDiagonalWeightComplex A S S (u + rightFrame) k)) ⟨m⟩ ≫
      (dualDiagonalTranslatedWeightColimitIso A S rightFrame k).hom =
    colimit.ι (Discrete.functor (fun u : Fin n → ℤ =>
      dualDiagonalWeightComplex A S S u k)) ⟨m + rightFrame⟩ := by
  have inclusion := (HasColimit.ι_isoOfEquivalence_hom
      (F := Discrete.functor (fun u : Fin n → ℤ =>
        dualDiagonalWeightComplex A S S (u + rightFrame) k))
      (G := Discrete.functor (fun u : Fin n → ℤ =>
        dualDiagonalWeightComplex A S S u k))
      (Discrete.equivalence (Equiv.addRight rightFrame))
      (Discrete.natIso (fun _ => Iso.refl _))
      (⟨m⟩ : Discrete (Fin n → ℤ)))
  simp only [Discrete.natIso_hom_app, Discrete.natIso_inv_app,
    Iso.refl_hom, Iso.refl_inv] at inclusion
  erw [Category.id_comp] at inclusion
  exact inclusion

/-- Literal compatibility of the entire comparison with each original
character. In particular the target character is exactly `m+rightFrame`. -/
@[reassoc]
theorem representedLaurentDualKernelMap_weightInclusion
    (frames : ∀ q, DiagonalCellFrames A S S q) (m : Fin n → ℤ) :
    representedLaurentWeightInclusion A S c k m ≫
        representedLaurentDualKernelMap A S c rightFrame frame k frames =
      representedWeightDualStripMap A S c m rightFrame frame k ≫
        diagonalFramedDualWeightInclusion k A S S frames (m + rightFrame) := by
  simp only [representedLaurentWeightInclusion, representedLaurentDualKernelMap,
    Category.assoc, Iso.inv_hom_id_assoc,
    ModuleDirectSum.complexColimitIso_inclusion_assoc, colimit.ι_map_assoc]
  change representedWeightDualStripMap A S c m rightFrame frame k ≫
      colimit.ι (Discrete.functor (fun u : Fin n → ℤ =>
        dualDiagonalWeightComplex A S S (u + rightFrame) k)) ⟨m⟩ ≫
      (dualDiagonalTranslatedWeightColimitIso A S rightFrame k).hom ≫
      (ModuleDirectSum.complexColimitIso k
        (fun u => dualDiagonalWeightComplex A S S u k)).inv ≫
      (diagonalFramedDualAllWeightIso k A S S frames).inv = _
  rw [dualDiagonalTranslatedWeightColimitIso_inclusion_assoc]
  rw [← ModuleDirectSum.complexColimitIso_inclusion]
  simp only [Category.assoc, Iso.hom_inv_id_assoc]
  rfl

end ToricPower.IntegralArrangement

end
