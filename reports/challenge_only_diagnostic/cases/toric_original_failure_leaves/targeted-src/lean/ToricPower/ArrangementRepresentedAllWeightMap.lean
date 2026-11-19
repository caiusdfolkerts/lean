module

public import ToricPower.ArrangementRepresentedDualStripExact
public import ToricPower.ArrangementLaurentWeightSum
public import ToricPower.DualDiagonalFramedWeightDecomposition
public import ToricPower.ExactComplexCoproducts

/-!
# The complete represented Laurent complex maps to the actual dual kernel

Every character is retained. The character maps are the specified
translated relative-cell maps; their unrestricted coproduct is exact,
and translation by the actual right frame simply reindexes all lattice
characters. The target is the scalar restriction of the original
ring-linear dual diagonal complex.

The sheaf augmentation comparison is a separate map calculation. This
file supplies its actual full-complex geometric comparison, with no
finite weight truncation.
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

/-- The original relative-cell map in every character. -/
def representedDualStripFamilyMap :
    Discrete.functor (fun m => representedWeightCellularComplex A S c m k) ⟶
      Discrete.functor (fun m => dualDiagonalWeightComplex A S S (m + rightFrame) k) :=
  Discrete.natTrans (fun m => representedWeightDualStripMap A S c m.as rightFrame frame k)

/-- Translation reindexes the entire lattice, including all empty fibers. -/
def dualDiagonalTranslatedWeightColimitIso :
    colimit (Discrete.functor (fun m : Fin n → ℤ =>
      dualDiagonalWeightComplex A S S (m + rightFrame) k)) ≅
        colimit (Discrete.functor (fun u : Fin n → ℤ =>
          dualDiagonalWeightComplex A S S u k)) :=
  HasColimit.isoOfEquivalence
    (Discrete.equivalence (Equiv.addRight rightFrame))
    (Discrete.natIso (fun _ => Iso.refl _))

/-- This specified map uses the full original coefficient complex and
lands in the scalar restriction of the genuine ring-linear dual kernel. -/
def representedLaurentDualKernelMap
    (frames : ∀ q, DiagonalCellFrames A S S q) :
    representableLaurentCellularComplex A S k c ⟶
      diagonalFramedDualScalarComplex k A S S frames :=
  (representableCellularWeightSumIso A S c k).hom ≫
    (ModuleDirectSum.complexColimitIso k
      (fun m => representedWeightCellularComplex A S c m k)).hom ≫
    colim.map (representedDualStripFamilyMap A S c rightFrame frame k) ≫
    (dualDiagonalTranslatedWeightColimitIso A S rightFrame k).hom ≫
    (ModuleDirectSum.complexColimitIso k
      (fun u => dualDiagonalWeightComplex A S S u k)).inv ≫
    (diagonalFramedDualAllWeightIso k A S S frames).inv

/-- The complete map is a quasi-isomorphism for unrestricted characters;
no finite-dimensional condition is imposed on any term. -/
theorem representedLaurentDualKernelMap_quasiIso
    (frames : ∀ q, DiagonalCellFrames A S S q)
    (strictDirection : ∃ v : Fin n → ℝ, ∀ i ∈ Sum.inl '' S,
      0 < augmentedForms A i v) :
    QuasiIso (representedLaurentDualKernelMap A S c rightFrame frame k frames) := by
  letI (m : Discrete (Fin n → ℤ)) :
      QuasiIso ((representedDualStripFamilyMap A S c rightFrame frame k).app m) :=
    representedWeightDualStripMap_quasiIso_all A S c m.as rightFrame frame strictDirection k
  haveI := ToricPower.complex_colimitMap_quasiIso
    (representedDualStripFamilyMap A S c rightFrame frame k)
  unfold representedLaurentDualKernelMap
  infer_instance

end ToricPower.IntegralArrangement

end
