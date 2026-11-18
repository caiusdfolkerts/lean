module

public import PaperVerification.LatticeTranslations
public import Mathlib.GroupTheory.QuotientGroup.Basic
public import Mathlib.SetTheory.Cardinal.Finite


@[expose] public section
/-! # Translation classes of actual deep holes

The quotient is taken in the ambient real additive group by the actual lattice
subgroup, and then restricted to classes containing a deepest point.
-/

noncomputable section

namespace PaperVerification.ColdSpots

def DeepTranslationClasses {n : ℕ} (L : AddSubgroup (Fin n → ℝ)) :=
  {C : (Fin n → ℝ) ⧸ L // ∃ x : Fin n → ℝ, IsDeepHole (L : Set _) x ∧
    (x : (Fin n → ℝ) ⧸ L) = C}

end PaperVerification.ColdSpots
