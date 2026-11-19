module

public import ToricPower.ArrangementIncidenceLabels

/-!
# Finite global monomial columns of the cellular diagonal

Each normalized source cell has its actual finite cellular boundary in
the universal cover.  Reindexing that boundary by the proved lattice-orbit
equivalence gives finitely many pairs `(normalized target, translation)`.
Every supported term satisfies the global Cartier-morphism inequalities
for the character pair `(a,-a)`.

The module complex on each affine product chart was constructed separately
from actual weight complexes.  These columns provide its global line-bundle
matrix entries; equality with the chart complex still requires the natural
inclusion of each strip into the universal-cover CW complex.

Candidate until the complete dependency closure is checked by Lean.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Topology Topology.RelCWComplex
open scoped Classical

namespace ToricPower.IntegralArrangement

variable {n s : ℕ} (k : Type) [Ring k] (A : Fin s → Fin n → ℤ)

local instance diagonalGlobalColumnsPeriodicCW : CWComplex (arrangementCarrier A) :=
  periodicArrangementCWComplex A

/-- The actual finite boundary column of a normalized source cell,
indexed by normalized target cells and literal lattice translations. -/
def diagonalGlobalColumn (d : ℕ) (j : NormalizedCell A (d+1)) :
    (NormalizedCell A d × (Fin n → ℤ)) →₀ k :=
  (Finsupp.domLCongr (cellOrbitEquiv A d) :
    (Cell (augmentedForms A) d →₀ k) ≃ₗ[k]
      ((NormalizedCell A d × (Fin n → ℤ)) →₀ k))
    (TauCeti.cellularBoundaryColumn (arrangementCarrier A) k d j.val)

/-- Its coefficient is exactly the genuine cellular incidence of the
corresponding translated cell, with its actual chosen disk orientation. -/
theorem diagonalGlobalColumn_apply (d : ℕ) (j : NormalizedCell A (d+1))
    (i : NormalizedCell A d) (a : Fin n → ℤ) :
    diagonalGlobalColumn k A d j (i,a) =
      TauCeti.cellularIncidence (arrangementCarrier A) k d
        (translateCell A a i.val) j.val := by
  rw [diagonalGlobalColumn, Finsupp.domLCongr_apply,
    Finsupp.domCongr_apply, Finsupp.equivMapDomain_apply]
  exact TauCeti.cellularBoundaryColumn_apply _ _ _ _ _

/-- The indexing type of supported global monomial terms is finite by
construction from the actual finite-support cellular boundary. -/
abbrev DiagonalGlobalColumnTerm (d : ℕ) (j : NormalizedCell A (d+1)) :=
  {p : NormalizedCell A d × (Fin n → ℤ) // p ∈ (diagonalGlobalColumn k A d j).support}

instance diagonalGlobalColumnTerm_finite (d : ℕ) (j : NormalizedCell A (d+1)) :
    Finite (DiagonalGlobalColumnTerm k A d j) := by
  unfold DiagonalGlobalColumnTerm
  infer_instance

/-- Every actually supported global matrix term is regular between
the displayed two line-bundle factors at every ray of the original fan. -/
theorem diagonalGlobalColumnTerm_regular (d : ℕ) (j : NormalizedCell A (d+1))
    (p : DiagonalGlobalColumnTerm k A d j) (ρ : Fin s) :
    reflectedCeiling A p.val.1.val ρ - reflectedCeiling A j.val ρ ≤
        rayPairing A p.val.2 ρ ∧
      p.val.1.val.val.1 (.inl ρ) - j.val.val.1 (.inl ρ) ≤
        -rayPairing A p.val.2 ρ := by
  have hp := Finsupp.mem_support_iff.mp p.property
  rw [diagonalGlobalColumn_apply] at hp
  exact normalized_incidence_character_regular A k p.val.1 j p.val.2 hp ρ

end ToricPower.IntegralArrangement
