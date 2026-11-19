module

public import ToricPower.CellularVertexAugmentation
public import ToricPower.DiagonalGlobalColumns

/-!
# The exact scalar cancellation in the global augmentation

The global boundary retains every translated incidence in the universal
cover. Reindexing does not change the total coefficient, and the actual
cellular augmentation sends each vertex to one and kills the differential.
Consequently every genuine global degree-one column has coefficient sum
zero, including when several translated incidences have the same normalized
target. This is the scalar identity used by the actual global augmentation.

Candidate source pending compilation.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Topology Topology.RelCWComplex
open scoped Classical BigOperators

namespace ToricPower.IntegralArrangement

variable {n s : ℕ} (k : Type) [CommRing k] (A : Fin s → Fin n → ℤ)

local instance diagonalAugmentationScalarsPeriodicCW : CWComplex (arrangementCarrier A) :=
  periodicArrangementCWComplex A

/-- The sum of the actual degree-one global column, before collecting
any translated incidences, is exactly zero. -/
theorem diagonalGlobalColumn_zero_sum (j : NormalizedCell A 1) :
    (diagonalGlobalColumn k A 0 j).sum (fun _ r => r) = 0 := by
  rw [diagonalGlobalColumn,Finsupp.domLCongr_apply,Finsupp.domCongr_apply,
    Finsupp.equivMapDomain_eq_mapDomain,
    Finsupp.sum_mapDomain_index (fun _ => rfl) (fun _ _ _ => rfl)]
  exact ToricPower.cellularBoundaryColumn_sum_zero
    (k := k) (arrangementCarrier A) j.val

theorem diagonalGlobalColumn_support_sum_zero (j : NormalizedCell A 1) :
    ∑ p ∈ (diagonalGlobalColumn k A 0 j).support,
      diagonalGlobalColumn k A 0 j p = 0 :=
  diagonalGlobalColumn_zero_sum k A j

theorem diagonalGlobalColumn_term_sum_zero (j : NormalizedCell A 1) :
    letI : Fintype (DiagonalGlobalColumnTerm k A 0 j) := Fintype.ofFinite _
    ∑ p : DiagonalGlobalColumnTerm k A 0 j, diagonalGlobalColumn k A 0 j p.val = 0 := by
  letI : Fintype (DiagonalGlobalColumnTerm k A 0 j) := Fintype.ofFinite _
  rw [← Finset.sum_subtype (diagonalGlobalColumn k A 0 j).support (fun _ => Iff.rfl)]
  exact diagonalGlobalColumn_support_sum_zero k A j

end ToricPower.IntegralArrangement
