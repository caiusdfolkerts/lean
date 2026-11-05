module
public import RawTargets
public import FiniteChecks
public import Init.Data.List.FinRange

@[expose] public section

/-!
# Exact polygon-size checks for the complete ten-vertex target table

These definitions use only `Init` and the previously verified finite-data
modules. The mathematical connection to finite-set cardinality is proved
separately. No value computed by the producer is accepted as a proof.
-/

namespace Nonrational.TerminalVerification.PaperPolygon

open Nonrational.TerminalData
open Papers.RationalityTen.FiniteChecks

def maskCard (m : Nat) : Nat :=
  ((List.finRange 10).filter fun i => m.testBit i.val).length

noncomputable def targetCheck (j : Nat) : Bool :=
  (j == 1982) || (targets j).polygons.all fun m => decide (maskCard m ≤ 4)

theorem targetCheck_sound {j : Nat} (h : targetCheck j = true) (hj : j ≠ 1982) :
    ∀ m ∈ (targets j).polygons, maskCard m ≤ 4 := by
  have hall : (targets j).polygons.all (fun m => decide (maskCard m ≤ 4)) = true := by
    simpa [targetCheck, hj] using h
  intro m hm
  exact of_decide_eq_true (List.all_eq_true.mp hall m hm)

end Nonrational.TerminalVerification.PaperPolygon
