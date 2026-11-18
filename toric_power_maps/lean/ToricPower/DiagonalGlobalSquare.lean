module

public import ToricPower.DiagonalGlobalColumns

/-!
# The genuine convolution identity for the finite global columns

Each normalized boundary column retains its literal lattice translation.
The coefficient of a two-step path of total translation `t` is therefore
the convolution sum over `(intermediate cell,a)` and `(target,t-a)`.
This file proves that sum is zero from the actual cellular identity
`d² = 0` on the universal cover and actual translation invariance of the
attaching-map degrees.

There is no imposed square-zero axiom for a chosen combinatorial matrix.
Candidate until its complete source dependency closure passes Lean.
-/

@[expose] public noncomputable section

open Topology Topology.RelCWComplex
open scoped Classical

namespace ToricPower.IntegralArrangement

variable {n s : ℕ} (k : Type) [Ring k] (A : Fin s → Fin n → ℤ)

local instance diagonalGlobalSquarePeriodicCW : CWComplex (arrangementCarrier A) :=
  periodicArrangementCWComplex A

/-- Reindexing a genuine finite boundary column preserves every finite
sum, without requiring a summand to be linear in its coefficient. -/
theorem diagonalGlobalColumn_sum {M : Type*} [AddCommMonoid M]
    (d : ℕ) (j : NormalizedCell A (d+1))
    (F : (NormalizedCell A d × (Fin n → ℤ)) → k → M) :
    (diagonalGlobalColumn k A d j).sum F =
      (TauCeti.cellularBoundaryColumn (arrangementCarrier A) k d j.val).sum
        (fun c r => F (cellOrbitEquiv A d c) r) := by
  simp only [diagonalGlobalColumn, Finsupp.domLCongr_apply,
    Finsupp.domCongr_apply, Finsupp.sum_equivMapDomain]
  rfl

/-- Translating a normalized column recovers the actual coefficient
between arbitrary universal-cover source and target cells. -/
theorem diagonalGlobalColumn_translatedTarget (d : ℕ)
    (i : NormalizedCell A d) (t : Fin n → ℤ)
    (j : Cell (augmentedForms A) (d+1)) :
    diagonalGlobalColumn k A d (normalizeCell A j)
        (i,t-coordinateCeilings A j) =
      TauCeti.cellularIncidence (arrangementCarrier A) k d
        (translateCell A t i.val) j := by
  rw [diagonalGlobalColumn_apply]
  have h := arrangement_cellularIncidence_translate A k
    (coordinateCeilings A j) d
    (translateCell A (t-coordinateCeilings A j) i.val) (normalizeCell A j).val
  rw [translateCell_add, sub_add_cancel, translate_normalizeCell] at h
  exact h.symm

/-- The exact coefficientwise convolution equation for the global
diagonal matrix, at every lattice character with no bound on `t`. -/
theorem diagonalGlobalColumn_convolution_zero (d : ℕ)
    (i : NormalizedCell A d) (j : NormalizedCell A (d+2))
    (t : Fin n → ℤ) :
    (diagonalGlobalColumn k A (d+1) j).sum
      (fun p r => r * diagonalGlobalColumn k A d p.1 (i,t-p.2)) = 0 := by
  rw [diagonalGlobalColumn_sum]
  change (TauCeti.cellularBoundaryColumn (arrangementCarrier A) k (d+1)
    j.val).sum (fun c r => r * diagonalGlobalColumn k A d (normalizeCell A c)
      (i,t-coordinateCeilings A c)) = 0
  simp_rw [diagonalGlobalColumn_translatedTarget]
  simpa only [Finsupp.sum, TauCeti.cellularBoundaryColumn_apply] using
    (TauCeti.sum_cellularIncidence_mul (arrangementCarrier A) k d
      (translateCell A t i.val) j.val)

/-- The literal finite-support convolution column obtained by composing
the two normalized boundary columns. -/
def diagonalGlobalComposedColumn (d : ℕ) (j : NormalizedCell A (d+2)) :
    (NormalizedCell A d × (Fin n → ℤ)) →₀ k :=
  (diagonalGlobalColumn k A (d+1) j).sum (fun p r =>
    r • Finsupp.mapDomain (fun q => (q.1,p.2+q.2))
      (diagonalGlobalColumn k A d p.1))

theorem diagonalGlobalComposedColumn_apply (d : ℕ)
    (j : NormalizedCell A (d+2)) (i : NormalizedCell A d) (t : Fin n → ℤ) :
    diagonalGlobalComposedColumn k A d j (i,t) =
      (diagonalGlobalColumn k A (d+1) j).sum
        (fun p r => r * diagonalGlobalColumn k A d p.1 (i,t-p.2)) := by
  unfold diagonalGlobalComposedColumn
  rw [Finsupp.sum_apply]
  apply Finsupp.sum_congr
  intro p hp
  simp only [Finsupp.smul_apply, smul_eq_mul]
  congr 1
  have hinj : Function.Injective
      (fun q : NormalizedCell A d × (Fin n → ℤ) => (q.1,p.2+q.2)) := by
    intro a b hab
    have first := congrArg (fun q : NormalizedCell A d × (Fin n → ℤ) => q.1) hab
    have second := congrArg (fun q : NormalizedCell A d × (Fin n → ℤ) => q.2) hab
    exact Prod.ext first (add_left_cancel second)
  have h := Finsupp.mapDomain_apply_of_injective hinj
    (diagonalGlobalColumn k A d p.1) (i,t-p.2)
  have heq : p.2 + (t-p.2) = t := by abel
  simpa only [heq] using h

/-- The actual finite global convolution column vanishes as a finitely
supported function, rather than only after a finite collection of tests. -/
theorem diagonalGlobalComposedColumn_eq_zero (d : ℕ)
    (j : NormalizedCell A (d+2)) : diagonalGlobalComposedColumn k A d j = 0 := by
  ext p
  rcases p with ⟨i,t⟩
  rw [diagonalGlobalComposedColumn_apply, diagonalGlobalColumn_convolution_zero]
  rfl

end ToricPower.IntegralArrangement
