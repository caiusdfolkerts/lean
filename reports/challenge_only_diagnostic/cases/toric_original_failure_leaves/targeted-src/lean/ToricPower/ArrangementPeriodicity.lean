module

public import ToricPower.ArrangementCore
public import Mathlib.Topology.Compactness.LocallyFinite

/-! # Actual integral-translation orbits of arrangement cells

The coordinate hyperplanes in the augmented arrangement give a unique
representative of every lattice orbit: its coordinate ceilings are zero.
These representatives are finite because their closures meet the compact
unit cube and the actual closed cells are locally finite. The equivalence
below records both the representative and the literal integer translation.
It is the finite-free indexing needed for the graded cellular resolution.

Candidate source until its ordinary compiler check succeeds.
-/

@[expose] public noncomputable section

open Set
open scoped BigOperators

namespace ToricPower.IntegralArrangement

variable {n s : ℕ} (A : Fin s → Fin n → ℤ)

def latticeLift (z : Fin n → ℤ) : Fin n → ℝ := fun j => (z j : ℝ)

def augmentedLatticePairing (z : Fin n → ℤ) : Fin s ⊕ Fin n → ℤ :=
  Sum.elim (fun i => ∑ j, A i j * z j) z

@[simp]
theorem augmentedLatticePairing_inr (z : Fin n → ℤ) (j : Fin n) :
    augmentedLatticePairing A z (.inr j) = z j := rfl

@[simp]
theorem augmentedLatticePairing_add (z w : Fin n → ℤ) :
    augmentedLatticePairing A (z + w) =
      augmentedLatticePairing A z + augmentedLatticePairing A w := by
  funext i
  rcases i with i | j
  · simp [augmentedLatticePairing, mul_add, Finset.sum_add_distrib]
  · rfl

@[simp]
theorem augmentedLatticePairing_neg (z : Fin n → ℤ) :
    augmentedLatticePairing A (-z) = -augmentedLatticePairing A z := by
  funext i
  rcases i with i | j
  · simp [augmentedLatticePairing]
  · rfl

@[simp]
theorem augmentedLatticePairing_zero : augmentedLatticePairing A 0 = 0 := by
  funext i
  rcases i with i | j <;> simp [augmentedLatticePairing]

theorem augmentedForms_latticeLift (z : Fin n → ℤ) (i : Fin s ⊕ Fin n) :
    augmentedForms A i (latticeLift z) = (augmentedLatticePairing A z i : ℝ) := by
  rcases i with i | j
  · simp [augmentedForms, integralRowForm, augmentedLatticePairing, latticeLift]
  · rfl

/-- Translation is the literal addition of the integer vector to every point
of the cell, with the corresponding integral change of ceiling labels. -/
def translateCell (z : Fin n → ℤ) {d : ℕ} (c : Cell (augmentedForms A) d) :
    Cell (augmentedForms A) d :=
  ⟨(c.val.1 + augmentedLatticePairing A z, c.val.2),
    (by
      obtain ⟨x, hx⟩ := c.property.1
      refine ⟨x + latticeLift z, ?_⟩
      exact (add_mem_cell_iff _ _ _ _ _ (augmentedForms_latticeLift A z) x).mpr hx),
    c.property.2⟩

@[simp]
theorem translateCell_zero {d : ℕ} (c : Cell (augmentedForms A) d) :
    translateCell A 0 c = c := by
  apply Subtype.ext
  simp [translateCell]

@[simp]
theorem translateCell_add (z w : Fin n → ℤ) {d : ℕ}
    (c : Cell (augmentedForms A) d) :
    translateCell A z (translateCell A w c) = translateCell A (w + z) c := by
  apply Subtype.ext
  simp [translateCell, add_assoc]

def coordinateCeilings {d : ℕ} (c : Cell (augmentedForms A) d) : Fin n → ℤ :=
  fun j => c.val.1 (.inr j)

@[simp]
theorem coordinateCeilings_translateCell (z : Fin n → ℤ) {d : ℕ}
    (c : Cell (augmentedForms A) d) :
    coordinateCeilings A (translateCell A z c) = coordinateCeilings A c + z := rfl

/-- Normalized cells are actual cells whose coordinate ceilings all vanish. -/
def NormalizedCell (d : ℕ) :=
  {c : Cell (augmentedForms A) d // coordinateCeilings A c = 0}

def normalizeCell {d : ℕ} (c : Cell (augmentedForms A) d) : NormalizedCell A d :=
  ⟨translateCell A (-coordinateCeilings A c) c, by simp⟩

/-- An exact orbit decomposition, rather than just a finite bound on labels. -/
def cellOrbitEquiv (d : ℕ) :
    Cell (augmentedForms A) d ≃ NormalizedCell A d × (Fin n → ℤ) where
  toFun c := (normalizeCell A c, coordinateCeilings A c)
  invFun q := translateCell A q.2 q.1.val
  left_inv c := by
    change translateCell A (coordinateCeilings A c)
      (translateCell A (-coordinateCeilings A c) c) = c
    rw [translateCell_add]
    simp
  right_inv q := by
    rcases q with ⟨⟨c, hc⟩, z⟩
    apply Prod.ext
    · apply Subtype.ext
      change translateCell A (-coordinateCeilings A (translateCell A z c))
        (translateCell A z c) = c
      rw [coordinateCeilings_translateCell, hc, zero_add, translateCell_add]
      simp
    · change coordinateCeilings A (translateCell A z c) = z
      rw [coordinateCeilings_translateCell, hc, zero_add]

/-- Every normalized cell meets the actual compact cube `[-1,0]^n`. -/
theorem normalizedCell_meets_cube {d : ℕ} (c : NormalizedCell A d) :
    (closedCell (augmentedForms A) c.val.val.1 c.val.val.2 ∩
      Icc (-1 : Fin n → ℝ) 0).Nonempty := by
  obtain ⟨x, hx⟩ := c.val.property.1
  have hxc := cell_subset_closedCell (augmentedForms A) _ _ hx
  refine ⟨x, hxc, ?_⟩
  constructor
  · intro j
    have h := (closedCell_coordinate_bounds A _ _ hxc j).1
    have he : c.val.val.1 (.inr j) = 0 := congrFun c.property j
    simpa only [he, Int.cast_zero, zero_sub, Pi.neg_apply, Pi.one_apply] using h
  · intro j
    have h := (closedCell_coordinate_bounds A _ _ hxc j).2
    have he : c.val.val.1 (.inr j) = 0 := congrFun c.property j
    simpa only [he, Int.cast_zero, Pi.zero_apply] using h

/-- Finiteness follows from the actual locally finite arrangement in the
given topology; no finiteness of orbit representatives is assumed. -/
instance normalizedCell_finite (d : ℕ) : Finite (NormalizedCell A d) := by
  let F : ((Fin s ⊕ Fin n → ℤ) × Set (Fin s ⊕ Fin n)) → Set (Fin n → ℝ) :=
    fun p => closedCell (augmentedForms A) p.1 p.2
  have hloc : LocallyFinite F :=
    closedCells_locallyFinite (augmentedForms A)
      (fun i => (augmentedForms A i).continuous_of_finiteDimensional)
  have hfin : Set.Finite {p | (F p ∩ Icc (-1 : Fin n → ℝ) 0).Nonempty} :=
    hloc.finite_nonempty_inter_compact isCompact_Icc
  let g : NormalizedCell A d →
      {p | (F p ∩ Icc (-1 : Fin n → ℝ) 0).Nonempty} :=
    fun c => ⟨c.val.val, normalizedCell_meets_cube A c⟩
  letI : Finite {p | (F p ∩ Icc (-1 : Fin n → ℝ) 0).Nonempty} := hfin.to_subtype
  exact Finite.of_injective g (by
    intro c c' h
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg
      (fun z : {p | (F p ∩ Icc (-1 : Fin n → ℝ) 0).Nonempty} => z.val) h)

/-- Literal translation acts freely on the cells; the coordinate ceilings
recover the translating lattice vector. -/
theorem translateCell_eq_iff {d : ℕ} (c : Cell (augmentedForms A) d)
    (z w : Fin n → ℤ) : translateCell A z c = translateCell A w c ↔ z = w := by
  constructor
  · intro h
    have h' := congrArg (coordinateCeilings A) h
    simp only [coordinateCeilings_translateCell] at h'
    exact add_left_cancel h'
  · rintro rfl
    rfl

/-- The cellular chain direction stops at the ambient dimension; this
bound follows from the actual active-kernel subspace. -/
theorem cell_dimension_le {d : ℕ} (c : Cell (augmentedForms A) d) : d ≤ n := by
  rw [← c.property.2]
  simpa using (Submodule.finrank_le (cellDirection (augmentedForms A) c.val.2))

theorem cell_isEmpty_of_dimension_lt {d : ℕ} (hd : n < d) :
    IsEmpty (Cell (augmentedForms A) d) :=
  ⟨fun c => (not_lt_of_ge (cell_dimension_le A c) hd).elim⟩

/-- There are finitely many normalized cells in all degrees together.
In particular the resulting equivariant complex has finitely many labels
and finite length, with neither finiteness property assumed. -/
instance allNormalizedCells_finite : Finite (Σ d, NormalizedCell A d) := by
  let g : (Σ d, NormalizedCell A d) →
      (Σ d : Fin (n + 1), NormalizedCell A d.val) :=
    fun c => ⟨⟨c.1, Nat.lt_succ_of_le (cell_dimension_le A c.2.val)⟩, c.2⟩
  exact Finite.of_injective g (by
    rintro ⟨d, c⟩ ⟨e, b⟩ h
    have hde : d = e := congrArg (fun t => t.1.val) h
    subst e
    have hcb : c = b := by
      cases h
      rfl
    subst b
    rfl)

end ToricPower.IntegralArrangement
