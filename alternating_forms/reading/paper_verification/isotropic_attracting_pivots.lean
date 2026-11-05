module

public import PaperVerification.IsotropicAttractingCoordinates

/-!
# Unit pivots for every canonical attracting chart

In chain coordinates the two canonical alternating matrices are supported on
the anti-diagonals with index sums `2*k+1` and `2*k`.  If the pivot columns
are common isotropic, every nonconstant attracting-chart equation is indexed
by a pivot pair `a < b` with `a+b < 2*k`.

Choose the coordinate `(row a, column 2*k+1-b)` for the first equation and
`(row b, column 2*k-a)` for the second.  These coordinates exist, are all
different, and their linear coefficients are units `1` or `-1`.  No
generic-smoothness hypothesis or inversion of an integer is needed.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

namespace PaperVerification.IsotropicAttractingCoordinates

variable {k s : ℕ} (p : Fin s ↪ Fin (2*k+1))

/-- The literal two anti-diagonal conditions on distinct pivot columns. -/
def IndependentPivots : Prop :=
  ∀ i j : Fin s, i ≠ j →
    (p i).val + (p j).val ≠ 2*k ∧ (p i).val + (p j).val ≠ 2*k+1

/-- The pivot pairs whose two normal characters are positive. -/
abbrev LowPair :=
  {q : Fin s × Fin s // p q.1 < p q.2 ∧ (p q.1).val + (p q.2).val < 2*k}

instance lowPairFintype : Fintype (LowPair p) := by
  classical
  unfold LowPair
  infer_instance

instance lowPairDecidableEq : DecidableEq (LowPair p) := Classical.decEq _

variable {p}

def firstPivot (hp : IndependentPivots p) (q : LowPair p) : Coordinate p := by
  let j : Fin (2*k+1) := ⟨2*k+1 - (p q.val.2).val, by
    have hq := q.property.1
    have hb := (p q.val.2).isLt
    omega⟩
  refine ⟨(q.val.1, j), ?_, ?_⟩
  · dsimp [j]
    have hq := q.property.2
    omega
  · rintro ⟨i, hi⟩
    have hi' : (p i).val = 2*k+1 - (p q.val.2).val := congrArg Fin.val hi
    have hb := (p q.val.2).isLt
    have hine : i ≠ q.val.2 := by
      intro he
      subst i
      omega
    have hn := (hp i q.val.2 hine).2
    apply hn
    omega

def secondPivot (hp : IndependentPivots p) (q : LowPair p) : Coordinate p := by
  let j : Fin (2*k+1) := ⟨2*k - (p q.val.1).val, by omega⟩
  refine ⟨(q.val.2, j), ?_, ?_⟩
  · dsimp [j]
    have hq := q.property.2
    omega
  · rintro ⟨i, hi⟩
    have hi' : (p i).val = 2*k - (p q.val.1).val := congrArg Fin.val hi
    have ha := (p q.val.1).isLt
    have hq := q.property.1
    have hsmall := q.property.2
    have hine : i ≠ q.val.1 := by
      intro he
      subst i
      omega
    have hn := (hp i q.val.1 hine).1
    apply hn
    omega

@[simp] theorem firstPivot_row (hp : IndependentPivots p) (q : LowPair p) :
    (firstPivot hp q).val.1 = q.val.1 := rfl

@[simp] theorem secondPivot_row (hp : IndependentPivots p) (q : LowPair p) :
    (secondPivot hp q).val.1 = q.val.2 := rfl

@[simp] theorem firstPivot_column_val (hp : IndependentPivots p) (q : LowPair p) :
    (firstPivot hp q).val.2.val = 2*k+1 - (p q.val.2).val := rfl

@[simp] theorem secondPivot_column_val (hp : IndependentPivots p) (q : LowPair p) :
    (secondPivot hp q).val.2.val = 2*k - (p q.val.1).val := rfl

theorem firstPivot_injective (hp : IndependentPivots p) :
    Function.Injective (firstPivot hp) := by
  intro q r h
  have hrow := congrArg (fun v : Coordinate p => v.val.1) h
  have hcol := congrArg (fun v : Coordinate p => v.val.2.val) h
  simp only [firstPivot_row, firstPivot_column_val] at hrow hcol
  apply Subtype.ext
  apply Prod.ext hrow
  apply p.injective
  apply Fin.ext
  have hq := (p q.val.2).isLt
  have hr := (p r.val.2).isLt
  omega

theorem secondPivot_injective (hp : IndependentPivots p) :
    Function.Injective (secondPivot hp) := by
  intro q r h
  have hrow := congrArg (fun v : Coordinate p => v.val.1) h
  have hcol := congrArg (fun v : Coordinate p => v.val.2.val) h
  simp only [secondPivot_row, secondPivot_column_val] at hrow hcol
  apply Subtype.ext
  apply Prod.ext ?_ hrow
  apply p.injective
  apply Fin.ext
  have hq := (p q.val.1).isLt
  have hr := (p r.val.1).isLt
  omega

/-- A first-form pivot can never be a second-form pivot. -/
theorem firstPivot_ne_secondPivot (hp : IndependentPivots p)
    (q r : LowPair p) : firstPivot hp q ≠ secondPivot hp r := by
  intro h
  have hrow := congrArg (fun v : Coordinate p => (p v.val.1).val) h
  have hcol := congrArg (fun v : Coordinate p => v.val.2.val) h
  simp only [firstPivot_row, secondPivot_row, firstPivot_column_val,
    secondPivot_column_val] at hrow hcol
  have hq := q.property.1
  have hr := r.property.1
  have hbq := (p q.val.2).isLt
  have har := (p r.val.1).isLt
  omega

/-- All positive normal equations receive distinct actual row coordinates. -/
def pivotEmbedding (hp : IndependentPivots p) :
    LowPair p ⊕ LowPair p ↪ Coordinate p where
  toFun := Sum.elim (firstPivot hp) (secondPivot hp)
  inj' := by
    intro q r h
    cases q with
    | inl q =>
        cases r with
        | inl r => exact congrArg Sum.inl (firstPivot_injective hp h)
        | inr r => exact False.elim (firstPivot_ne_secondPivot hp q r h)
    | inr q =>
        cases r with
        | inl r => exact False.elim (firstPivot_ne_secondPivot hp r q h.symm)
        | inr r => exact congrArg Sum.inr (secondPivot_injective hp h)

@[simp] theorem coordinateWeight_firstPivot (hp : IndependentPivots p)
    (q : LowPair p) : coordinateWeight p (firstPivot hp q) =
      2*k+1 - (p q.val.1).val - (p q.val.2).val := by
  simp only [coordinateWeight, firstPivot_row, firstPivot_column_val]
  omega

@[simp] theorem coordinateWeight_secondPivot (hp : IndependentPivots p)
    (q : LowPair p) : coordinateWeight p (secondPivot hp q) =
      2*k - (p q.val.1).val - (p q.val.2).val := by
  simp only [coordinateWeight, secondPivot_row, secondPivot_column_val]

variable {R : Type*} [CommRing R]

/-- The chosen first-form coordinate has coefficient `1` or `-1`, including
the cases where the larger pivot lies beyond the center of the chain. -/
theorem firstPivot_coefficient (hp : IndependentPivots p) (q : LowPair p) :
    formMatrix (R := R) (2*k+1) (firstPivot hp q).val.2 (p q.val.2) =
      if (p q.val.2).val ≤ k then 1 else -1 := by
  have hb := (p q.val.2).isLt
  have hs : (firstPivot hp q).val.2.val + (p q.val.2).val = 2*k+1 := by
    rw [firstPivot_column_val]
    omega
  unfold formMatrix
  rw [ite_eq_left hs]
  by_cases h : (p q.val.2).val ≤ k
  · have hl : p q.val.2 < (firstPivot hp q).val.2 := by
      change (p q.val.2).val < 2*k+1 - (p q.val.2).val
      omega
    simp [h, hl]
  · have hl : (firstPivot hp q).val.2 < p q.val.2 := by
      change 2*k+1 - (p q.val.2).val < (p q.val.2).val
      omega
    simp [h, hl, not_lt_of_gt hl]

/-- The chosen second-form coordinate always has coefficient `-1`. -/
theorem secondPivot_coefficient (hp : IndependentPivots p) (q : LowPair p) :
    formMatrix (R := R) (2*k) (p q.val.1) (secondPivot hp q).val.2 = -1 := by
  have ha := (p q.val.1).isLt
  have hq := q.property.1
  have hsmall := q.property.2
  have hs : (p q.val.1).val + (secondPivot hp q).val.2.val = 2*k := by
    rw [secondPivot_column_val]
    omega
  have hl : p q.val.1 < (secondPivot hp q).val.2 := by
    change (p q.val.1).val < 2*k - (p q.val.1).val
    omega
  unfold formMatrix
  rw [ite_eq_left hs, ite_eq_right (not_lt_of_gt hl), ite_eq_left hl]

end PaperVerification.IsotropicAttractingCoordinates
