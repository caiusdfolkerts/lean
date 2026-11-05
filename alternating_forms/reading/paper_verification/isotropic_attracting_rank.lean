module

public import PaperVerification.IsotropicAttractingPivots
public import PaperVerification.IsotropicAttractingLinearTerms

/-!
# A well-founded order for the actual isotropy equations

The torus weight orders every nonlinear term.  The remaining linear terms
can have equal torus weight.  Their pivot intervals are strictly wider, so
the secondary order by decreasing interval width makes those terms lower
as well.  This file proves that assertion for the literal polynomial
equations, rather than assuming an invertible Jacobian.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

namespace PaperVerification.IsotropicAttractingCoordinates

variable {k s : ℕ} {p : Fin s ↪ Fin (2*k+1)}

/-- Width of the interval between the two pivot columns. -/
def intervalWidth (q : LowPair p) : ℕ :=
  (p q.val.2).val - (p q.val.1).val

theorem intervalWidth_pos (q : LowPair p) : 0 < intervalWidth q := by
  exact Nat.sub_pos_of_lt q.property.1

theorem intervalWidth_lt (q : LowPair p) : intervalWidth q < 2*k+1 := by
  have h := (p q.val.2).isLt
  unfold intervalWidth
  omega

/-- The secondary order is positive on equation pivots and zero on the
coordinates which remain free. -/
def secondaryRank (hp : IndependentPivots p) : Coordinate p → ℕ :=
  Function.extend (pivotEmbedding hp)
    (Sum.elim (fun q => 2*k+1 - intervalWidth q)
      (fun q => 2*k+1 - intervalWidth q)) (fun _ => 0)

@[simp] theorem secondaryRank_firstPivot (hp : IndependentPivots p) (q : LowPair p) :
    secondaryRank hp (firstPivot hp q) = 2*k+1 - intervalWidth q := by
  exact (pivotEmbedding hp).injective.extend_apply _ _ (Sum.inl q)

@[simp] theorem secondaryRank_secondPivot (hp : IndependentPivots p) (q : LowPair p) :
    secondaryRank hp (secondPivot hp q) = 2*k+1 - intervalWidth q := by
  exact (pivotEmbedding hp).injective.extend_apply _ _ (Sum.inr q)

theorem secondaryRank_eq_zero (hp : IndependentPivots p) (v : Coordinate p)
    (hv : v ∉ Set.range (pivotEmbedding hp)) : secondaryRank hp v = 0 := by
  exact Function.extend_apply' _ _ _ hv

theorem secondaryRank_lt (hp : IndependentPivots p) (v : Coordinate p) :
    secondaryRank hp v < 2*k+2 := by
  by_cases hv : v ∈ Set.range (pivotEmbedding hp)
  · obtain ⟨q, rfl⟩ := hv
    cases q with
    | inl q =>
        change secondaryRank hp (firstPivot hp q) < _
        rw [secondaryRank_firstPivot]
        omega
    | inr q =>
        change secondaryRank hp (secondPivot hp q) < _
        rw [secondaryRank_secondPivot]
        omega
  · rw [secondaryRank_eq_zero hp v hv]
    omega

/-- One natural-valued order combines the positive torus weight with the
decreasing-width order on its linear equations. -/
def eliminationRank (hp : IndependentPivots p) (v : Coordinate p) : ℕ :=
  (2*k+2) * coordinateWeight p v + secondaryRank hp v

theorem eliminationRank_lt_of_weight_lt (hp : IndependentPivots p)
    (v z : Coordinate p) (h : coordinateWeight p v < coordinateWeight p z) :
    eliminationRank hp v < eliminationRank hp z := by
  have hm := Nat.mul_le_mul_left (2*k+2) (Nat.succ_le_of_lt h)
  rw [Nat.mul_succ] at hm
  have hv := secondaryRank_lt hp v
  unfold eliminationRank
  omega

theorem eliminationRank_lt_of_secondary_lt (hp : IndependentPivots p)
    (v z : Coordinate p) (hw : coordinateWeight p v = coordinateWeight p z)
    (h : secondaryRank hp v < secondaryRank hp z) :
    eliminationRank hp v < eliminationRank hp z := by
  simp only [eliminationRank, hw]
  omega

/-- The other possible linear term of a first-form equation is lower.
If it is an equation pivot, it is a second-form pivot on a wider interval. -/
theorem first_partner_lower (hp : IndependentPivots p) (q : LowPair p)
    (v : Coordinate p) (hrow : v.val.1 = q.val.2)
    (hcol : (p q.val.1).val + v.val.2.val = 2*k+1) :
    eliminationRank hp v < eliminationRank hp (firstPivot hp q) := by
  apply eliminationRank_lt_of_secondary_lt
  · rw [coordinateWeight_firstPivot]
    unfold coordinateWeight
    rw [hrow]
    omega
  · rw [secondaryRank_firstPivot]
    by_cases hv : v ∈ Set.range (pivotEmbedding hp)
    · obtain ⟨r, hr⟩ := hv
      cases r with
      | inl r =>
          change firstPivot hp r = v at hr
          have hrrow := congrArg (fun z : Coordinate p => z.val.1) hr
          have hrcol := congrArg (fun z : Coordinate p => z.val.2.val) hr
          simp only [firstPivot_row, firstPivot_column_val] at hrrow hrcol
          have he : (p r.val.1).val = (p q.val.2).val :=
            congrArg (fun i => (p i).val) (hrrow.trans hrow)
          have hqr := q.property.1
          have hrr := r.property.1
          have hb := (p r.val.2).isLt
          omega
      | inr r =>
          change secondPivot hp r = v at hr
          have hrrow := congrArg (fun z : Coordinate p => z.val.1) hr
          have hrcol := congrArg (fun z : Coordinate p => z.val.2.val) hr
          simp only [secondPivot_row, secondPivot_column_val] at hrrow hrcol
          have he : (p r.val.2).val = (p q.val.2).val :=
            congrArg (fun i => (p i).val) (hrrow.trans hrow)
          rw [← hr, secondaryRank_secondPivot]
          have hqr := q.property.1
          have hrr := r.property.1
          have ha := (p r.val.1).isLt
          have hb := (p q.val.2).isLt
          unfold intervalWidth
          omega
    · rw [secondaryRank_eq_zero hp v hv]
      exact Nat.sub_pos_of_lt (intervalWidth_lt q)

/-- The other possible linear term of a second-form equation is lower.
If it is an equation pivot, it is a first-form pivot on a wider interval. -/
theorem second_partner_lower (hp : IndependentPivots p) (q : LowPair p)
    (v : Coordinate p) (hrow : v.val.1 = q.val.1)
    (hcol : v.val.2.val + (p q.val.2).val = 2*k) :
    eliminationRank hp v < eliminationRank hp (secondPivot hp q) := by
  apply eliminationRank_lt_of_secondary_lt
  · rw [coordinateWeight_secondPivot]
    unfold coordinateWeight
    rw [hrow]
    omega
  · rw [secondaryRank_secondPivot]
    by_cases hv : v ∈ Set.range (pivotEmbedding hp)
    · obtain ⟨r, hr⟩ := hv
      cases r with
      | inl r =>
          change firstPivot hp r = v at hr
          have hrrow := congrArg (fun z : Coordinate p => z.val.1) hr
          have hrcol := congrArg (fun z : Coordinate p => z.val.2.val) hr
          simp only [firstPivot_row, firstPivot_column_val] at hrrow hrcol
          have he : (p r.val.1).val = (p q.val.1).val :=
            congrArg (fun i => (p i).val) (hrrow.trans hrow)
          rw [← hr, secondaryRank_firstPivot]
          have hqr := q.property.1
          have hrr := r.property.1
          have ha := (p q.val.1).isLt
          have hb := (p r.val.2).isLt
          unfold intervalWidth
          omega
      | inr r =>
          change secondPivot hp r = v at hr
          have hrrow := congrArg (fun z : Coordinate p => z.val.1) hr
          have hrcol := congrArg (fun z : Coordinate p => z.val.2.val) hr
          simp only [secondPivot_row, secondPivot_column_val] at hrrow hrcol
          have he : (p r.val.2).val = (p q.val.1).val :=
            congrArg (fun i => (p i).val) (hrrow.trans hrow)
          have hqr := q.property.1
          have hrr := r.property.1
          have ha := (p r.val.1).isLt
          omega
    · rw [secondaryRank_eq_zero hp v hv]
      exact Nat.sub_pos_of_lt (intervalWidth_lt q)

end PaperVerification.IsotropicAttractingCoordinates
