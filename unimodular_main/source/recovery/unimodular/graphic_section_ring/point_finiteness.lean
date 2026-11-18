module

public import Recovery.Unimodular.GraphicSectionRing.InitialIdeal
public import Mathlib.Order.WellQuasiOrder
public import Mathlib.Data.Set.Finite.Basic

/-!
# Finiteness of graphic lattice points from the homogeneous character condition

The constraints may be an arbitrary, even infinite, set. There are only
finitely many ordered coordinate pairs. Choosing one original inequality
per occurring pair gives a vector of nonnegative integer slacks for each
actual lattice point. Comparable slack vectors have a difference satisfying
all the original homogeneous inequalities; the assumed character condition
therefore forces the points to agree. Dickson's lemma makes the slack image
finite. No finite-constraint, nonempty-polyhedron, positive-dimension, or
boundedness premise is added.

Source candidate, pending compilation.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace Unimodular.GraphicSectionRing

attribute [local instance] Classical.propDecidable

variable {n : ℕ}

/-- The finite set of ordered coordinate pairs that actually occur among
the original constraints. Bounds are not replaced or minimized. -/
def OccurringConstraintPair (C : Set (Constraint n)) :=
  {p : Coordinate n × Coordinate n // ∃ c ∈ C, (c.left, c.right) = p}

instance occurringConstraintPair_finite (C : Set (Constraint n)) :
    Finite (OccurringConstraintPair C) := by
  unfold OccurringConstraintPair
  infer_instance

/-- One original constraint with each occurring ordered pair. -/
def pairConstraint (C : Set (Constraint n)) (p : OccurringConstraintPair C) : Constraint n :=
  Classical.choose p.property

theorem pairConstraint_mem (C : Set (Constraint n)) (p : OccurringConstraintPair C) :
    pairConstraint C p ∈ C :=
  (Classical.choose_spec p.property).1

theorem pairConstraint_coordinates (C : Set (Constraint n))
    (p : OccurringConstraintPair C) :
    ((pairConstraint C p).left, (pairConstraint C p).right) = p.val :=
  (Classical.choose_spec p.property).2

/-- Literal nonnegative integer slack, encoded as a natural number. -/
def pointSlacks (C : Set (Constraint n)) (x : Point C) : OccurringConstraintPair C → ℕ :=
  fun p => ((pairConstraint C p).bound -
    difference x.val (pairConstraint C p).left (pairConstraint C p).right).toNat

theorem difference_sub (x y : Lattice n) (a b : Coordinate n) :
    difference (x - y) a b = difference x a b - difference y a b := by
  cases a <;> cases b <;> simp [difference, anchored, Pi.sub_apply] <;> ring

/-- Componentwise comparable slacks force equality of the original points.
Each original constraint is handled through its actual ordered pair. -/
theorem pointSlacks_comparable_eq (C : Set (Constraint n))
    (hzero : ∀ m : Lattice n, (∀ c ∈ C,
      difference m c.left c.right ≤ 0) → m = 0)
    (x y : Point C) (hxy : pointSlacks C x ≤ pointSlacks C y) : x = y := by
  apply Subtype.ext
  apply Eq.symm
  apply sub_eq_zero.mp
  apply hzero (y.val - x.val)
  intro c hc
  let p : OccurringConstraintPair C := ⟨(c.left, c.right), c, hc, rfl⟩
  let r := pairConstraint C p
  have hrc : r ∈ C := pairConstraint_mem C p
  have hl : r.left = c.left := congrArg Prod.fst (pairConstraint_coordinates C p)
  have hr : r.right = c.right := congrArg Prod.snd (pairConstraint_coordinates C p)
  have hx := x.property r hrc
  have hy := y.property r hrc
  have hle := hxy p
  change (r.bound - difference x.val r.left r.right).toNat ≤
    (r.bound - difference y.val r.left r.right).toNat at hle
  have hd : difference y.val r.left r.right ≤ difference x.val r.left r.right := by
    omega
  rw [hl, hr] at hd
  rw [difference_sub]
  omega

/-- The full actual lattice-point set is finite as soon as the only
integral homogeneous character allowed by all inequalities is zero. This
includes inconsistent systems, arbitrary infinite systems, and rank zero. -/
theorem finite_point_of_homogeneous_zero (C : Set (Constraint n))
    (hzero : ∀ m : Lattice n, (∀ c ∈ C,
      difference m c.left c.right ≤ 0) → m = 0) :
    Finite (Point C) := by
  have hinj : Function.Injective (pointSlacks C) := by
    intro x y h
    exact pointSlacks_comparable_eq C hzero x y (le_of_eq h)
  have hanti : IsAntichain (· ≤ ·) (Set.range (pointSlacks C)) := by
    rintro _ ⟨x, rfl⟩ _ ⟨y, rfl⟩ hne hle
    exact hne (congrArg (pointSlacks C) (pointSlacks_comparable_eq C hzero x y hle))
  exact (Set.finite_range_iff hinj).mp
    (WellQuasiOrderedLE.finite_of_isAntichain hanti)

end Unimodular.GraphicSectionRing

#print axioms Unimodular.GraphicSectionRing.pointSlacks_comparable_eq
#print axioms Unimodular.GraphicSectionRing.finite_point_of_homogeneous_zero

end

#check Unimodular.GraphicSectionRing.finite_point_of_homogeneous_zero
