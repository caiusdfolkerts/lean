module

public import PaperVerification.TriangularPolynomialCoordinates
public import Mathlib.LinearAlgebra.Matrix.BilinearForm
public import Mathlib.Data.Finset.Prod

/-!
# Polynomial equations on the attracting Grassmann charts

Fix distinct pivot columns.  A row has a one in its pivot column, zeros in
the other pivot columns, and variables only strictly to the right of its
pivot.  These are actual row-echelon coordinates, over an arbitrary
commutative coefficient ring.  The isotropy equations below evaluate to the
original bilinear equations on those rows.

For a form supported on the anti-diagonal `a + b = c`, its row-pair equation
has weight `c - pivot i - pivot j`.  Every coordinate has strictly positive
weight.  Equations of negative weight vanish identically.  These facts are
the input to triangular elimination; no affine-paving or cohomology claim is
included in this file.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

namespace PaperVerification.IsotropicAttractingCoordinates

open MvPolynomial
open scoped BigOperators

variable {R : Type*} [CommRing R] {n s : ℕ}

/-- The actual free entries in a row-echelon matrix with the chosen pivots. -/
abbrev Coordinate (p : Fin s ↪ Fin n) :=
  {a : Fin s × Fin n // (p a.1).val < a.2.val ∧ a.2 ∉ Set.range p}

instance coordinateFintype (p : Fin s ↪ Fin n) : Fintype (Coordinate p) := by
  classical
  unfold Coordinate
  infer_instance

instance coordinateDecidableEq (p : Fin s ↪ Fin n) : DecidableEq (Coordinate p) :=
  Classical.decEq _

/-- Positive weight of an actual non-pivot row entry. -/
def coordinateWeight (p : Fin s ↪ Fin n) (a : Coordinate p) : ℕ :=
  a.val.2.val - (p a.val.1).val

theorem coordinateWeight_pos (p : Fin s ↪ Fin n) (a : Coordinate p) :
    0 < coordinateWeight p a := Nat.sub_pos_of_lt a.property.1

/-- Universal row entries.  The second condition removes every other pivot
column, so this is a split row frame over any coefficient ring. -/
def row (p : Fin s ↪ Fin n) (i : Fin s) (j : Fin n) :
    MvPolynomial (Coordinate p) R := by
  classical
  exact if j = p i then 1 else
    if h : (p i).val < j.val ∧ j ∉ Set.range p then X ⟨(i,j),h⟩ else 0

@[simp] theorem row_pivot (p : Fin s ↪ Fin n) (i j : Fin s) :
    row (R := R) p i (p j) = if j = i then 1 else 0 := by
  classical
  by_cases h : j = i
  · subst j
    simp [row]
  · have hpi : p j ≠ p i := fun he => h (p.injective he)
    simp [row, h, hpi]

theorem row_eq_zero_of_lt (p : Fin s ↪ Fin n) (i : Fin s) (j : Fin n)
    (hj : j.val < (p i).val) : row (R := R) p i j = 0 := by
  classical
  have hne : j ≠ p i := fun he => by simpa [he] using hj
  simp [row, hne, Nat.not_lt_of_ge (Nat.le_of_lt hj)]

/-- Every nonzero universal row entry has its expected character. -/
theorem row_homogeneous (p : Fin s ↪ Fin n) (i : Fin s) (j : Fin n) :
    (row (R := R) p i j).IsWeightedHomogeneous (coordinateWeight p)
      (j.val - (p i).val) := by
  classical
  unfold row
  split_ifs with h hj
  · subst j
    simpa using isWeightedHomogeneous_one R (coordinateWeight p)
  · exact isWeightedHomogeneous_X R (coordinateWeight p) ⟨(i,j),hj⟩
  · exact isWeightedHomogeneous_zero R _ _

/-- The alternating anti-diagonal matrix.  For the canonical pencil its
two parameters are `c = 2*k+1` and `c = 2*k`. -/
def formMatrix (c : ℕ) (a b : Fin n) : R :=
  if a.val + b.val = c then
    if b < a then 1 else if a < b then -1 else 0
  else 0

theorem formMatrix_eq_zero_of_ne (c : ℕ) (a b : Fin n)
    (h : a.val + b.val ≠ c) : formMatrix (R := R) c a b = 0 := by
  simp [formMatrix, h]

/-- Literal polynomial pairing of two universal rows. -/
def equation (p : Fin s ↪ Fin n) (c : ℕ) (i j : Fin s) :
    MvPolynomial (Coordinate p) R :=
  ∑ a : Fin n, ∑ b : Fin n, C (formMatrix (R := R) c a b) * row p i a * row p j b

/-- The equations are weighted homogeneous with the original normal
character, including the identically zero negative-weight cases. -/
theorem equation_homogeneous (p : Fin s ↪ Fin n) (c : ℕ) (i j : Fin s) :
    (equation (R := R) p c i j).IsWeightedHomogeneous (coordinateWeight p)
      (c - (p i).val - (p j).val) := by
  classical
  unfold equation
  apply IsWeightedHomogeneous.sum
  intro a _
  apply IsWeightedHomogeneous.sum
  intro b _
  by_cases hab : a.val + b.val = c
  · by_cases hai : (p i).val ≤ a.val
    · by_cases hbj : (p j).val ≤ b.val
      · have hd : 0 + (a.val - (p i).val) + (b.val - (p j).val) =
            c - (p i).val - (p j).val := by omega
        simpa only [hd] using
          ((isWeightedHomogeneous_C (coordinateWeight p)
            (formMatrix (R := R) c a b)).mul (row_homogeneous p i a)).mul
            (row_homogeneous p j b)
      · rw [row_eq_zero_of_lt p j b (by omega), mul_zero]
        exact isWeightedHomogeneous_zero R _ _
    · rw [row_eq_zero_of_lt p i a (by omega), mul_zero, zero_mul]
      exact isWeightedHomogeneous_zero R _ _
  · rw [formMatrix_eq_zero_of_ne c a b hab, map_zero, zero_mul, zero_mul]
    exact isWeightedHomogeneous_zero R _ _

/-- A negative normal weight gives the zero polynomial, rather than an
extra equation on the attracting coordinates. -/
theorem equation_eq_zero_of_negative_weight (p : Fin s ↪ Fin n)
    (c : ℕ) (i j : Fin s) (hc : c < (p i).val + (p j).val) :
    equation (R := R) p c i j = 0 := by
  classical
  unfold equation
  apply Finset.sum_eq_zero
  intro a _
  apply Finset.sum_eq_zero
  intro b _
  by_cases hab : a.val + b.val = c
  · by_cases hai : (p i).val ≤ a.val
    · have hbj : b.val < (p j).val := by omega
      rw [row_eq_zero_of_lt p j b hbj, mul_zero]
    · rw [row_eq_zero_of_lt p i a (by omega), mul_zero, zero_mul]
  · rw [formMatrix_eq_zero_of_ne c a b hab, map_zero, zero_mul, zero_mul]

/-- Evaluation is precisely the original bilinear pairing of the actual
row vectors; this is not a definition of a replacement isotropy condition. -/
theorem aeval_equation {A : Type*} [CommRing A] [Algebra R A]
    (p : Fin s ↪ Fin n) (c : ℕ) (i j : Fin s) (v : Coordinate p → A) :
    aeval v (equation (R := R) p c i j) =
      ∑ a : Fin n, ∑ b : Fin n,
        algebraMap R A (formMatrix (R := R) c a b) *
          aeval v (row (R := R) p i a) * aeval v (row (R := R) p j b) := by
  simp [equation]

/-- The full isotropic ideal on the cell, retaining both original forms. -/
def isotropyIdeal (p : Fin s ↪ Fin n) (c₁ c₂ : ℕ) :
    Ideal (MvPolynomial (Coordinate p) R) :=
  Ideal.span (Set.range (fun x : Bool × Fin s × Fin s =>
    equation p (if x.1 then c₁ else c₂) x.2.1 x.2.2))

end PaperVerification.IsotropicAttractingCoordinates
