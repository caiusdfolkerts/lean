module

public import Papers.RationalityTenBasisCertificates
public import Mathlib.Algebra.MvPolynomial.Eval
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.LinearAlgebra.Matrix.Notation
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.NormNum

@[expose] public section

/-!
# Exact polynomial tables for rank-four matroid charts

The JSON convention is a four-row, eight-column matrix `[I | D]`.
Configurations elsewhere in the project are matrices of eight rows and
four coordinates.  `rowMatrix` therefore stores `[I; Dᵀ]`, explicitly.
The determinant is unchanged by this transpose.  Every imported minor
polynomial is required to be equal to the determinant of this actual
matrix, as a polynomial; evaluation then preserves that equality.

The variable type is arbitrary. In particular it may be the nested
`Option` type used by a sequence of rational eliminations.
-/

noncomputable section
namespace Papers.RationalityTen.MatroidChecked.ChartPolynomial

open Matrix MvPolynomial Finset BasisCertificates

abbrev Point := Fin 8
abbrev Coordinate := Fin 4
abbrev firstFour : Coordinate → Point := Fin.castAdd 4
abbrev lastFour : Coordinate → Point := Fin.natAdd 4

inductive Entry (ι : Type*) where
  | zero
  | one
  | variable (i : ι)
  deriving DecidableEq

def Entry.value {ι R : Type*} [Zero R] [One R] (x : ι → R) : Entry ι → R
  | .zero => 0
  | .one => 1
  | .variable i => x i

def Entry.polynomial {ι : Type*} : Entry ι → MvPolynomial ι ℚ
  | .zero => 0
  | .one => 1
  | .variable i => X i

@[simp] theorem Entry.eval_polynomial {ι R : Type*} [CommRing R]
    (f : ℚ →+* R) (x : ι → R) (e : Entry ι) :
    eval₂Hom f x e.polynomial = e.value x := by
  cases e <;> simp [Entry.polynomial, Entry.value]

/-- The first index of `D` is a basis coordinate; the second is a
nonbasis label. The lower block of the returned row matrix is `Dᵀ`. -/
def rowMatrix {R : Type*} [Zero R] [One R]
    (D : Coordinate → Coordinate → R) : Matrix Point Coordinate R :=
  fun k => Fin.addCases (m := 4) (n := 4) (fun i j => if i = j then 1 else 0) (fun j i => D i j) k

@[simp] theorem rowMatrix_first {R : Type*} [Zero R] [One R]
    (D : Coordinate → Coordinate → R) (i j : Coordinate) :
    rowMatrix D (firstFour i) j = if i = j then 1 else 0 := by
  simp only [rowMatrix, firstFour, Fin.addCases_left]

@[simp] theorem rowMatrix_last {R : Type*} [Zero R] [One R]
    (D : Coordinate → Coordinate → R) (i j : Coordinate) :
    rowMatrix D (lastFour i) j = D j i := by
  simp only [rowMatrix, lastFour, Fin.addCases_right]

def polynomialMatrix {ι : Type*} (D : Coordinate → Coordinate → Entry ι) :
    Matrix Point Coordinate (MvPolynomial ι ℚ) :=
  rowMatrix (fun i j => (D i j).polynomial)

def valueMatrix {ι R : Type*} [Zero R] [One R]
    (D : Coordinate → Coordinate → Entry ι) (x : ι → R) : Matrix Point Coordinate R :=
  rowMatrix (fun i j => (D i j).value x)

theorem map_polynomialMatrix {ι R : Type*} [CommRing R]
    (D : Coordinate → Coordinate → Entry ι) (f : ℚ →+* R) (x : ι → R) :
    (polynomialMatrix D).map (eval₂Hom f x) = valueMatrix D x := by
  ext i j
  refine Fin.addCases (m := 4) (n := 4) (fun a => ?_) (fun a => ?_) i
  · change eval₂Hom f x (polynomialMatrix D (firstFour a) j) =
      valueMatrix D x (firstFour a) j
    by_cases h : a = j <;> simp [polynomialMatrix, valueMatrix, h]
  · change eval₂Hom f x (polynomialMatrix D (lastFour a) j) =
      valueMatrix D x (lastFour a) j
    simpa only [polynomialMatrix, valueMatrix, rowMatrix_last] using
      Entry.eval_polynomial f x (D j a)

/-- Variable occurrences are recorded explicitly; finite tables check both
directions so an unnoticed repeated variable cannot constrain a matrix entry. -/
structure ParameterCertificate {ι : Type*}
    (D : Coordinate → Coordinate → Entry ι)
    (position : ι → Coordinate × Coordinate) : Prop where
  variable_at : ∀ k, D (position k).1 (position k).2 = .variable k
  position_at : ∀ i j k, D i j = .variable k → position k = (i,j)

def parametersOf {ι R : Type*}
    (position : ι → Coordinate × Coordinate) (q : Matrix Point Coordinate R) : ι → R :=
  fun k => q (lastFour (position k).2) (position k).1

/-- Every matrix with the declared zeros, ones, and identity basis is in
the parameterization. No nonzero assumption is imposed on free variables. -/
theorem ParameterCertificate.valueMatrix_parametersOf {ι R : Type*} [Zero R] [One R]
    {D : Coordinate → Coordinate → Entry ι}
    {position : ι → Coordinate × Coordinate} (C : ParameterCertificate D position)
    (q : Matrix Point Coordinate R)
    (hidentity : q.submatrix firstFour id = 1)
    (hzero : ∀ i j, D i j = .zero → q (lastFour j) i = 0)
    (hone : ∀ i j, D i j = .one → q (lastFour j) i = 1) :
    valueMatrix D (parametersOf position q) = q := by
  ext i j
  refine Fin.addCases (m := 4) (n := 4) (fun a => ?_) (fun a => ?_) i
  · have h := congrFun (congrFun hidentity a) j
    simpa [valueMatrix, Matrix.submatrix_apply, Matrix.one_apply] using h.symm
  · change rowMatrix (fun r c => (D r c).value (parametersOf position q))
      (lastFour a) j = q (lastFour a) j
    rw [rowMatrix_last]
    cases he : D j a with
    | zero => exact (hzero j a he).symm
    | one => exact (hone j a he).symm
    | «variable» k =>
      change q (lastFour (position k).2) (position k).1 = q (lastFour a) j
      rw [C.position_at j a k he]

/-- Only explicitly chosen coordinates need to be units. This permits
an added coordinate to be zero when one incidence equation is relaxed. -/
theorem parametersOf_nonzero {ι R : Type*} [Zero R]
    (position : ι → Coordinate × Coordinate) (q : Matrix Point Coordinate R)
    {u : ℕ} (unitVariables : Fin u → ι)
    (h : ∀ k, q (lastFour (position (unitVariables k)).2)
      (position (unitVariables k)).1 ≠ 0) :
    ∀ k, parametersOf position q (unitVariables k) ≠ 0 := h

/-- The complete lexicographic list of four-element subsets of eight labels. -/
def minorRowTree : Table (Coordinate → Point) :=
  .node 35 (.node 17 (.node 8 (.node 4 (.node 2 (.node 1 (.leaf ![0,1,2,3]) (.leaf ![0,1,2,4])) (.node 3 (.leaf ![0,1,2,5]) (.leaf ![0,1,2,6]))) (.node 6 (.node 5 (.leaf ![0,1,2,7]) (.leaf ![0,1,3,4])) (.node 7 (.leaf ![0,1,3,5]) (.leaf ![0,1,3,6])))) (.node 12 (.node 10 (.node 9 (.leaf ![0,1,3,7]) (.leaf ![0,1,4,5])) (.node 11 (.leaf ![0,1,4,6]) (.leaf ![0,1,4,7]))) (.node 14 (.node 13 (.leaf ![0,1,5,6]) (.leaf ![0,1,5,7])) (.node 15 (.leaf ![0,1,6,7]) (.node 16 (.leaf ![0,2,3,4]) (.leaf ![0,2,3,5])))))) (.node 26 (.node 21 (.node 19 (.node 18 (.leaf ![0,2,3,6]) (.leaf ![0,2,3,7])) (.node 20 (.leaf ![0,2,4,5]) (.leaf ![0,2,4,6]))) (.node 23 (.node 22 (.leaf ![0,2,4,7]) (.leaf ![0,2,5,6])) (.node 24 (.leaf ![0,2,5,7]) (.node 25 (.leaf ![0,2,6,7]) (.leaf ![0,3,4,5]))))) (.node 30 (.node 28 (.node 27 (.leaf ![0,3,4,6]) (.leaf ![0,3,4,7])) (.node 29 (.leaf ![0,3,5,6]) (.leaf ![0,3,5,7]))) (.node 32 (.node 31 (.leaf ![0,3,6,7]) (.leaf ![0,4,5,6])) (.node 33 (.leaf ![0,4,5,7]) (.node 34 (.leaf ![0,4,6,7]) (.leaf ![0,5,6,7]))))))) (.node 52 (.node 43 (.node 39 (.node 37 (.node 36 (.leaf ![1,2,3,4]) (.leaf ![1,2,3,5])) (.node 38 (.leaf ![1,2,3,6]) (.leaf ![1,2,3,7]))) (.node 41 (.node 40 (.leaf ![1,2,4,5]) (.leaf ![1,2,4,6])) (.node 42 (.leaf ![1,2,4,7]) (.leaf ![1,2,5,6])))) (.node 47 (.node 45 (.node 44 (.leaf ![1,2,5,7]) (.leaf ![1,2,6,7])) (.node 46 (.leaf ![1,3,4,5]) (.leaf ![1,3,4,6]))) (.node 49 (.node 48 (.leaf ![1,3,4,7]) (.leaf ![1,3,5,6])) (.node 50 (.leaf ![1,3,5,7]) (.node 51 (.leaf ![1,3,6,7]) (.leaf ![1,4,5,6])))))) (.node 61 (.node 56 (.node 54 (.node 53 (.leaf ![1,4,5,7]) (.leaf ![1,4,6,7])) (.node 55 (.leaf ![1,5,6,7]) (.leaf ![2,3,4,5]))) (.node 58 (.node 57 (.leaf ![2,3,4,6]) (.leaf ![2,3,4,7])) (.node 59 (.leaf ![2,3,5,6]) (.node 60 (.leaf ![2,3,5,7]) (.leaf ![2,3,6,7]))))) (.node 65 (.node 63 (.node 62 (.leaf ![2,4,5,6]) (.leaf ![2,4,5,7])) (.node 64 (.leaf ![2,4,6,7]) (.leaf ![2,5,6,7]))) (.node 67 (.node 66 (.leaf ![3,4,5,6]) (.leaf ![3,4,5,7])) (.node 68 (.leaf ![3,4,6,7]) (.node 69 (.leaf ![3,5,6,7]) (.leaf ![4,5,6,7])))))))

def minorRows (i : Fin 70) : Coordinate → Point := minorRowTree.get i.val

@[simp] theorem minorRows_zero : minorRows 0 = firstFour := by
  funext i
  fin_cases i <;> rfl

def minorSet (i : Fin 70) : Finset Point := univ.image (minorRows i)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem minorSets_complete :
    univ.image minorSet = (univ : Finset Point).powersetCard 4 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem minorSet_card : ∀ i : Fin 70, (minorSet i).card = 4 := by
  decide +kernel

theorem exists_minorSet (S : Finset Point) (hS : S.card = 4) :
    ∃ i : Fin 70, minorSet i = S := by
  have hmem : S ∈ (univ : Finset Point).powersetCard 4 :=
    mem_powersetCard.mpr ⟨subset_univ _, hS⟩
  rw [← minorSets_complete] at hmem
  obtain ⟨i, _, hi⟩ := mem_image.mp hmem
  exact ⟨i, hi⟩

/-- A shared four-by-four determinant expansion, used once in the table
proof rather than expanded afresh for every stored matroid. -/
theorem det_four {R : Type*} [CommRing R] (A : Matrix Coordinate Coordinate R) :
    A.det = A 0 0 * A 1 1 * A 2 2 * A 3 3 - A 0 0 * A 1 1 * A 2 3 * A 3 2 - A 0 0 * A 1 2 * A 2 1 * A 3 3 + A 0 0 * A 1 2 * A 2 3 * A 3 1 + A 0 0 * A 1 3 * A 2 1 * A 3 2 - A 0 0 * A 1 3 * A 2 2 * A 3 1 - A 0 1 * A 1 0 * A 2 2 * A 3 3 + A 0 1 * A 1 0 * A 2 3 * A 3 2 + A 0 1 * A 1 2 * A 2 0 * A 3 3 - A 0 1 * A 1 2 * A 2 3 * A 3 0 - A 0 1 * A 1 3 * A 2 0 * A 3 2 + A 0 1 * A 1 3 * A 2 2 * A 3 0 + A 0 2 * A 1 0 * A 2 1 * A 3 3 - A 0 2 * A 1 0 * A 2 3 * A 3 1 - A 0 2 * A 1 1 * A 2 0 * A 3 3 + A 0 2 * A 1 1 * A 2 3 * A 3 0 + A 0 2 * A 1 3 * A 2 0 * A 3 1 - A 0 2 * A 1 3 * A 2 1 * A 3 0 - A 0 3 * A 1 0 * A 2 1 * A 3 2 + A 0 3 * A 1 0 * A 2 2 * A 3 1 + A 0 3 * A 1 1 * A 2 0 * A 3 2 - A 0 3 * A 1 1 * A 2 2 * A 3 0 - A 0 3 * A 1 2 * A 2 0 * A 3 1 + A 0 3 * A 1 2 * A 2 1 * A 3 0 := by
  simp only [Matrix.det_succ_row_zero, Matrix.det_fin_three, Matrix.submatrix_apply,
    Fin.sum_univ_succ, Fin.val_zero, Fin.val_succ, Fin.val_eq_zero,
    Fin.zero_succAbove, Fin.succ_succAbove_zero, Fin.succ_succAbove_one,
    Fin.succ_zero_eq_one, Fin.succ_one_eq_two, Matrix.submatrix_submatrix,
    Function.comp_apply, Matrix.det_unique, Fin.default_eq_zero,
    Finset.univ_unique, Finset.sum_singleton]
  norm_num [Fin.succAbove, Fin.succ, Fin.castSucc, Fin.lt_def]
  ring

/-- A universe-polymorphic literal lookup table for formulas over any coefficient ring. -/
inductive FormulaTable (α : Type*) where
  | leaf : α → FormulaTable α
  | node : ℕ → FormulaTable α → FormulaTable α → FormulaTable α

def FormulaTable.get {α : Type*} (t : FormulaTable α) (i : ℕ) : α :=
  match t with
  | .leaf a => a
  | .node k l r => if i < k then l.get i else r.get i

def minorFormulaTree {R : Type*} [CommRing R] :
    FormulaTable ((Coordinate → Coordinate → R) → R) :=
  .node 35 (.node 17 (.node 8 (.node 4 (.node 2 (.node 1 (.leaf (fun D => 1)) (.leaf (fun D => D 3 0))) (.node 3 (.leaf (fun D => D 3 1)) (.leaf (fun D => D 3 2)))) (.node 6 (.node 5 (.leaf (fun D => D 3 3)) (.leaf (fun D => -D 2 0))) (.node 7 (.leaf (fun D => -D 2 1)) (.leaf (fun D => -D 2 2))))) (.node 12 (.node 10 (.node 9 (.leaf (fun D => -D 2 3)) (.leaf (fun D => D 2 0 * D 3 1 - D 3 0 * D 2 1))) (.node 11 (.leaf (fun D => D 2 0 * D 3 2 - D 3 0 * D 2 2)) (.leaf (fun D => D 2 0 * D 3 3 - D 3 0 * D 2 3)))) (.node 14 (.node 13 (.leaf (fun D => D 2 1 * D 3 2 - D 3 1 * D 2 2)) (.leaf (fun D => D 2 1 * D 3 3 - D 3 1 * D 2 3))) (.node 15 (.leaf (fun D => D 2 2 * D 3 3 - D 3 2 * D 2 3)) (.node 16 (.leaf (fun D => D 1 0)) (.leaf (fun D => D 1 1))))))) (.node 26 (.node 21 (.node 19 (.node 18 (.leaf (fun D => D 1 2)) (.leaf (fun D => D 1 3))) (.node 20 (.leaf (fun D => -D 1 0 * D 3 1 + D 3 0 * D 1 1)) (.leaf (fun D => -D 1 0 * D 3 2 + D 3 0 * D 1 2)))) (.node 23 (.node 22 (.leaf (fun D => -D 1 0 * D 3 3 + D 3 0 * D 1 3)) (.leaf (fun D => -D 1 1 * D 3 2 + D 3 1 * D 1 2))) (.node 24 (.leaf (fun D => -D 1 1 * D 3 3 + D 3 1 * D 1 3)) (.node 25 (.leaf (fun D => -D 1 2 * D 3 3 + D 3 2 * D 1 3)) (.leaf (fun D => D 1 0 * D 2 1 - D 2 0 * D 1 1)))))) (.node 30 (.node 28 (.node 27 (.leaf (fun D => D 1 0 * D 2 2 - D 2 0 * D 1 2)) (.leaf (fun D => D 1 0 * D 2 3 - D 2 0 * D 1 3))) (.node 29 (.leaf (fun D => D 1 1 * D 2 2 - D 2 1 * D 1 2)) (.leaf (fun D => D 1 1 * D 2 3 - D 2 1 * D 1 3)))) (.node 32 (.node 31 (.leaf (fun D => D 1 2 * D 2 3 - D 2 2 * D 1 3)) (.leaf (fun D => D 1 0 * D 2 1 * D 3 2 - D 1 0 * D 3 1 * D 2 2 - D 2 0 * D 1 1 * D 3 2 + D 2 0 * D 3 1 * D 1 2 + D 3 0 * D 1 1 * D 2 2 - D 3 0 * D 2 1 * D 1 2))) (.node 33 (.leaf (fun D => D 1 0 * D 2 1 * D 3 3 - D 1 0 * D 3 1 * D 2 3 - D 2 0 * D 1 1 * D 3 3 + D 2 0 * D 3 1 * D 1 3 + D 3 0 * D 1 1 * D 2 3 - D 3 0 * D 2 1 * D 1 3)) (.node 34 (.leaf (fun D => D 1 0 * D 2 2 * D 3 3 - D 1 0 * D 3 2 * D 2 3 - D 2 0 * D 1 2 * D 3 3 + D 2 0 * D 3 2 * D 1 3 + D 3 0 * D 1 2 * D 2 3 - D 3 0 * D 2 2 * D 1 3)) (.leaf (fun D => D 1 1 * D 2 2 * D 3 3 - D 1 1 * D 3 2 * D 2 3 - D 2 1 * D 1 2 * D 3 3 + D 2 1 * D 3 2 * D 1 3 + D 3 1 * D 1 2 * D 2 3 - D 3 1 * D 2 2 * D 1 3)))))))) (.node 52 (.node 43 (.node 39 (.node 37 (.node 36 (.leaf (fun D => -D 0 0)) (.leaf (fun D => -D 0 1))) (.node 38 (.leaf (fun D => -D 0 2)) (.leaf (fun D => -D 0 3)))) (.node 41 (.node 40 (.leaf (fun D => D 0 0 * D 3 1 - D 3 0 * D 0 1)) (.leaf (fun D => D 0 0 * D 3 2 - D 3 0 * D 0 2))) (.node 42 (.leaf (fun D => D 0 0 * D 3 3 - D 3 0 * D 0 3)) (.leaf (fun D => D 0 1 * D 3 2 - D 3 1 * D 0 2))))) (.node 47 (.node 45 (.node 44 (.leaf (fun D => D 0 1 * D 3 3 - D 3 1 * D 0 3)) (.leaf (fun D => D 0 2 * D 3 3 - D 3 2 * D 0 3))) (.node 46 (.leaf (fun D => -D 0 0 * D 2 1 + D 2 0 * D 0 1)) (.leaf (fun D => -D 0 0 * D 2 2 + D 2 0 * D 0 2)))) (.node 49 (.node 48 (.leaf (fun D => -D 0 0 * D 2 3 + D 2 0 * D 0 3)) (.leaf (fun D => -D 0 1 * D 2 2 + D 2 1 * D 0 2))) (.node 50 (.leaf (fun D => -D 0 1 * D 2 3 + D 2 1 * D 0 3)) (.node 51 (.leaf (fun D => -D 0 2 * D 2 3 + D 2 2 * D 0 3)) (.leaf (fun D => -D 0 0 * D 2 1 * D 3 2 + D 0 0 * D 3 1 * D 2 2 + D 2 0 * D 0 1 * D 3 2 - D 2 0 * D 3 1 * D 0 2 - D 3 0 * D 0 1 * D 2 2 + D 3 0 * D 2 1 * D 0 2))))))) (.node 61 (.node 56 (.node 54 (.node 53 (.leaf (fun D => -D 0 0 * D 2 1 * D 3 3 + D 0 0 * D 3 1 * D 2 3 + D 2 0 * D 0 1 * D 3 3 - D 2 0 * D 3 1 * D 0 3 - D 3 0 * D 0 1 * D 2 3 + D 3 0 * D 2 1 * D 0 3)) (.leaf (fun D => -D 0 0 * D 2 2 * D 3 3 + D 0 0 * D 3 2 * D 2 3 + D 2 0 * D 0 2 * D 3 3 - D 2 0 * D 3 2 * D 0 3 - D 3 0 * D 0 2 * D 2 3 + D 3 0 * D 2 2 * D 0 3))) (.node 55 (.leaf (fun D => -D 0 1 * D 2 2 * D 3 3 + D 0 1 * D 3 2 * D 2 3 + D 2 1 * D 0 2 * D 3 3 - D 2 1 * D 3 2 * D 0 3 - D 3 1 * D 0 2 * D 2 3 + D 3 1 * D 2 2 * D 0 3)) (.leaf (fun D => D 0 0 * D 1 1 - D 1 0 * D 0 1)))) (.node 58 (.node 57 (.leaf (fun D => D 0 0 * D 1 2 - D 1 0 * D 0 2)) (.leaf (fun D => D 0 0 * D 1 3 - D 1 0 * D 0 3))) (.node 59 (.leaf (fun D => D 0 1 * D 1 2 - D 1 1 * D 0 2)) (.node 60 (.leaf (fun D => D 0 1 * D 1 3 - D 1 1 * D 0 3)) (.leaf (fun D => D 0 2 * D 1 3 - D 1 2 * D 0 3)))))) (.node 65 (.node 63 (.node 62 (.leaf (fun D => D 0 0 * D 1 1 * D 3 2 - D 0 0 * D 3 1 * D 1 2 - D 1 0 * D 0 1 * D 3 2 + D 1 0 * D 3 1 * D 0 2 + D 3 0 * D 0 1 * D 1 2 - D 3 0 * D 1 1 * D 0 2)) (.leaf (fun D => D 0 0 * D 1 1 * D 3 3 - D 0 0 * D 3 1 * D 1 3 - D 1 0 * D 0 1 * D 3 3 + D 1 0 * D 3 1 * D 0 3 + D 3 0 * D 0 1 * D 1 3 - D 3 0 * D 1 1 * D 0 3))) (.node 64 (.leaf (fun D => D 0 0 * D 1 2 * D 3 3 - D 0 0 * D 3 2 * D 1 3 - D 1 0 * D 0 2 * D 3 3 + D 1 0 * D 3 2 * D 0 3 + D 3 0 * D 0 2 * D 1 3 - D 3 0 * D 1 2 * D 0 3)) (.leaf (fun D => D 0 1 * D 1 2 * D 3 3 - D 0 1 * D 3 2 * D 1 3 - D 1 1 * D 0 2 * D 3 3 + D 1 1 * D 3 2 * D 0 3 + D 3 1 * D 0 2 * D 1 3 - D 3 1 * D 1 2 * D 0 3)))) (.node 67 (.node 66 (.leaf (fun D => -D 0 0 * D 1 1 * D 2 2 + D 0 0 * D 2 1 * D 1 2 + D 1 0 * D 0 1 * D 2 2 - D 1 0 * D 2 1 * D 0 2 - D 2 0 * D 0 1 * D 1 2 + D 2 0 * D 1 1 * D 0 2)) (.leaf (fun D => -D 0 0 * D 1 1 * D 2 3 + D 0 0 * D 2 1 * D 1 3 + D 1 0 * D 0 1 * D 2 3 - D 1 0 * D 2 1 * D 0 3 - D 2 0 * D 0 1 * D 1 3 + D 2 0 * D 1 1 * D 0 3))) (.node 68 (.leaf (fun D => -D 0 0 * D 1 2 * D 2 3 + D 0 0 * D 2 2 * D 1 3 + D 1 0 * D 0 2 * D 2 3 - D 1 0 * D 2 2 * D 0 3 - D 2 0 * D 0 2 * D 1 3 + D 2 0 * D 1 2 * D 0 3)) (.node 69 (.leaf (fun D => -D 0 1 * D 1 2 * D 2 3 + D 0 1 * D 2 2 * D 1 3 + D 1 1 * D 0 2 * D 2 3 - D 1 1 * D 2 2 * D 0 3 - D 2 1 * D 0 2 * D 1 3 + D 2 1 * D 1 2 * D 0 3)) (.leaf (fun D => D 0 0 * D 1 1 * D 2 2 * D 3 3 - D 0 0 * D 1 1 * D 3 2 * D 2 3 - D 0 0 * D 2 1 * D 1 2 * D 3 3 + D 0 0 * D 2 1 * D 3 2 * D 1 3 + D 0 0 * D 3 1 * D 1 2 * D 2 3 - D 0 0 * D 3 1 * D 2 2 * D 1 3 - D 1 0 * D 0 1 * D 2 2 * D 3 3 + D 1 0 * D 0 1 * D 3 2 * D 2 3 + D 1 0 * D 2 1 * D 0 2 * D 3 3 - D 1 0 * D 2 1 * D 3 2 * D 0 3 - D 1 0 * D 3 1 * D 0 2 * D 2 3 + D 1 0 * D 3 1 * D 2 2 * D 0 3 + D 2 0 * D 0 1 * D 1 2 * D 3 3 - D 2 0 * D 0 1 * D 3 2 * D 1 3 - D 2 0 * D 1 1 * D 0 2 * D 3 3 + D 2 0 * D 1 1 * D 3 2 * D 0 3 + D 2 0 * D 3 1 * D 0 2 * D 1 3 - D 2 0 * D 3 1 * D 1 2 * D 0 3 - D 3 0 * D 0 1 * D 1 2 * D 2 3 + D 3 0 * D 0 1 * D 2 2 * D 1 3 + D 3 0 * D 1 1 * D 0 2 * D 2 3 - D 3 0 * D 1 1 * D 2 2 * D 0 3 - D 3 0 * D 2 1 * D 0 2 * D 1 3 + D 3 0 * D 2 1 * D 1 2 * D 0 3))))))))

def minorFormula {R : Type*} [CommRing R]
    (D : Coordinate → Coordinate → R) (i : Fin 70) : R :=
  minorFormulaTree.get i.val D

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem minorFormula_correct {R : Type*} [CommRing R]
    (D : Coordinate → Coordinate → R) (i : Fin 70) :
    ((rowMatrix D).submatrix (minorRows i) id).det = minorFormula D i := by
  rw [det_four]
  fin_cases i <;>
    dsimp [minorFormula, minorFormulaTree, minorRows, minorRowTree,
      Table.get, FormulaTable.get, rowMatrix, Matrix.submatrix, Fin.addCases] <;>
    norm_num <;> ring

def actualMinor {ι : Type*} (D : Coordinate → Coordinate → Entry ι)
    (i : Fin 70) : MvPolynomial ι ℚ :=
  (polynomialMatrix D |>.submatrix (minorRows i) id).det

theorem actualMinor_eq_formula {ι : Type*}
    (D : Coordinate → Coordinate → Entry ι) (i : Fin 70) :
    actualMinor D i = minorFormula (fun r c => (D r c).polynomial) i :=
  minorFormula_correct _ _

/-- A finite table is accepted only with a proof of every actual determinant identity. -/
structure MinorTableCertificate {ι : Type*}
    (D : Coordinate → Coordinate → Entry ι)
    (P : Fin 70 → MvPolynomial ι ℚ) : Prop where
  identity : ∀ i, P i = actualMinor D i

theorem eval_actualMinor {ι R : Type*} [CommRing R]
    (D : Coordinate → Coordinate → Entry ι) (f : ℚ →+* R)
    (x : ι → R) (i : Fin 70) :
    eval₂Hom f x (actualMinor D i) =
      ((valueMatrix D x).submatrix (minorRows i) id).det := by
  have h := (eval₂Hom f x).map_det
    ((polynomialMatrix D).submatrix (minorRows i) id)
  have hm : (eval₂Hom f x).mapMatrix
      ((polynomialMatrix D).submatrix (minorRows i) id) =
      ((polynomialMatrix D).map (eval₂Hom f x)).submatrix (minorRows i) id := rfl
  rw [hm, map_polynomialMatrix] at h
  exact h

theorem MinorTableCertificate.eval_identity {ι R : Type*} [CommRing R]
    {D : Coordinate → Coordinate → Entry ι}
    {P : Fin 70 → MvPolynomial ι ℚ} (C : MinorTableCertificate D P)
    (f : ℚ →+* R) (x : ι → R) (i : Fin 70) :
    eval₂Hom f x (P i) = ((valueMatrix D x).submatrix (minorRows i) id).det := by
  rw [C.identity, eval_actualMinor]

/-- Exact agreement with the catalogue's relabelled complete basis family. -/
structure PatternCertificate (family : Finset (Finset Point))
    (labelCode : ℕ) (basisMark : Fin 70 → Bool) : Prop where
  permutation_valid : ValidPermutation 8 labelCode
  basis_correct : ∀ i, basisMark i = true ↔
    (minorSet i).image (permutationFunction labelCode) ∈ family

/-- Catalogue isomorphisms map original labels to catalogue labels. A
chart's stored label order is therefore transported back by the inverse
catalogue permutation, with this exact membership correspondence. -/
theorem catalogue_label_membership
    (A B : Finset (Finset Point)) (σ label : Equiv.Perm Point)
    (h : A.image (fun S => S.image σ) = B) (S : Finset Point) :
    S.image (label.trans σ.symm) ∈ A ↔ S.image label ∈ B := by
  have hmap : (S.image (label.trans σ.symm)).image σ = S.image label := by
    simp only [Finset.image_image, Function.comp_def, Equiv.trans_apply,
      Equiv.apply_symm_apply]
  rw [← h]
  constructor
  · intro hS
    exact Finset.mem_image.mpr ⟨S.image (label.trans σ.symm), hS, hmap⟩
  · intro hS
    obtain ⟨T, hT, hTS⟩ := Finset.mem_image.mp hS
    have heq : T = S.image (label.trans σ.symm) :=
      (Finset.image_injective σ.injective) (hTS.trans hmap.symm)
    exact heq ▸ hT

theorem PatternCertificate.original_basis_iff
    {A B : Finset (Finset Point)} {labelCode : ℕ} {basisMark : Fin 70 → Bool}
    (C : PatternCertificate B labelCode basisMark) (σ : Equiv.Perm Point)
    (h : A.image (fun S => S.image σ) = B) (i : Fin 70) :
    (minorSet i).image
      ((checkedPermutation 8 labelCode C.permutation_valid).trans σ.symm) ∈ A ↔
        basisMark i = true := by
  rw [catalogue_label_membership A B σ _ h]
  exact (C.basis_correct i).symm

def exchangeSet (i j : Coordinate) : Finset Point :=
  univ.image (Function.update firstFour i (lastFour j))

/-- The zero/nonzero support of the nonbasis block follows from actual
basis exchange. This certificate is used only for an original exact chart;
a chart obtained by relaxing a zero entry need not satisfy this predicate. -/
structure CoordinateSupportCertificate {ι : Type*}
    (family : Finset (Finset Point)) (labelCode : ℕ)
    (D : Coordinate → Coordinate → Entry ι) : Prop where
  support_correct : ∀ i j, D i j ≠ .zero ↔
    (exchangeSet i j).image (permutationFunction labelCode) ∈ family

/-- Entry constraints sufficient for a prescribed chart, including charts
where one zero entry is replaced by an additional unrestricted variable. -/
structure EntryConstraintCertificate {ι : Type*} {u : ℕ}
    (family : Finset (Finset Point)) (labelCode : ℕ)
    (D : Coordinate → Coordinate → Entry ι)
    (position : ι → Coordinate × Coordinate) (unitVariables : Fin u → ι) : Prop where
  zero_correct : ∀ i j, D i j = .zero →
    (exchangeSet i j).image (permutationFunction labelCode) ∉ family
  one_nonzero : ∀ i j, D i j = .one →
    (exchangeSet i j).image (permutationFunction labelCode) ∈ family
  unit_nonzero : ∀ k,
    (exchangeSet (position (unitVariables k)).1 (position (unitVariables k)).2).image
      (permutationFunction labelCode) ∈ family

/-- The literal elimination equations are precisely all prescribed
zero minor polynomials, allowing repeated entries and omitting zero polynomials. -/
structure EquationTableCertificate {ι : Type*} {m : ℕ}
    (requiredZero : Fin 70 → Bool) (P : Fin 70 → MvPolynomial ι ℚ)
    (E : Fin m → MvPolynomial ι ℚ) : Prop where
  origin : ∀ j, ∃ i, requiredZero i = true ∧ E j = P i
  coverage : ∀ i, requiredZero i = true → P i = 0 ∨ ∃ j, E j = P i

/-- This is the exact semantic bridge to the system accepted by the
rational elimination lemmas. No JSON status flag enters the theorem. -/
theorem equations_iff_required_zero_minors {ι R : Type*} [CommRing R] {m : ℕ}
    {D : Coordinate → Coordinate → Entry ι}
    {P : Fin 70 → MvPolynomial ι ℚ} {E : Fin m → MvPolynomial ι ℚ}
    {requiredZero : Fin 70 → Bool}
    (C : MinorTableCertificate D P)
    (Q : EquationTableCertificate requiredZero P E)
    (f : ℚ →+* R) (x : ι → R) :
    (∀ j, eval₂Hom f x (E j) = 0) ↔
      ∀ i, requiredZero i = true →
        ((valueMatrix D x).submatrix (minorRows i) id).det = 0 := by
  constructor
  · intro h i hi
    rw [← C.eval_identity f x i]
    rcases Q.coverage i hi with hz | ⟨j, hj⟩
    · rw [hz, map_zero]
    · rw [← hj]
      exact h j
  · intro h j
    obtain ⟨i, hi, hij⟩ := Q.origin j
    rw [hij, C.eval_identity]
    exact h i hi

end Papers.RationalityTen.MatroidChecked.ChartPolynomial
