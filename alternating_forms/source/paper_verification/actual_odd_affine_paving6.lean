module

public import paper_verification.literal001
import all paper_verification.literal001
public import Mathlib.Algebra.MvPolynomial.Variables
public import Mathlib.RingTheory.MvPolynomial.Ideal
public import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous
public import Mathlib.Tactic.Ring
public import Lean.Elab.Tactic.Omega
public import Mathlib.LinearAlgebra.Matrix.BilinearForm
public import Mathlib.Data.Finset.Prod
public import Mathlib.Algebra.MvPolynomial.PDeriv
public import paper_verification.literal005
import all paper_verification.literal005
public import paper_verification.ambient_base2
import all paper_verification.ambient_base2
public import Mathlib.RingTheory.Ideal.Quotient.PowTransition
public import paper_verification.section_four_geometry1
import all paper_verification.section_four_geometry1
public import paper_verification.fixed_plane_count3
import all paper_verification.fixed_plane_count3
import Lean.Util.CollectAxioms
import Lean.Util.FoldConsts
import Lean.PrettyPrinter

set_option Elab.async false

section ComponentSource_0
/- Original module: PaperVerification.TriangularPolynomialCoordinates -/


/-!
# Triangular polynomial coordinates

A change of coordinates `X i ↦ X i + p i` is an actual polynomial algebra
isomorphism when every variable occurring in `p i` has smaller natural-number
weight. Its inverse is constructed by well-founded recursion, rather than
assumed from a Jacobian condition. Consequently, any subset of these
coordinates cuts out an affine space, with its full scheme-theoretic ideal.

This is the algebraic elimination step needed for positive-weight attracting
charts. No assertion about an attracting chart or its smoothness is included
in the hypotheses by definition.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

namespace PaperVerification.TriangularPolynomialCoordinates

open MvPolynomial

variable {R σ : Type*} [CommRing R]

local instance : DecidableEq σ := Classical.decEq σ

lemma aeval_eq_of_eq_on_vars {A : Type*} [CommRing A] [Algebra R A]
    (p : MvPolynomial σ R) {g h : σ → A}
    (hh : ∀ i ∈ p.vars, g i = h i) : aeval g p = aeval h p :=
  eval₂Hom_congr' rfl (fun i hi _ => hh i hi) rfl

/-- Recursive inverse coordinates. Only smaller weights are evaluated
recursively; values on all other variables are irrelevant under triangularity. -/
def inverseCoordinate (w : σ → ℕ) (p : σ → MvPolynomial σ R)
    (i : σ) : MvPolynomial σ R :=
  X i - aeval (fun j => if h : w j < w i then inverseCoordinate w p j else 0) (p i)
termination_by w i

/-- The forward substitution associated to a triangular family. -/
def substitution (p : σ → MvPolynomial σ R) :
    MvPolynomial σ R →ₐ[R] MvPolynomial σ R :=
  aeval (fun i => X i + p i)

@[simp] theorem substitution_X (p : σ → MvPolynomial σ R) (i : σ) :
    substitution p (X i) = X i + p i := by simp [substitution]

theorem substitution_inverseCoordinate (w : σ → ℕ) (p : σ → MvPolynomial σ R)
    (hp : ∀ i j, j ∈ (p i).vars → w j < w i) (i : σ) :
    substitution p (inverseCoordinate w p i) = X i := by
  induction h : w i using Nat.strong_induction_on generalizing i with
  | h n ih =>
    rw [inverseCoordinate, map_sub, substitution_X, comp_aeval_apply]
    have he : aeval
        (fun j => substitution p (if h : w j < w i then inverseCoordinate w p j else 0))
        (p i) = p i := by
      calc
        _ = aeval (fun j => X j) (p i) := by
          apply aeval_eq_of_eq_on_vars
          intro j hj
          rw [dite_eq_left (hp i j hj)]
          exact ih (w j) (h ▸ hp i j hj) j rfl
        _ = p i := aeval_X_left_apply (p i)
    rw [he]
    ring

theorem inverseCoordinate_substitution (w : σ → ℕ) (p : σ → MvPolynomial σ R)
    (hp : ∀ i j, j ∈ (p i).vars → w j < w i) (i : σ) :
    aeval (inverseCoordinate w p) (substitution p (X i)) = X i := by
  rw [substitution_X, map_add, aeval_X, inverseCoordinate]
  have he : aeval
      (fun j => if h : w j < w i then inverseCoordinate w p j else 0) (p i) =
      aeval (inverseCoordinate w p) (p i) := by
    apply aeval_eq_of_eq_on_vars
    intro j hj
    rw [dite_eq_left (hp i j hj)]
  rw [he]
  ring

/-- An actual polynomial algebra automorphism, including both inverse laws. -/
def triangularEquiv (w : σ → ℕ) (p : σ → MvPolynomial σ R)
    (hp : ∀ i j, j ∈ (p i).vars → w j < w i) :
    MvPolynomial σ R ≃ₐ[R] MvPolynomial σ R :=
  AlgEquiv.ofAlgHom (substitution p) (aeval (inverseCoordinate w p))
    (by
      apply MvPolynomial.algHom_ext
      intro i
      simpa only [AlgHom.comp_apply, aeval_X, AlgHom.id_apply] using
        substitution_inverseCoordinate w p hp i)
    (by
      apply MvPolynomial.algHom_ext
      intro i
      simpa only [AlgHom.comp_apply, AlgHom.id_apply] using
        inverseCoordinate_substitution w p hp i)

@[simp] theorem triangularEquiv_X (w : σ → ℕ) (p : σ → MvPolynomial σ R)
    (hp : ∀ i j, j ∈ (p i).vars → w j < w i) (i : σ) :
    triangularEquiv w p hp (X i) = X i + p i := by
  exact substitution_X p i

/-- Set the coordinates in `s` equal to zero and retain the others. -/
def eraseCoordinates (s : Set σ) :
    MvPolynomial σ R →ₐ[R] MvPolynomial {i // i ∉ s} R := by
  classical
  exact aeval (fun i => if h : i ∉ s then X ⟨i,h⟩ else 0)

@[simp] theorem eraseCoordinates_rename (s : Set σ)
    (q : MvPolynomial {i // i ∉ s} R) :
    eraseCoordinates s (rename Subtype.val q) = q := by
  classical
  have h : (eraseCoordinates (R := R) s).comp (rename Subtype.val) = AlgHom.id R _ := by
    ext i
    simp [eraseCoordinates, i.property]
  exact DFunLike.congr_fun h q

theorem eraseCoordinates_surjective (s : Set σ) :
    Function.Surjective (eraseCoordinates (R := R) s) :=
  fun q => ⟨rename Subtype.val q, eraseCoordinates_rename s q⟩

theorem ker_eraseCoordinates (s : Set σ) :
    RingHom.ker (eraseCoordinates (R := R) s).toRingHom =
      Ideal.span (X '' s : Set (MvPolynomial σ R)) := by
  classical
  rw [span_X_image_eq_ker_aeval_ite_mem]
  ext q
  rw [RingHom.mem_ker, RingHom.mem_ker]
  have he : (rename Subtype.val : MvPolynomial {i // i ∉ s} R →ₐ[R] MvPolynomial σ R)
      (eraseCoordinates s q) = aeval (fun i => if i ∈ sᶜ then X i else 0) q := by
    have h : (rename Subtype.val).comp (eraseCoordinates (R := R) s) =
        aeval (fun i => if i ∈ sᶜ then X i else 0) := by
      ext i
      simp only [AlgHom.comp_apply, eraseCoordinates, aeval_X]
      split_ifs <;> simp_all
    exact DFunLike.congr_fun h q
  rw [← he]
  constructor
  · intro hz
    change eraseCoordinates s q = 0 at hz
    rw [hz,map_zero]
  · intro hz
    change eraseCoordinates s q = 0
    apply rename_injective Subtype.val Subtype.val_injective
    simpa only [map_zero] using hz

/-- The coordinate ideal has the expected polynomial quotient, over any
commutative coefficient ring. -/
def coordinateQuotientEquiv (s : Set σ) :
    (MvPolynomial σ R ⧸ Ideal.span (X '' s : Set (MvPolynomial σ R))) ≃ₐ[R]
      MvPolynomial {i // i ∉ s} R :=
  (Ideal.quotientEquivAlgOfEq R (ker_eraseCoordinates (R := R) s).symm).trans
    (Ideal.quotientKerAlgEquivOfSurjective (eraseCoordinates_surjective (R := R) s))

/-- Triangular equations cut out a genuine affine coordinate ring: the
ideal here is literally generated by `X i + p i` for `i ∈ s`. -/
def triangularQuotientEquiv (w : σ → ℕ) (p : σ → MvPolynomial σ R)
    (hp : ∀ i j, j ∈ (p i).vars → w j < w i) (s : Set σ) :
    (MvPolynomial σ R ⧸ Ideal.span ((fun i => X i + p i) '' s)) ≃ₐ[R]
      MvPolynomial {i // i ∉ s} R := by
  let e := triangularEquiv w p hp
  have heval : e.toRingHom ∘ X = (fun i => X i + p i) := by
    funext i
    exact triangularEquiv_X w p hp i
  have he : Ideal.span ((fun i => X i + p i) '' s) =
      (Ideal.span (X '' s)).map e.toRingHom := by
    rw [Ideal.map_span,Set.image_image]
    change Ideal.span ((fun i => X i + p i) '' s) = Ideal.span ((e.toRingHom ∘ X) '' s)
    rw [heval]
  exact (Ideal.quotientEquivAlg _ _ e he).symm.trans (coordinateQuotientEquiv s)

/-- A positive weighted homogeneous polynomial with zero linear part uses
only variables of strictly smaller weight than its degree. -/
theorem vars_lt_weight_of_no_linear_terms (w : σ → ℕ) (hw : ∀ i, 0 < w i)
    (f : MvPolynomial σ R) (d : ℕ) (hf : f.IsWeightedHomogeneous w d)
    (hlin : ∀ i, f.coeff (Finsupp.single i 1) = 0)
    (j : σ) (hj : j ∈ f.vars) : w j < d := by
  classical
  letI : Finsupp.NonTorsionWeight ℕ w :=
    Finsupp.nonTorsionWeight_of ℕ w (fun i => ne_of_gt (hw i))
  obtain ⟨a,ha,hja⟩ := (mem_vars_iff_mem_support (p := f) j).mp hj
  have haj : a j ≠ 0 := Finsupp.mem_support_iff.mp hja
  have hdegree : Finsupp.weight w a = d := hf (mem_support_iff.mp ha)
  have hne : a ≠ Finsupp.single j 1 := by
    intro he
    exact (mem_support_iff.mp ha) (by simpa only [he] using hlin j)
  have hres : a - Finsupp.single j 1 ≠ 0 := by
    intro hz
    apply hne
    have hh := Finsupp.sub_add_single_one_cancel haj
    rw [hz, zero_add] at hh
    exact hh.symm
  have hpos : 0 < Finsupp.weight w (a - Finsupp.single j 1) :=
    Nat.pos_of_ne_zero (fun hz => hres ((Finsupp.weight_eq_zero_iff_eq_zero w).mp hz))
  have hh := Finsupp.weight_sub_single_add (w := w) haj
  rw [hdegree] at hh
  omega

/-- The nonlinear remainders of positive weighted homogeneous equations
with normalized independent linear terms satisfy the triangular condition. -/
theorem normalized_homogeneous_triangular (w : σ → ℕ) (hw : ∀ i, 0 < w i)
    (F : σ → MvPolynomial σ R)
    (hF : ∀ i, (F i).IsWeightedHomogeneous w (w i))
    (hlin : ∀ i j, (F i).coeff (Finsupp.single j 1) = if j = i then 1 else 0) :
    ∀ i j, j ∈ (F i - X i).vars → w j < w i := by
  classical
  intro i j hj
  apply vars_lt_weight_of_no_linear_terms w hw (F i - X i) (w i)
    ((hF i).sub (isWeightedHomogeneous_X R w i)) _ j hj
  intro q
  simp [hlin, coeff_single_X, eq_comm]

/-- A normalized positive weighted homogeneous family is a polynomial
coordinate system. This is stronger than a set-theoretic parametrization. -/
def homogeneousCoordinateEquiv (w : σ → ℕ) (hw : ∀ i, 0 < w i)
    (F : σ → MvPolynomial σ R)
    (hF : ∀ i, (F i).IsWeightedHomogeneous w (w i))
    (hlin : ∀ i j, (F i).coeff (Finsupp.single j 1) = if j = i then 1 else 0) :
    MvPolynomial σ R ≃ₐ[R] MvPolynomial σ R :=
  triangularEquiv w (fun i => F i - X i)
    (normalized_homogeneous_triangular w hw F hF hlin)

@[simp] theorem homogeneousCoordinateEquiv_X (w : σ → ℕ) (hw : ∀ i, 0 < w i)
    (F : σ → MvPolynomial σ R)
    (hF : ∀ i, (F i).IsWeightedHomogeneous w (w i))
    (hlin : ∀ i j, (F i).coeff (Finsupp.single j 1) = if j = i then 1 else 0)
    (i : σ) : homogeneousCoordinateEquiv w hw F hF hlin (X i) = F i := by
  simp [homogeneousCoordinateEquiv]

end PaperVerification.TriangularPolynomialCoordinates
end
end
end ComponentSource_0

run_cmd Lean.logInfo "COMPONENT_SOURCE_END: PaperVerification.TriangularPolynomialCoordinates"

section ComponentSource_1
/- Original module: PaperVerification.IsotropicAttractingCoordinates -/


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
end
end
end ComponentSource_1

run_cmd Lean.logInfo "COMPONENT_SOURCE_END: PaperVerification.IsotropicAttractingCoordinates"

section ComponentSource_2
/- Original module: PaperVerification.IsotropicAttractingPivots -/


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
end
end
end ComponentSource_2

run_cmd Lean.logInfo "COMPONENT_SOURCE_END: PaperVerification.IsotropicAttractingPivots"

section ComponentSource_3
/- Original module: PaperVerification.IsotropicAttractingIdeal -/


/-!
# The full scheme-theoretic ideal on an attracting cell

Both original alternating forms, on every ordered pair of universal rows,
generate exactly the ideal indexed by the increasing low pivot pairs.  The
argument works over every commutative coefficient ring: diagonal pairings
vanish by pairwise cancellation, not by division by two.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

namespace PaperVerification.IsotropicAttractingCoordinates

open MvPolynomial
open scoped BigOperators

variable {R : Type*} [CommRing R] {n s : ℕ}

@[simp] theorem formMatrix_self (c : ℕ) (a : Fin n) :
    formMatrix (R := R) c a a = 0 := by
  simp [formMatrix]

theorem formMatrix_swap (c : ℕ) (a b : Fin n) :
    formMatrix (R := R) c b a = -formMatrix c a b := by
  unfold formMatrix
  by_cases hab : a.val + b.val = c
  · have hba : b.val + a.val = c := by omega
    rw [ite_eq_left hab, ite_eq_left hba]
    rcases lt_trichotomy a b with h | h | h
    · simp [h, not_lt_of_gt h]
    · simp [h]
    · simp [h, not_lt_of_gt h]
  · have hba : b.val + a.val ≠ c := by omega
    simp [hab, hba]

/-- Swapping the two universal rows negates the original pairing. -/
theorem equation_swap (p : Fin s ↪ Fin n) (c : ℕ) (i j : Fin s) :
    equation (R := R) p c j i = -equation p c i j := by
  classical
  unfold equation
  calc
    _ = ∑ a : Fin n, ∑ b : Fin n,
        C (formMatrix (R := R) c b a) * row p j b * row p i a :=
      Finset.sum_comm
    _ = ∑ a : Fin n, ∑ b : Fin n,
        -(C (formMatrix (R := R) c a b) * row p i a * row p j b) := by
      apply Finset.sum_congr rfl
      intro a _
      apply Finset.sum_congr rfl
      intro b _
      rw [formMatrix_swap, map_neg]
      ring
    _ = _ := by simp

/-- Diagonal pairings vanish over arbitrary commutative rings, including
characteristic two; no cancellation of the scalar two is used. -/
@[simp] theorem equation_self (p : Fin s ↪ Fin n) (c : ℕ) (i : Fin s) :
    equation (R := R) p c i i = 0 := by
  classical
  unfold equation
  rw [← Finset.sum_product']
  apply Finset.sum_ninvolution Prod.swap
  · intro q
    dsimp only [Prod.swap]
    rw [formMatrix_swap, map_neg]
    ring
  · intro q hq he
    have h : q.2 = q.1 := congrArg Prod.fst he
    apply hq
    simp [h]
  · intro q
    simp
  · intro q
    rfl

variable {k : ℕ} {p : Fin s ↪ Fin (2*k+1)}

/-- The complete list of nonzero positive-weight row-pair equations. -/
def lowEquation : LowPair p ⊕ LowPair p → MvPolynomial (Coordinate p) R :=
  Sum.elim (fun q => equation p (2*k+1) q.val.1 q.val.2)
    (fun q => equation p (2*k) q.val.1 q.val.2)

def lowIdeal : Ideal (MvPolynomial (Coordinate p) R) :=
  Ideal.span (Set.range (lowEquation (R := R) (p := p)))

theorem lowIdeal_le_isotropyIdeal :
    lowIdeal (R := R) (p := p) ≤ isotropyIdeal p (2*k+1) (2*k) := by
  apply Ideal.span_le.mpr
  rintro _ ⟨q, rfl⟩
  apply Ideal.subset_span
  cases q with
  | inl q => exact ⟨(true, q.val.1, q.val.2), rfl⟩
  | inr q => exact ⟨(false, q.val.1, q.val.2), rfl⟩

theorem ordered_equation_mem_lowIdeal (hp : IndependentPivots p)
    (c : ℕ) (hc : c = 2*k+1 ∨ c = 2*k) (i j : Fin s)
    (hij : p i < p j) :
    equation (R := R) p c i j ∈ lowIdeal (p := p) := by
  by_cases hlow : (p i).val + (p j).val < 2*k
  · let q : LowPair p := ⟨(i,j), hij, hlow⟩
    apply Ideal.subset_span
    rcases hc with rfl | rfl
    · exact ⟨Sum.inl q, rfl⟩
    · exact ⟨Sum.inr q, rfl⟩
  · have hne : i ≠ j := by
      intro h
      simp [h] at hij
    have hind := hp i j hne
    have hneg : c < (p i).val + (p j).val := by
      rcases hc with rfl | rfl <;> omega
    rw [equation_eq_zero_of_negative_weight p c i j hneg]
    exact Ideal.zero_mem _

theorem equation_mem_lowIdeal (hp : IndependentPivots p)
    (c : ℕ) (hc : c = 2*k+1 ∨ c = 2*k) (i j : Fin s) :
    equation (R := R) p c i j ∈ lowIdeal (p := p) := by
  rcases lt_trichotomy (p i) (p j) with hij | hij | hij
  · exact ordered_equation_mem_lowIdeal hp c hc i j hij
  · have he := p.injective hij
    subst j
    rw [equation_self]
    exact Ideal.zero_mem _
  · rw [equation_swap p c j i]
    exact neg_mem (ordered_equation_mem_lowIdeal hp c hc j i hij)

/-- Equality with the full original ideal. This retains all nilpotent and
scheme-theoretic information; it is not a set-theoretic comparison. -/
theorem isotropyIdeal_eq_lowIdeal (hp : IndependentPivots p) :
    isotropyIdeal (R := R) p (2*k+1) (2*k) = lowIdeal (p := p) := by
  apply le_antisymm
  · apply Ideal.span_le.mpr
    rintro _ ⟨q, rfl⟩
    apply equation_mem_lowIdeal hp
    cases q.1 <;> simp
  · exact lowIdeal_le_isotropyIdeal

end PaperVerification.IsotropicAttractingCoordinates
end
end
end ComponentSource_3

run_cmd Lean.logInfo "COMPONENT_SOURCE_END: PaperVerification.IsotropicAttractingIdeal"

section ComponentSource_4
/- Original module: PaperVerification.IsotropicAttractingPairing -/


/-!
# Agreement with the original alternating-form coefficients

The attracting equations use full skew matrices.  The original Plücker
charts use the coefficients on strictly increasing pairs.  This file
proves their equality over every commutative ring, retaining the signs and
without dividing the full matrix sum by two.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

namespace PaperVerification.IsotropicAttractingCoordinates

open MvPolynomial
open scoped BigOperators

variable {R A : Type*} [CommRing R] [CommRing A] {n s : ℕ}

theorem map_formMatrix (φ : R →+* A) (c : ℕ) (i j : Fin n) :
    φ (formMatrix c i j) = formMatrix c i j := by
  unfold formMatrix
  split_ifs <;> simp

theorem sum_strictPairs (f : Fin n × Fin n → R) :
    (∑ q : {q : Fin n × Fin n // q.1 < q.2}, f q.val) =
      ∑ i : Fin n, ∑ j : Fin n, if i < j then f (i,j) else 0 := by
  classical
  rw [← Finset.sum_subtype (Finset.univ.filter (fun q : Fin n × Fin n => q.1 < q.2))
    (by simp)]
  rw [Finset.sum_filter]
  exact Fintype.sum_prod_type _

/-- The full skew-matrix pairing is exactly the original increasing-pair
coefficient formula. -/
theorem formMatrix_pairing_eq (c : ℕ) (u v : Fin n → R) :
    (∑ i : Fin n, ∑ j : Fin n, formMatrix c i j * u i * v j) =
      ∑ q : {q : Fin n × Fin n // q.1 < q.2},
        formMatrix c q.val.1 q.val.2 *
          (u q.val.1 * v q.val.2 - u q.val.2 * v q.val.1) := by
  classical
  have hsplit (i j : Fin n) : formMatrix c i j * u i * v j =
      (if i < j then formMatrix c i j * u i * v j else 0) +
        (if j < i then formMatrix c i j * u i * v j else 0) := by
    rcases lt_trichotomy i j with h | h | h
    · simp [h, not_lt_of_gt h]
    · subst j
      simp
    · simp [h, not_lt_of_gt h]
  calc
    _ = (∑ i : Fin n, ∑ j : Fin n,
        if i < j then formMatrix c i j * u i * v j else 0) +
      ∑ i : Fin n, ∑ j : Fin n,
        if j < i then formMatrix c i j * u i * v j else 0 := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro i _
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro j _
      exact hsplit i j
    _ = (∑ i : Fin n, ∑ j : Fin n,
        if i < j then formMatrix c i j * u i * v j else 0) +
      ∑ i : Fin n, ∑ j : Fin n,
        if i < j then formMatrix c j i * u j * v i else 0 := by
      congr 1
      exact Finset.sum_comm
    _ = ∑ i : Fin n, ∑ j : Fin n, if i < j then
        formMatrix c i j * (u i * v j - u j * v i) else 0 := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro i _
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro j _
      split_ifs
      · rw [formMatrix_swap]
        ring
      · ring
    _ = _ := (sum_strictPairs (fun q : Fin n × Fin n =>
      formMatrix c q.1 q.2 * (u q.1 * v q.2 - u q.2 * v q.1))).symm

/-- The exact Plücker-chart convention for the same canonical equations. -/
theorem equation_eq_increasing_pair_sum (p : Fin s ↪ Fin n) (c : ℕ) (i j : Fin s) :
    equation (R := R) p c i j =
      ∑ q : {q : Fin n × Fin n // q.1 < q.2},
        C (formMatrix (R := R) c q.val.1 q.val.2) *
          (row p i q.val.1 * row p j q.val.2 - row p i q.val.2 * row p j q.val.1) := by
  simp only [equation, map_formMatrix]
  exact formMatrix_pairing_eq c (row p i) (row p j)

end PaperVerification.IsotropicAttractingCoordinates
end
end
end ComponentSource_4

run_cmd Lean.logInfo "COMPONENT_SOURCE_END: PaperVerification.IsotropicAttractingPairing"

section ComponentSource_5
/- Original module: PaperVerification.IsotropicAttractingLinearTerms -/


/-!
# Exact linear terms of the attracting-chart equations

The coefficient of each variable is computed in the literal polynomial
equation.  This separates the two possible linear terms from quadratic
terms, whose variables have smaller positive weight.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

namespace PaperVerification.IsotropicAttractingCoordinates

open MvPolynomial
open scoped BigOperators

variable {R σ : Type*} [CommRing R]

/-- The product rule for the coefficient of a single variable. -/
theorem coeff_single_mul (f g : MvPolynomial σ R) (i : σ) :
    (f*g).coeff (Finsupp.single i 1) =
      f.coeff (Finsupp.single i 1) * g.constantCoeff +
        f.constantCoeff * g.coeff (Finsupp.single i 1) := by
  have h := congrArg (fun q : MvPolynomial σ R => q.constantCoeff)
    (pderiv_mul (i := i) (f := f) (g := g))
  simpa only [map_add, map_mul, constantCoeff_eq, coeff_pderiv,
    Finsupp.zero_apply, zero_add, Nat.cast_zero, Nat.cast_one, mul_one] using h

/-- A variable in a positive-weight homogeneous polynomial either has
smaller weight, or already occurs in the polynomial's linear part. -/
theorem vars_lt_weight_or_linear (w : σ → ℕ) (hw : ∀ i, 0 < w i)
    (f : MvPolynomial σ R) (d : ℕ) (hf : f.IsWeightedHomogeneous w d)
    (j : σ) (hj : j ∈ f.vars) :
    w j < d ∨ f.coeff (Finsupp.single j 1) ≠ 0 := by
  classical
  letI : Finsupp.NonTorsionWeight ℕ w :=
    Finsupp.nonTorsionWeight_of ℕ w (fun i => ne_of_gt (hw i))
  obtain ⟨a, ha, hja⟩ := (mem_vars_iff_mem_support (p := f) j).mp hj
  by_cases he : a = Finsupp.single j 1
  · right
    simpa only [he] using mem_support_iff.mp ha
  · left
    have haj : a j ≠ 0 := Finsupp.mem_support_iff.mp hja
    have hd : Finsupp.weight w a = d := hf (mem_support_iff.mp ha)
    have hres : a - Finsupp.single j 1 ≠ 0 := by
      intro hz
      apply he
      have hh := Finsupp.sub_add_single_one_cancel haj
      rw [hz, zero_add] at hh
      exact hh.symm
    have hpos : 0 < Finsupp.weight w (a - Finsupp.single j 1) :=
      Nat.pos_of_ne_zero (fun hz => hres ((Finsupp.weight_eq_zero_iff_eq_zero w).mp hz))
    have hh := Finsupp.weight_sub_single_add (w := w) haj
    rw [hd] at hh
    omega

variable {n s : ℕ}

@[simp] theorem row_constantCoeff (p : Fin s ↪ Fin n) (i : Fin s) (j : Fin n) :
    (row (R := R) p i j).constantCoeff = if j = p i then 1 else 0 := by
  classical
  rw [row]
  split
  · simp_all
  · split
    · change (X (⟨(i,j), ‹_›⟩ : Coordinate p) : MvPolynomial (Coordinate p) R).constantCoeff = _
      simp_all
    · simp_all

/-- The universal row has exactly its specified variable as linear term. -/
theorem row_coeff_single (p : Fin s ↪ Fin n) (i : Fin s) (j : Fin n)
    (v : Coordinate p) :
    (row (R := R) p i j).coeff (Finsupp.single v 1) =
      if v.val.1 = i ∧ v.val.2 = j then 1 else 0 := by
  classical
  by_cases h : j = p i
  · have hn : ¬ (v.val.1 = i ∧ v.val.2 = j) := by
      rintro ⟨hi, hv⟩
      apply v.property.2
      exact ⟨i, h.symm.trans hv.symm⟩
    have hzero : (0 : Coordinate p →₀ ℕ) ≠ Finsupp.single v 1 := by
      intro hz
      have hh := congrArg (fun f : Coordinate p →₀ ℕ => f v) hz
      simp at hh
    rw [ite_eq_right hn, row, ite_eq_left h]
    simp only [coeff_one, ite_eq_right hzero]
  · rw [row, ite_eq_right h]
    by_cases hj : (p i).val < j.val ∧ j ∉ Set.range p
    · rw [dite_eq_left hj]
      change (X (⟨(i,j),hj⟩ : Coordinate p) : MvPolynomial (Coordinate p) R).coeff
        (Finsupp.single v 1) = _
      have he : ((⟨(i,j),hj⟩ : Coordinate p) = v) ↔
          v.val.1 = i ∧ v.val.2 = j := by
        rw [Subtype.ext_iff, Prod.ext_iff]
        simp only [eq_comm]
      simp [coeff_single_X, he]
    · rw [dite_eq_right hj]
      have hn : ¬ (v.val.1 = i ∧ v.val.2 = j) := by
        rintro ⟨hi, hv⟩
        apply hj
        simpa only [hi, hv] using v.property
      simp [hn]

/-- The linear coefficient is the differential of the original pairing:
one term moves the first row, and one moves the second row. -/
theorem equation_coeff_single (p : Fin s ↪ Fin n) (c : ℕ) (i j : Fin s)
    (v : Coordinate p) :
    (equation (R := R) p c i j).coeff (Finsupp.single v 1) =
      (if v.val.1 = i then formMatrix c v.val.2 (p j) else 0) +
        (if v.val.1 = j then formMatrix c (p i) v.val.2 else 0) := by
  classical
  simp only [equation, coeff_sum]
  simp_rw [mul_assoc, coeff_C_mul, coeff_single_mul,
    row_coeff_single, row_constantCoeff, mul_add, Finset.sum_add_distrib]
  by_cases hij : i = j
  · subst j
    by_cases hi : v.val.1 = i <;> simp [hi, mul_ite, ite_mul, eq_comm]
  · by_cases hi : v.val.1 = i <;> by_cases hj : v.val.1 = j <;>
      simp [hi, hj, hij, Ne.symm hij, mul_ite, ite_mul, eq_comm]

/-- Nonzero linear coefficients must come from one of the two original
anti-diagonal edges, with the indicated row. -/
theorem equation_linear_support (p : Fin s ↪ Fin n) (c : ℕ) (i j : Fin s)
    (v : Coordinate p)
    (hv : (equation (R := R) p c i j).coeff (Finsupp.single v 1) ≠ 0) :
    (v.val.1 = i ∧ v.val.2.val + (p j).val = c) ∨
      (v.val.1 = j ∧ (p i).val + v.val.2.val = c) := by
  classical
  rw [equation_coeff_single] at hv
  by_contra h
  have hfirst : (if v.val.1 = i then formMatrix (R := R) c v.val.2 (p j) else 0) = 0 := by
    split_ifs with hi
    · apply formMatrix_eq_zero_of_ne
      intro he
      exact h (Or.inl ⟨hi, he⟩)
    · rfl
  have hsecond : (if v.val.1 = j then formMatrix (R := R) c (p i) v.val.2 else 0) = 0 := by
    split_ifs with hj
    · apply formMatrix_eq_zero_of_ne
      intro he
      exact h (Or.inr ⟨hj, he⟩)
    · rfl
  exact hv (by rw [hfirst, hsecond, zero_add])

end PaperVerification.IsotropicAttractingCoordinates
end
end
end ComponentSource_5

run_cmd Lean.logInfo "COMPONENT_SOURCE_END: PaperVerification.IsotropicAttractingLinearTerms"

section ComponentSource_6
/- Original module: PaperVerification.IsotropicAttractingRank -/


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
end
end
end ComponentSource_6

run_cmd Lean.logInfo "COMPONENT_SOURCE_END: PaperVerification.IsotropicAttractingRank"

section ComponentSource_7
/- Original module: PaperVerification.IsotropicAttractingElimination -/


/-!
# Explicit affine coordinate rings for every nonempty attracting chart

The original two isotropy equations form a triangular system with unit
pivots.  The resulting equivalence concerns the quotient by the full
original ideal, over every commutative coefficient ring.  The remaining
variables are exactly the row entries outside the chosen equation pivots.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

namespace PaperVerification.IsotropicAttractingCoordinates

open MvPolynomial

variable {R : Type*} [CommRing R] {k s : ℕ} {p : Fin s ↪ Fin (2*k+1)}

def normalizer : LowPair p ⊕ LowPair p → R :=
  Sum.elim (fun q => if (p q.val.2).val ≤ k then 1 else -1) (fun _ => -1)

theorem normalizer_square (q : LowPair p ⊕ LowPair p) :
    normalizer (R := R) q * normalizer q = 1 := by
  cases q with
  | inl q => simp only [normalizer, Sum.elim_inl]; split <;> simp
  | inr q => simp [normalizer]

/-- Each literal equation is multiplied by its chosen coefficient, which
is its own inverse. -/
def normalizedEquation (q : LowPair p ⊕ LowPair p) : MvPolynomial (Coordinate p) R :=
  C (normalizer q) * lowEquation q

theorem normalizedEquation_homogeneous (hp : IndependentPivots p)
    (q : LowPair p ⊕ LowPair p) :
    (normalizedEquation (R := R) q).IsWeightedHomogeneous (coordinateWeight p)
      (coordinateWeight p (pivotEmbedding hp q)) := by
  unfold normalizedEquation
  cases q with
  | inl q =>
      change (C (normalizer (Sum.inl q)) * equation p (2*k+1) q.val.1 q.val.2).IsWeightedHomogeneous
        (coordinateWeight p) (coordinateWeight p (firstPivot hp q))
      rw [coordinateWeight_firstPivot]
      simpa only [zero_add] using
        (isWeightedHomogeneous_C (coordinateWeight p) (normalizer (R := R) (Sum.inl q))).mul
          (equation_homogeneous p (2*k+1) q.val.1 q.val.2)
  | inr q =>
      change (C (normalizer (Sum.inr q)) * equation p (2*k) q.val.1 q.val.2).IsWeightedHomogeneous
        (coordinateWeight p) (coordinateWeight p (secondPivot hp q))
      rw [coordinateWeight_secondPivot]
      simpa only [zero_add] using
        (isWeightedHomogeneous_C (coordinateWeight p) (normalizer (R := R) (Sum.inr q))).mul
          (equation_homogeneous p (2*k) q.val.1 q.val.2)

theorem lowPair_rows_ne (q : LowPair p) : q.val.1 ≠ q.val.2 := by
  intro h
  have hl := q.property.1
  rw [h] at hl
  exact lt_irrefl _ hl

/-- The selected coefficient is literally one after normalization. -/
theorem normalizedEquation_pivot_coeff (hp : IndependentPivots p)
    (q : LowPair p ⊕ LowPair p) :
    (normalizedEquation (R := R) q).coeff (Finsupp.single (pivotEmbedding hp q) 1) = 1 := by
  rw [normalizedEquation, coeff_C_mul]
  cases q with
  | inl q =>
      change normalizer (R := R) (Sum.inl q) *
        (equation p (2*k+1) q.val.1 q.val.2).coeff
          (Finsupp.single (firstPivot hp q) 1) = 1
      rw [equation_coeff_single]
      change normalizer (R := R) (Sum.inl q) *
        ((if q.val.1 = q.val.1 then
          formMatrix (2*k+1) (firstPivot hp q).val.2 (p q.val.2) else 0) +
          if q.val.1 = q.val.2 then
            formMatrix (2*k+1) (p q.val.1) (firstPivot hp q).val.2 else 0) = 1
      rw [ite_eq_left rfl, ite_eq_right (lowPair_rows_ne q), add_zero, firstPivot_coefficient]
      simp only [normalizer, Sum.elim_inl]
      split <;> simp
  | inr q =>
      change normalizer (R := R) (Sum.inr q) *
        (equation p (2*k) q.val.1 q.val.2).coeff
          (Finsupp.single (secondPivot hp q) 1) = 1
      rw [equation_coeff_single]
      change normalizer (R := R) (Sum.inr q) *
        ((if q.val.2 = q.val.1 then
          formMatrix (2*k) (secondPivot hp q).val.2 (p q.val.2) else 0) +
          if q.val.2 = q.val.2 then
            formMatrix (2*k) (p q.val.1) (secondPivot hp q).val.2 else 0) = 1
      rw [ite_eq_left rfl, ite_eq_right (Ne.symm (lowPair_rows_ne q)), zero_add,
        secondPivot_coefficient]
      simp only [normalizer, Sum.elim_inr]
      simp

theorem first_linear_lower (hp : IndependentPivots p) (q : LowPair p)
    (v : Coordinate p) (hne : v ≠ firstPivot hp q)
    (hv : (equation (R := R) p (2*k+1) q.val.1 q.val.2).coeff
      (Finsupp.single v 1) ≠ 0) :
    eliminationRank hp v < eliminationRank hp (firstPivot hp q) := by
  rcases equation_linear_support p (2*k+1) q.val.1 q.val.2 v hv with h | h
  · exfalso
    apply hne
    apply Subtype.ext
    apply Prod.ext h.1
    apply Fin.ext
    rw [firstPivot_column_val]
    omega
  · exact first_partner_lower hp q v h.1 h.2

theorem second_linear_lower (hp : IndependentPivots p) (q : LowPair p)
    (v : Coordinate p) (hne : v ≠ secondPivot hp q)
    (hv : (equation (R := R) p (2*k) q.val.1 q.val.2).coeff
      (Finsupp.single v 1) ≠ 0) :
    eliminationRank hp v < eliminationRank hp (secondPivot hp q) := by
  rcases equation_linear_support p (2*k) q.val.1 q.val.2 v hv with h | h
  · exact second_partner_lower hp q v h.1 h.2
  · exfalso
    apply hne
    apply Subtype.ext
    apply Prod.ext h.1
    apply Fin.ext
    rw [secondPivot_column_val]
    omega

theorem normalizedEquation_linear_lower (hp : IndependentPivots p)
    (q : LowPair p ⊕ LowPair p) (v : Coordinate p) (hne : v ≠ pivotEmbedding hp q)
    (hv : (normalizedEquation (R := R) q).coeff (Finsupp.single v 1) ≠ 0) :
    eliminationRank hp v < eliminationRank hp (pivotEmbedding hp q) := by
  have he : (lowEquation (R := R) q).coeff (Finsupp.single v 1) ≠ 0 := by
    intro hz
    apply hv
    simp only [normalizedEquation, coeff_C_mul, hz, mul_zero]
  cases q with
  | inl q => exact first_linear_lower hp q v hne he
  | inr q => exact second_linear_lower hp q v hne he

/-- Every variable in the normalized remainder has strictly lower rank. -/
theorem normalizedEquation_remainder_lower (hp : IndependentPivots p)
    (q : LowPair p ⊕ LowPair p) (v : Coordinate p)
    (hv : v ∈ (normalizedEquation (R := R) q - X (pivotEmbedding hp q)).vars) :
    eliminationRank hp v < eliminationRank hp (pivotEmbedding hp q) := by
  classical
  have hh := (normalizedEquation_homogeneous (R := R) hp q).sub
    (isWeightedHomogeneous_X R (coordinateWeight p) (pivotEmbedding hp q))
  rcases vars_lt_weight_or_linear (coordinateWeight p) (coordinateWeight_pos p)
      (normalizedEquation q - X (pivotEmbedding hp q)) _ hh v hv with h | h
  · exact eliminationRank_lt_of_weight_lt hp v (pivotEmbedding hp q) h
  · by_cases he : v = pivotEmbedding hp q
    · subst v
      simp only [coeff_sub, normalizedEquation_pivot_coeff, coeff_single_X,
        and_self, ite_true, sub_self, ne_eq, not_true_eq_false] at h
    · apply normalizedEquation_linear_lower (R := R) hp q v he
      simpa only [coeff_sub, coeff_single_X, true_and, ite_eq_right (Ne.symm he),
        sub_zero] using h

/-- Extend the normalized remainders by zero on free coordinates. -/
def coordinateRemainder (hp : IndependentPivots p) :
    Coordinate p → MvPolynomial (Coordinate p) R :=
  Function.extend (pivotEmbedding hp)
    (fun q => normalizedEquation q - X (pivotEmbedding hp q)) (fun _ => 0)

@[simp] theorem coordinateRemainder_pivot (hp : IndependentPivots p)
    (q : LowPair p ⊕ LowPair p) :
    coordinateRemainder (R := R) hp (pivotEmbedding hp q) =
      normalizedEquation q - X (pivotEmbedding hp q) :=
  (pivotEmbedding hp).injective.extend_apply _ _ q

theorem coordinateRemainder_lower (hp : IndependentPivots p) :
    ∀ i j, j ∈ (coordinateRemainder (R := R) hp i).vars →
      eliminationRank hp j < eliminationRank hp i := by
  intro i j hj
  by_cases hi : i ∈ Set.range (pivotEmbedding hp)
  · obtain ⟨q, rfl⟩ := hi
    rw [coordinateRemainder_pivot] at hj
    exact normalizedEquation_remainder_lower hp q j hj
  · have hz : coordinateRemainder (R := R) hp i = 0 :=
      Function.extend_apply' _ _ _ hi
    simp [hz] at hj

theorem lowIdeal_eq_normalized_span :
    lowIdeal (R := R) (p := p) = Ideal.span (Set.range (normalizedEquation (R := R) (p := p))) := by
  apply le_antisymm
  · apply Ideal.span_le.mpr
    rintro _ ⟨q, rfl⟩
    have he : lowEquation (R := R) q = C (normalizer q) * normalizedEquation q := by
      rw [normalizedEquation, ← mul_assoc, ← map_mul, normalizer_square, map_one, one_mul]
    rw [he]
    exact Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨q, rfl⟩)
  · apply Ideal.span_le.mpr
    rintro _ ⟨q, rfl⟩
    exact Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨q, rfl⟩)

theorem normalized_span_eq_triangular_span (hp : IndependentPivots p) :
    Ideal.span (Set.range (normalizedEquation (R := R) (p := p))) =
      Ideal.span ((fun i => X i + coordinateRemainder (R := R) hp i) ''
        Set.range (pivotEmbedding hp)) := by
  congr 1
  ext f
  constructor
  · rintro ⟨q, rfl⟩
    refine ⟨pivotEmbedding hp q, ⟨q, rfl⟩, ?_⟩
    dsimp only
    rw [coordinateRemainder_pivot]
    ring
  · rintro ⟨i, ⟨q, rfl⟩, rfl⟩
    refine ⟨q, ?_⟩
    dsimp only
    rw [coordinateRemainder_pivot]
    ring

/-- The literal attracting-chart coordinate ring is a polynomial algebra
on its free entries. All original equations occur in the source ideal. -/
def attractingCoordinateRingEquiv (hp : IndependentPivots p) :
    (MvPolynomial (Coordinate p) R ⧸ isotropyIdeal p (2*k+1) (2*k)) ≃ₐ[R]
      MvPolynomial {i : Coordinate p // i ∉ Set.range (pivotEmbedding hp)} R :=
  (Ideal.quotientEquivAlgOfEq R ((isotropyIdeal_eq_lowIdeal hp).trans
    (lowIdeal_eq_normalized_span.trans (normalized_span_eq_triangular_span hp)))).trans
      (PaperVerification.TriangularPolynomialCoordinates.triangularQuotientEquiv
        (eliminationRank hp) (coordinateRemainder hp) (coordinateRemainder_lower hp)
        (Set.range (pivotEmbedding hp)))

end PaperVerification.IsotropicAttractingCoordinates
end
end
end ComponentSource_7

run_cmd Lean.logInfo "COMPONENT_SOURCE_END: PaperVerification.IsotropicAttractingElimination"

section ComponentSource_8
/- Original module: PaperVerification.IsotropicAttractingChartRings -/


/-!
# Attracting cells inside the original Plücker affine charts

The original chart polynomial ring retains every nonpivot matrix entry.
Setting the entries to the left of their row pivots to zero gives exactly
the row-echelon coordinates used by the explicit elimination theorem.
This restriction carries the original increasing-pair isotropy ideal to
the full skew-matrix ideal, and its kernel is the coordinate ideal of
those vanishing entries.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

namespace PaperVerification.IsotropicAttractingCharts

open MvPolynomial
open PaperVerification.AlternatingForms
open PaperVerification.IsotropicAttractingCoordinates
open PaperVerification.TriangularPolynomialCoordinates
open scoped BigOperators

variable {K : Type*} [Field K] {s n t : ℕ}

abbrev indexEmbedding (p : PluckerIndex s n) : Fin s ↪ Fin n :=
  ⟨p.val, p.property.injective⟩

@[simp] theorem indexEmbedding_apply (p : PluckerIndex s n) (i : Fin s) :
    indexEmbedding p i = p.val i := rfl

/-- These are precisely the nonpivot entries weakly left of the row
pivot; equality cannot occur because the column is a nonpivot. -/
def negativeCoordinates (p : PluckerIndex s n) : Set (PluckerChartVariable p) :=
  {v | ¬ (p.val v.1).val < v.2.val.val}

def positiveCoordinateEquiv (p : PluckerIndex s n) :
    {v : PluckerChartVariable p // v ∉ negativeCoordinates p} ≃ Coordinate (indexEmbedding p) where
  toFun v := ⟨(v.val.1, v.val.2.val), by
    simpa only [negativeCoordinates, Set.mem_ofPred_eq, not_not, indexEmbedding_apply]
      using v.property,
    v.val.2.property⟩
  invFun v := ⟨(v.val.1, ⟨v.val.2, v.property.2⟩), by
    simpa only [negativeCoordinates, Set.mem_ofPred_eq, not_not, indexEmbedding_apply]
      using v.property.1⟩
  left_inv v := by apply Subtype.ext; rfl
  right_inv v := by apply Subtype.ext; rfl

/-- The actual polynomial restriction to row-echelon matrices. -/
def fullChartRestriction (p : PluckerIndex s n) :
    MvPolynomial (PluckerChartVariable p) K →ₐ[K]
      MvPolynomial (Coordinate (indexEmbedding p)) K :=
  (renameEquiv K (positiveCoordinateEquiv p)).toAlgHom.comp
    (eraseCoordinates (negativeCoordinates p))

theorem fullChartRestriction_X (p : PluckerIndex s n) (v : PluckerChartVariable p) :
    fullChartRestriction (K := K) p (X v) =
      if h : (p.val v.1).val < v.2.val.val then
        X (⟨(v.1,v.2.val),h,v.2.property⟩ : Coordinate (indexEmbedding p)) else 0 := by
  classical
  change (renameEquiv K (positiveCoordinateEquiv p))
    (eraseCoordinates (negativeCoordinates p) (X v)) = _
  by_cases h : (p.val v.1).val < v.2.val.val
  · have hv : v ∉ negativeCoordinates p := not_not.mpr h
    rw [eraseCoordinates, MvPolynomial.aeval_X, dite_eq_left hv,
      dite_eq_left h, renameEquiv_apply, MvPolynomial.rename_X]
    rfl
  · have hv : ¬ v ∉ negativeCoordinates p := fun hv => h (not_not.mp hv)
    rw [eraseCoordinates, MvPolynomial.aeval_X, dite_eq_right hv,
      map_zero, dite_eq_right h]

theorem fullChartRestriction_surjective (p : PluckerIndex s n) :
    Function.Surjective (fullChartRestriction (K := K) p) :=
  (renameEquiv K (positiveCoordinateEquiv p)).surjective.comp
    (eraseCoordinates_surjective (negativeCoordinates p))

theorem fullChartRestriction_kernel (p : PluckerIndex s n) :
    RingHom.ker (fullChartRestriction (K := K) p).toRingHom =
      Ideal.span (X '' negativeCoordinates p) := by
  change RingHom.ker ((renameEquiv K (positiveCoordinateEquiv p)).toRingHom.comp
    (eraseCoordinates (R := K) (negativeCoordinates p)).toRingHom) = _
  rw [RingHom.ker_comp_of_injective _
    (f := (renameEquiv K (positiveCoordinateEquiv p)).toRingHom)
    (renameEquiv K (positiveCoordinateEquiv p)).injective]
  exact ker_eraseCoordinates (negativeCoordinates p)

/-- The restricted original normalized matrix is the literal echelon
matrix, entry by entry. -/
theorem fullChartRestriction_matrix (p : PluckerIndex s n) (i : Fin s) (j : Fin n) :
    fullChartRestriction (K := K) p (pluckerChartMatrix p i j) =
      row (indexEmbedding p) i j := by
  classical
  by_cases hij : j = p.val i
  · simp [pluckerChartMatrix, row, hij]
  · by_cases hj : j ∈ Set.range p.val
    · simp only [pluckerChartMatrix, Matrix.of_apply, ite_eq_right hij, dite_eq_left hj, map_zero]
      simp [row, indexEmbedding, hij, hj]
    · rw [pluckerChartMatrix_nonpivot p i ⟨j,hj⟩, fullChartRestriction_X]
      simp only [row, indexEmbedding, Function.Embedding.coeFn_mk, ite_eq_right hij]
      by_cases hlt : (p.val i).val < j.val
      · simp [hlt, hj]
      · simp [hlt]

/-- Coefficients of the same skew matrix in the original convention. -/
def canonicalCoefficient (c : ℕ) : StrictPairs n → K :=
  fun q => formMatrix c q.val.1 q.val.2

theorem fullChartRestriction_pairing (p : PluckerIndex (t+2) n)
    (c : ℕ) (i j : Fin (t+2)) :
    fullChartRestriction (K := K) p
      (alternatingRowPair (canonicalCoefficient (K := K) c) (pluckerChartMatrix p) i j) =
      equation (indexEmbedding p) c i j := by
  simp only [alternatingRowPair, map_sum, map_smul, map_sub, map_mul,
    fullChartRestriction_matrix]
  rw [equation_eq_increasing_pair_sum]
  apply Finset.sum_congr rfl
  intro q _
  rw [Algebra.smul_def]
  rfl

def canonicalForms (c₁ c₂ : ℕ) : Fin 2 → StrictPairs n → K :=
  fun l => canonicalCoefficient (if l = 0 then c₁ else c₂)

/-- The image is the full original isotropy ideal in the smaller cell
ring. No radical or reduction is taken. -/
theorem fullChartRestriction_isotropyIdeal (p : PluckerIndex (t+2) n) (c₁ c₂ : ℕ) :
    (isotropicChartIdeal p (canonicalForms (K := K) c₁ c₂)).map
        (fullChartRestriction p).toRingHom =
      isotropyIdeal (indexEmbedding p) c₁ c₂ := by
  apply le_antisymm
  · rw [Ideal.map_le_iff_le_comap]
    apply Ideal.span_le.mpr
    rintro _ ⟨⟨l,q⟩,rfl⟩
    change fullChartRestriction p
      (alternatingRowPair (canonicalForms c₁ c₂ l) (pluckerChartMatrix p) q.val.1 q.val.2)
        ∈ isotropyIdeal (indexEmbedding p) c₁ c₂
    unfold canonicalForms
    rw [fullChartRestriction_pairing]
    apply Ideal.subset_span
    by_cases hl : l = 0
    · exact ⟨(true,q.val.1,q.val.2), by simp [hl]⟩
    · exact ⟨(false,q.val.1,q.val.2), by simp [hl]⟩
  · apply Ideal.span_le.mpr
    rintro _ ⟨⟨b,i,j⟩,rfl⟩
    let l : Fin 2 := if b then 0 else 1
    have hl : (if l = 0 then c₁ else c₂) = (if b then c₁ else c₂) := by
      cases b <;> simp [l]
    have hmem := Ideal.mem_map_of_mem (fullChartRestriction (K := K) p).toRingHom
      (alternatingRowPair_mem_chartIdeal p (canonicalForms c₁ c₂) l i j)
    change fullChartRestriction p
      (alternatingRowPair (canonicalForms c₁ c₂ l) (pluckerChartMatrix p) i j) ∈ _ at hmem
    change equation (R := K) (indexEmbedding p) (if b then c₁ else c₂) i j ∈
      (isotropicChartIdeal p (canonicalForms c₁ c₂)).map
        (fullChartRestriction (K := K) p).toRingHom
    rw [canonicalForms, fullChartRestriction_pairing, hl] at hmem
    exact hmem

/-- Literal closed-cell ideal in the original full Plücker chart. -/
def fullCellIdeal (p : PluckerIndex (t+2) n) (c₁ c₂ : ℕ) :
    Ideal (MvPolynomial (PluckerChartVariable p) K) :=
  isotropicChartIdeal p (canonicalForms c₁ c₂) ⊔ Ideal.span (X '' negativeCoordinates p)

def fullChartToCell (p : PluckerIndex (t+2) n) (c₁ c₂ : ℕ) :
    MvPolynomial (PluckerChartVariable p) K →ₐ[K]
      (MvPolynomial (Coordinate (indexEmbedding p)) K ⧸
        isotropyIdeal (indexEmbedding p) c₁ c₂) :=
  (Ideal.Quotient.mkₐ K (isotropyIdeal (indexEmbedding p) c₁ c₂)).comp (fullChartRestriction p)

theorem fullChartToCell_surjective (p : PluckerIndex (t+2) n) (c₁ c₂ : ℕ) :
    Function.Surjective (fullChartToCell (K := K) p c₁ c₂) :=
  Ideal.Quotient.mk_surjective.comp (fullChartRestriction_surjective p)

theorem fullChartToCell_kernel (p : PluckerIndex (t+2) n) (c₁ c₂ : ℕ) :
    RingHom.ker (fullChartToCell (K := K) p c₁ c₂).toRingHom = fullCellIdeal p c₁ c₂ := by
  change RingHom.ker ((Ideal.Quotient.mk (isotropyIdeal (indexEmbedding p) c₁ c₂)).comp
    (fullChartRestriction (K := K) p).toRingHom) = _
  rw [← RingHom.comap_ker, Ideal.mk_ker, ← fullChartRestriction_isotropyIdeal,
    Ideal.comap_map_of_surjective' (fullChartRestriction (K := K) p).toRingHom
      (fullChartRestriction_surjective p),
    fullChartRestriction_kernel]
  rfl

/-- The original chart with precisely its left entries set to zero has
the same complete coordinate ring as the explicitly eliminated cell. -/
def fullCellCoordinateRingEquiv (p : PluckerIndex (t+2) n) (c₁ c₂ : ℕ) :
    (MvPolynomial (PluckerChartVariable p) K ⧸ fullCellIdeal p c₁ c₂) ≃ₐ[K]
      (MvPolynomial (Coordinate (indexEmbedding p)) K ⧸
        isotropyIdeal (indexEmbedding p) c₁ c₂) :=
  (Ideal.quotientEquivAlgOfEq K (fullChartToCell_kernel p c₁ c₂).symm).trans
    (Ideal.quotientKerAlgEquivOfSurjective (fullChartToCell_surjective p c₁ c₂))

/-- Every permitted original affine cell is an actual affine space. -/
def originalCellPolynomialEquiv {k : ℕ} (p : PluckerIndex (t+2) (2*k+1))
    (hp : IndependentPivots (indexEmbedding p)) :
    (MvPolynomial (PluckerChartVariable p) K ⧸ fullCellIdeal p (2*k+1) (2*k)) ≃ₐ[K]
      MvPolynomial {i : Coordinate (indexEmbedding p) //
        i ∉ Set.range (pivotEmbedding hp)} K :=
  (fullCellCoordinateRingEquiv p (2*k+1) (2*k)).trans (attractingCoordinateRingEquiv hp)

end PaperVerification.IsotropicAttractingCharts
end
end
end ComponentSource_8

run_cmd Lean.logInfo "COMPONENT_SOURCE_END: PaperVerification.IsotropicAttractingChartRings"

section ComponentSource_9
/- Original module: PaperVerification.IsotropicAttractingMinorFiltration -/


/-!
# The original homogeneous coordinates cut out the attracting cells

Order the Plücker coordinates by the sum of their column indices.  On the
chart with pivot `p`, vanishing of every smaller-weight minor is exactly
the row-echelon condition.  Every different minor of equal weight also
vanishes there.  Thus the explicit affine cells are the strata of the
actual homogeneous-coordinate filtration on the original projective
scheme, rather than merely an abstract disjoint family of affine schemes.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

namespace PaperVerification.IsotropicAttractingCharts

open MvPolynomial
open PaperVerification.AlternatingForms
open PaperVerification.IsotropicAttractingCoordinates
open scoped BigOperators

variable {K : Type*} [Field K] {s n : ℕ}

/-- The character of the original Plücker coordinate for the chain torus. -/
def pluckerWeight (p : PluckerIndex s n) : ℕ := ∑ i, (p.val i).val

theorem pluckerWeight_lt_of_le_ne (p I : PluckerIndex s n)
    (hle : ∀ i, p.val i ≤ I.val i) (hne : p ≠ I) : pluckerWeight p < pluckerWeight I := by
  have hstrict : ∃ i, (p.val i).val < (I.val i).val := by
    by_contra h
    push Not at h
    apply hne
    apply Subtype.ext
    funext i
    exact Fin.ext (Nat.le_antisymm (hle i) (h i))
  obtain ⟨i, hi⟩ := hstrict
  exact Finset.sum_lt_sum (fun j _ => hle j) ⟨i, Finset.mem_univ _, hi⟩

/-- An echelon matrix has no nonpivot minor of weight at most that of
its pivot.  The argument uses the genuine determinant expansion. -/
theorem echelon_minor_eq_zero (p I : PluckerIndex s n)
    (hw : pluckerWeight I ≤ pluckerWeight p) (hne : p ≠ I) :
    Matrix.det (Matrix.of (fun i j : Fin s =>
      row (R := K) (indexEmbedding p) i (I.val j))) = 0 := by
  classical
  rw [Matrix.det_apply]
  apply Finset.sum_eq_zero
  intro σ _
  have hmiss : ∃ i, ¬ p.val (σ i) ≤ I.val i := by
    by_contra h
    have hall : ∀ i, p.val (σ i) ≤ I.val i := by
      intro i
      exact not_not.mp (not_exists.mp h i)
    have hdiag := monotone_matching_lower p.val I.val p.property.monotone I.property.monotone σ hall
    exact (not_lt_of_ge hw) (pluckerWeight_lt_of_le_ne p I hdiag hne)
  obtain ⟨i, hi⟩ := hmiss
  have hz : (∏ j, row (R := K) (indexEmbedding p) (σ j) (I.val j)) = 0 := by
    apply Finset.prod_eq_zero (Finset.mem_univ i)
    exact row_eq_zero_of_lt (indexEmbedding p) (σ i) (I.val i) (lt_of_not_ge hi)
  simp only [Matrix.of_apply, hz, smul_zero]

theorem fullChartRestriction_minor (p I : PluckerIndex s n) :
    fullChartRestriction (K := K) p
      (matrixMinorEvaluation (K := K) (pluckerChartMatrix (K := K) p) (X I)) =
      Matrix.det (Matrix.of (fun i j : Fin s => row (R := K) (indexEmbedding p) i (I.val j))) := by
  rw [matrixMinorEvaluation, aeval_X, AlgHom.map_det]
  congr 1
  apply Matrix.ext
  intro i j
  exact fullChartRestriction_matrix (K := K) p i (I.val j)

def earlyMinorIdeal (p : PluckerIndex s n) : Ideal (MvPolynomial (PluckerChartVariable p) K) :=
  Ideal.span {f : MvPolynomial (PluckerChartVariable p) K |
    ∃ I : PluckerIndex s n, pluckerWeight I < pluckerWeight p ∧
    f = matrixMinorEvaluation (K := K) (pluckerChartMatrix p) (X I)}

theorem earlyMinorIdeal_le_kernel (p : PluckerIndex s n) :
    earlyMinorIdeal (K := K) p ≤ RingHom.ker (fullChartRestriction p).toRingHom := by
  apply Ideal.span_le.mpr
  rintro f ⟨I, hw, rfl⟩
  change fullChartRestriction p (matrixMinorEvaluation (pluckerChartMatrix p) (X I)) = 0
  rw [fullChartRestriction_minor]
  exact echelon_minor_eq_zero p I (Nat.le_of_lt hw) (fun he => by simpa [he] using hw)

theorem update_columns_injective (p : PluckerIndex s n) (i : Fin s) (j : Fin n)
    (hj : j ∉ Set.range p.val) : Function.Injective (Function.update p.val i j) := by
  intro a b hab
  by_cases ha : a = i
  · subst a
    by_cases hb : b = i
    · exact hb.symm
    · simp only [Function.update_self, Function.update_of_ne hb] at hab
      exact False.elim (hj ⟨b, hab.symm⟩)
  · by_cases hb : b = i
    · subst b
      simp only [Function.update_self, Function.update_of_ne ha] at hab
      exact False.elim (hj ⟨a, hab⟩)
    · simp only [Function.update_of_ne ha, Function.update_of_ne hb] at hab
      exact p.property.injective hab

theorem sortedPluckerWeight (I : Fin s → Fin n) (hI : Function.Injective I) :
    pluckerWeight (sortedPluckerIndex I hI) = ∑ i, (I i).val :=
  Equiv.sum_comp (Tuple.sort I) (fun i => (I i).val)

/-- A left-of-pivot entry is represented by a strictly earlier genuine
Plücker coordinate, after sorting its replacement column. -/
theorem replacement_weight_lt (p : PluckerIndex s n) (i : Fin s) (j : Fin n)
    (hj : j ∉ Set.range p.val) (hlt : j < p.val i) :
    pluckerWeight (sortedPluckerIndex (Function.update p.val i j)
      (update_columns_injective p i j hj)) < pluckerWeight p := by
  classical
  rw [sortedPluckerWeight]
  apply Finset.sum_lt_sum
  · intro a _
    by_cases ha : a = i
    · subst a
      simpa only [Function.update_self] using Nat.le_of_lt hlt
    · simp [Function.update_of_ne ha]
  · refine ⟨i, Finset.mem_univ _, ?_⟩
    simp only [Function.update_self]
    exact show j.val < (p.val i).val from hlt

theorem cramerCoordinate_mem_early (p : PluckerIndex s n) (i : Fin s) (j : Fin n)
    (hj : j ∉ Set.range p.val) (hlt : j < p.val i) :
    matrixMinorEvaluation (K := K) (pluckerChartMatrix p) (cramerPluckerCoordinate p i j)
      ∈ earlyMinorIdeal (K := K) p := by
  classical
  let hi := update_columns_injective p i j hj
  rw [cramerPluckerCoordinate, orderedPluckerCoordinate, dite_eq_left hi, map_smul,
    Algebra.smul_def]
  apply Ideal.mul_mem_left
  exact Ideal.subset_span ⟨sortedPluckerIndex (Function.update p.val i j) hi,
    replacement_weight_lt p i j hj hlt, rfl⟩

/-- The global homogeneous vanishing conditions induce exactly the
original coordinate ideal of the cell in the pivot affine chart. -/
theorem earlyMinorIdeal_eq_negativeCoordinates (p : PluckerIndex s n) :
    earlyMinorIdeal (K := K) p = Ideal.span (X '' negativeCoordinates p) := by
  apply le_antisymm
  · rw [← fullChartRestriction_kernel]
    exact earlyMinorIdeal_le_kernel p
  · apply Ideal.span_le.mpr
    rintro _ ⟨v, hv, rfl⟩
    have hne : v.2.val ≠ p.val v.1 := fun h => v.2.property ⟨v.1, h.symm⟩
    have hlt : v.2.val < p.val v.1 := by
      have hnot : ¬ (p.val v.1).val < v.2.val.val := hv
      exact lt_of_le_of_ne (Nat.le_of_not_gt hnot) hne
    have hm := cramerCoordinate_mem_early (K := K) p v.1 v.2.val v.2.property hlt
    rw [matrixMinorEvaluation_cramer, pluckerChartMatrix_pivot, Matrix.cramer_one] at hm
    change pluckerChartMatrix (K := K) p v.1 v.2.val ∈ earlyMinorIdeal p at hm
    rw [pluckerChartMatrix_nonpivot] at hm
    exact hm

/-- Equal-weight coordinates other than the pivot vanish on the same
scheme-theoretic cell; this ensures the frontier has strictly larger
Plücker weight and permits any tie-breaking order in the filtration. -/
theorem nonpivot_low_minor_mem_early (p I : PluckerIndex s n)
    (hw : pluckerWeight I ≤ pluckerWeight p) (hne : p ≠ I) :
    matrixMinorEvaluation (K := K) (pluckerChartMatrix p) (X I) ∈ earlyMinorIdeal (K := K) p := by
  rw [earlyMinorIdeal_eq_negativeCoordinates, ← fullChartRestriction_kernel]
  change fullChartRestriction p (matrixMinorEvaluation (pluckerChartMatrix p) (X I)) = 0
  rw [fullChartRestriction_minor]
  exact echelon_minor_eq_zero p I hw hne

end PaperVerification.IsotropicAttractingCharts
end
end
end ComponentSource_9

run_cmd Lean.logInfo "COMPONENT_SOURCE_END: PaperVerification.IsotropicAttractingMinorFiltration"

section ComponentSource_10
/- Original module: PaperVerification.IsotropicAttractingNormalizedFiltration -/


/-!
# The actual normalized rings of the homogeneous filtration

Adding earlier Plücker coordinates to the original homogeneous isotropy
ideal, then taking the genuine pivot affine chart, gives exactly the
closed row-echelon cell already eliminated.  The comparison is an
isomorphism of the full coordinate rings, before taking radicals.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

namespace PaperVerification.IsotropicAttractingCharts

open MvPolynomial
open PaperVerification.AlternatingForms
open PaperVerification.IsotropicAttractingCoordinates

attribute [local instance] MvPolynomial.gradedAlgebra

variable {K : Type*} [Field K] {s n t : ℕ}

/-- Any ordering refining Plücker weight has precisely these properties
for the set of indices strictly before a chosen pivot. -/
def EarlierSet (p : PluckerIndex s n) (E : Set (PluckerIndex s n)) : Prop :=
  (∀ I, pluckerWeight I < pluckerWeight p → I ∈ E) ∧
    ∀ I ∈ E, pluckerWeight I ≤ pluckerWeight p ∧ p ≠ I

/-- The original homogeneous coordinate ideal of the filtration stage. -/
def filtrationIdeal (E : Set (PluckerIndex (t+2) n)) (c₁ c₂ : ℕ) :
    Ideal (MvPolynomial (PluckerIndex (t+2) n) K) :=
  isotropicPluckerIdeal (canonicalForms c₁ c₂) ⊔ Ideal.span (X '' E)

theorem filtrationIdeal_isHomogeneous (E : Set (PluckerIndex (t+2) n)) (c₁ c₂ : ℕ) :
    (filtrationIdeal (K := K) E c₁ c₂).IsHomogeneous
      (homogeneousSubmodule (PluckerIndex (t+2) n) K) := by
  apply (isotropicPluckerIdeal_isHomogeneous (canonicalForms c₁ c₂)).sup
  apply Ideal.homogeneous_span
  rintro _ ⟨I, hI, rfl⟩
  exact ⟨1, isHomogeneous_X K I⟩

theorem filtrationIdeal_mono {E F : Set (PluckerIndex (t+2) n)}
    (hEF : E ⊆ F) (c₁ c₂ : ℕ) :
    filtrationIdeal (K := K) E c₁ c₂ ≤ filtrationIdeal F c₁ c₂ :=
  sup_le_sup_left (Ideal.span_mono (Set.image_mono hEF)) _

/-- Exactly the earlier homogeneous coordinates become the entry ideal
of the row-echelon chart. Equal weights cause no extra equations. -/
theorem earlierVariables_map (p : PluckerIndex s n) (E : Set (PluckerIndex s n))
    (hE : EarlierSet p E) :
    (Ideal.span (X '' E : Set (MvPolynomial (PluckerIndex s n) K))).map
      (matrixMinorEvaluation (K := K) (pluckerChartMatrix (K := K) p)).toRingHom =
        earlyMinorIdeal (K := K) p := by
  apply le_antisymm
  · rw [Ideal.map_le_iff_le_comap]
    apply Ideal.span_le.mpr
    rintro _ ⟨I, hI, rfl⟩
    exact nonpivot_low_minor_mem_early p I (hE.2 I hI).1 (hE.2 I hI).2
  · apply Ideal.span_le.mpr
    rintro _ ⟨I, hI, rfl⟩
    exact Ideal.mem_map_of_mem _ (Ideal.subset_span ⟨I, hE.1 I hI, rfl⟩)

variable [CharZero K]

/-- The full homogeneous filtration ideal maps to the literal full cell
ideal in the original matrix chart. -/
theorem filtrationIdeal_map_chart (p : PluckerIndex (t+2) n)
    (E : Set (PluckerIndex (t+2) n)) (hE : EarlierSet p E) (c₁ c₂ : ℕ) :
    (filtrationIdeal (K := K) E c₁ c₂).map
      (matrixMinorEvaluation (K := K) (pluckerChartMatrix (K := K) p)).toRingHom =
        fullCellIdeal (K := K) p c₁ c₂ := by
  rw [filtrationIdeal, Ideal.map_sup, isotropicPluckerIdeal_map_chart_eq,
    earlierVariables_map p E hE, earlyMinorIdeal_eq_negativeCoordinates]
  rfl

/-- Evaluate every original homogeneous Plücker coordinate on the
universal row-echelon cell, preserving every original isotropy equation. -/
def normalizedCellEvaluation (p : PluckerIndex (t+2) n) (c₁ c₂ : ℕ) :
    MvPolynomial (PluckerIndex (t+2) n) K →ₐ[K]
      (MvPolynomial (Coordinate (indexEmbedding p)) K ⧸
        isotropyIdeal (indexEmbedding p) c₁ c₂) :=
  (fullChartToCell p c₁ c₂).comp (matrixMinorEvaluation (pluckerChartMatrix p))

theorem normalizedCellEvaluation_surjective (p : PluckerIndex (t+2) n) (c₁ c₂ : ℕ) :
    Function.Surjective (normalizedCellEvaluation (K := K) p c₁ c₂) :=
  (fullChartToCell_surjective p c₁ c₂).comp (matrixMinorEvaluation_chart_surjective p)

/-- Exact kernel of the normalized coordinate evaluation. The only
additional relation is the genuine pivot normalization `X p = 1`. -/
theorem normalizedCellEvaluation_kernel (p : PluckerIndex (t+2) n)
    (E : Set (PluckerIndex (t+2) n)) (hE : EarlierSet p E) (c₁ c₂ : ℕ) :
    RingHom.ker (normalizedCellEvaluation (K := K) p c₁ c₂).toRingHom =
      filtrationIdeal E c₁ c₂ ⊔ Ideal.span {X p - 1} := by
  change RingHom.ker ((fullChartToCell (K := K) p c₁ c₂).toRingHom.comp
    (matrixMinorEvaluation (pluckerChartMatrix p)).toRingHom) = _
  rw [← RingHom.comap_ker, fullChartToCell_kernel,
    ← filtrationIdeal_map_chart p E hE c₁ c₂,
    Ideal.comap_map_of_surjective'
      (matrixMinorEvaluation (K := K) (pluckerChartMatrix p)).toRingHom
      (matrixMinorEvaluation_chart_surjective p),
    matrixMinorEvaluation_chart_kernel, pluckerBigCellIdeal]
  have hle : matrixPluckerIdeal (K := K) (s := t+2) (n := n) ≤
      filtrationIdeal E c₁ c₂ := le_trans le_sup_left le_sup_left
  rw [← sup_assoc, sup_eq_left.mpr hle]

/-- The actual normalized quotient defining the filtration stratum is
isomorphic to the original common-isotropic echelon coordinate ring. -/
def normalizedFiltrationCellEquiv (p : PluckerIndex (t+2) n)
    (E : Set (PluckerIndex (t+2) n)) (hE : EarlierSet p E) (c₁ c₂ : ℕ) :
    (MvPolynomial (PluckerIndex (t+2) n) K ⧸
      (filtrationIdeal E c₁ c₂ ⊔ Ideal.span {X p - 1})) ≃ₐ[K]
      (MvPolynomial (Coordinate (indexEmbedding p)) K ⧸
        isotropyIdeal (indexEmbedding p) c₁ c₂) :=
  (Ideal.quotientEquivAlgOfEq K
    (normalizedCellEvaluation_kernel p E hE c₁ c₂).symm).trans
      (Ideal.quotientKerAlgEquivOfSurjective (normalizedCellEvaluation_surjective p c₁ c₂))

/-- The whole scheme-theoretic pivot stratum of the original homogeneous
filtration is a polynomial algebra for every independent pivot. -/
def normalizedFiltrationPolynomialEquiv {k : ℕ} (p : PluckerIndex (t+2) (2*k+1))
    (E : Set (PluckerIndex (t+2) (2*k+1))) (hE : EarlierSet p E)
    (hp : IndependentPivots (indexEmbedding p)) :
    (MvPolynomial (PluckerIndex (t+2) (2*k+1)) K ⧸
      (filtrationIdeal E (2*k+1) (2*k) ⊔ Ideal.span {X p - 1})) ≃ₐ[K]
      MvPolynomial {i : Coordinate (indexEmbedding p) //
        i ∉ Set.range (pivotEmbedding hp)} K :=
  (normalizedFiltrationCellEquiv p E hE (2*k+1) (2*k)).trans
    (attractingCoordinateRingEquiv hp)

end PaperVerification.IsotropicAttractingCharts
end
end
end ComponentSource_10

run_cmd Lean.logInfo "COMPONENT_SOURCE_END: PaperVerification.IsotropicAttractingNormalizedFiltration"

section ComponentSource_11
/- Original module: PaperVerification.PluckerWeightOrder -/


/-!
# A finite order refining the genuine Plücker weights

This is only the combinatorial indexing of the closed filtration.  Every
Plücker coordinate occurs exactly once, and its predecessor set satisfies
the hypotheses already used to identify the actual affine stratum.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

namespace PaperVerification.IsotropicAttractingCharts

open PaperVerification.AlternatingForms

variable (s n : ℕ)

abbrev pivotCount := Fintype.card (PluckerIndex s n)

/-- Sort one enumeration by weight; no numerical tie-breaking assumption
is needed by the determinant proof. -/
def weightOrderedPivots : Fin (pivotCount s n) ≃ PluckerIndex s n :=
  (Tuple.sort (fun i : Fin (pivotCount s n) =>
    pluckerWeight ((Fintype.equivFin (PluckerIndex s n)).symm i))).trans
      (Fintype.equivFin (PluckerIndex s n)).symm

theorem weightOrderedPivots_monotone :
    Monotone (fun i => pluckerWeight (weightOrderedPivots s n i)) := by
  intro i j hij
  have h := (Tuple.monotone_sort (fun i : Fin (pivotCount s n) =>
    pluckerWeight ((Fintype.equivFin (PluckerIndex s n)).symm i))) hij
  exact h

/-- The literal original coordinates eliminated at the m-th stage. -/
def pivotPrefix (m : ℕ) : Set (PluckerIndex s n) :=
  {I | ((weightOrderedPivots s n).symm I).val < m}

@[simp] theorem pivotPrefix_zero : pivotPrefix s n 0 = ∅ := by
  ext I
  simp [pivotPrefix]

@[simp] theorem pivotPrefix_all : pivotPrefix s n (pivotCount s n) = Set.univ := by
  ext I
  simp only [pivotPrefix, Set.mem_ofPred_eq, Set.mem_univ, iff_true]
  exact ((weightOrderedPivots s n).symm I).isLt

theorem pivotPrefix_mono : Monotone (pivotPrefix s n) := by
  intro a b hab I hI
  exact lt_of_lt_of_le hI hab

theorem pivotPrefix_successor (i : Fin (pivotCount s n)) :
    pivotPrefix s n (i.val+1) = insert (weightOrderedPivots s n i)
      (pivotPrefix s n i.val) := by
  ext I
  change ((weightOrderedPivots s n).symm I).val < i.val+1 ↔
    I = weightOrderedPivots s n i ∨ ((weightOrderedPivots s n).symm I).val < i.val
  constructor
  · intro h
    by_cases he : ((weightOrderedPivots s n).symm I).val = i.val
    · left
      apply (weightOrderedPivots s n).symm.injective
      simpa only [Equiv.symm_apply_apply] using Fin.ext he
    · right
      omega
  · rintro (rfl | h)
    · simp
    · omega

/-- Exactly the weight-refinement properties needed by the genuine
normalized-filtration coordinate-ring theorem. -/
theorem pivotPrefix_earlier (i : Fin (pivotCount s n)) :
    EarlierSet (weightOrderedPivots s n i) (pivotPrefix s n i.val) := by
  constructor
  · intro I hI
    change ((weightOrderedPivots s n).symm I).val < i.val
    by_contra h
    have hi : i ≤ (weightOrderedPivots s n).symm I := Nat.le_of_not_gt h
    have hw := weightOrderedPivots_monotone s n hi
    change pluckerWeight (weightOrderedPivots s n i) ≤
      pluckerWeight (weightOrderedPivots s n ((weightOrderedPivots s n).symm I)) at hw
    rw [Equiv.apply_symm_apply] at hw
    exact (not_lt_of_ge hw) hI
  · intro I hI
    have hi : (weightOrderedPivots s n).symm I < i := hI
    constructor
    · have hw := weightOrderedPivots_monotone s n (le_of_lt hi)
      simpa only [Equiv.apply_symm_apply] using hw
    · intro he
      have hv := congrArg (weightOrderedPivots s n).symm he
      rw [Equiv.symm_apply_apply] at hv
      exact (ne_of_lt hi) hv.symm

end PaperVerification.IsotropicAttractingCharts
end
end
end ComponentSource_11

run_cmd Lean.logInfo "COMPONENT_SOURCE_END: PaperVerification.PluckerWeightOrder"

section ComponentSource_12
/- Original module: PaperVerification.ProjSurjectionRange -/


/-!
# The image of an actual surjective graded Proj map

The image consists precisely of the relevant homogeneous prime ideals
containing the literal kernel. This provides the underlying closed sets
of the homogeneous-coordinate filtration without replacing its schemes
by zero loci or by sets of closed points.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

open AlgebraicGeometry CategoryTheory
open scoped HomogeneousIdeal

namespace PaperVerification

universe u
variable {A B σ τ : Type u} [CommRing A] [CommRing B]
  [SetLike σ A] [AddSubgroupClass σ A]
  [SetLike τ B] [AddSubgroupClass τ B]
  {𝒜 : ℕ → σ} {ℬ : ℕ → τ} [GradedRing 𝒜] [GradedRing ℬ]

/-- A graded map preserves every element of positive homogeneous degree. -/
theorem irrelevant_le_comap_graded (f : 𝒜 →+*ᵍ ℬ) :
    𝒜₊ ≤ ℬ₊.comap f := by
  apply _root_.toIdeal_le_toIdeal_iff.mp
  apply (HomogeneousIdeal.toIdeal_irrelevant_le 𝒜).mpr
  intro d hd a ha
  exact HomogeneousIdeal.mem_irrelevant_of_mem ℬ hd (f.map_mem ha)

/-- Surjectivity on rings identifies the actual image of the Proj map
with the homogeneous primes containing its kernel. -/
theorem range_projMap_of_surjective (f : 𝒜 →+*ᵍ ℬ)
    (hf : ℬ₊ ≤ 𝒜₊.map f) (hs : Function.Surjective f)
    (p : ProjectiveSpectrum 𝒜) :
    p ∈ Set.range (Proj.map f hf) ↔ RingHom.ker f.toRingHom ≤ p.asHomogeneousIdeal.toIdeal := by
  constructor
  · rintro ⟨q, rfl⟩ a ha
    change f a ∈ q.asHomogeneousIdeal.toIdeal
    have hfa : f a = 0 := RingHom.mem_ker.mp ha
    exact hfa.symm ▸ Ideal.zero_mem _
  · intro hk
    have hback : (p.asHomogeneousIdeal.map f).comap f = p.asHomogeneousIdeal := by
      apply HomogeneousIdeal.ext
      change (p.asHomogeneousIdeal.toIdeal.map f.toRingHom).comap f.toRingHom = _
      rw [Ideal.comap_map_of_surjective' f.toRingHom hs, sup_eq_left.mpr hk]
    let q : ProjectiveSpectrum ℬ := {
      asHomogeneousIdeal := p.asHomogeneousIdeal.map f
      isPrime := Ideal.map_isPrime_of_surjective hs hk
      not_irrelevant_le := by
        intro h
        apply p.not_irrelevant_le
        rw [← hback]
        exact (irrelevant_le_comap_graded f).trans (HomogeneousIdeal.comap_mono f h) }
    refine ⟨q, ?_⟩
    apply ProjectiveSpectrum.ext
    exact hback

namespace HomogeneousQuotientProjective

open MvPolynomial
attribute [local instance] MvPolynomial.gradedAlgebra

variable {K ι : Type} [Field K]
    (I J : Ideal (MvPolynomial ι K))
    (hI : I.IsHomogeneous (homogeneousSubmodule ι K))
    (hJ : J.IsHomogeneous (homogeneousSubmodule ι K))
    (hIJ : I ≤ J)

/-- Exact prime-ideal description of the accepted homogeneous quotient
closed immersion. -/
theorem quotientProjMap_range (p : ProjectiveSpectrum (grading I hI)) :
    p ∈ Set.range (quotientProjMap I J hI hJ hIJ) ↔
      J ≤ p.asHomogeneousIdeal.toIdeal.comap (Ideal.Quotient.mk I) := by
  rw [quotientProjMap, range_projMap_of_surjective _ _ (Ideal.Quotient.factor_surjective hIJ)]
  change RingHom.ker (Ideal.Quotient.factor hIJ) ≤ p.asHomogeneousIdeal.toIdeal ↔ _
  rw [Ideal.Quotient.factor_ker, Ideal.map_le_iff_le_comap]

end HomogeneousQuotientProjective
end PaperVerification
end
end
end ComponentSource_12

run_cmd Lean.logInfo "COMPONENT_SOURCE_END: PaperVerification.ProjSurjectionRange"

section ComponentSource_13
/- Original module: PaperVerification.IsotropicAttractingEmpty -/


/-!
# The empty attracting charts

If a pivot coordinate plane is not common isotropic, its row-echelon
chart contains an original isotropy equation equal to a unit.  Thus the
entire scheme-theoretic chart is empty, including over nonreduced rings.
Combined with the elimination theorem, this gives the exact nonempty-cell
indexing condition, without a field-point or reducedness argument.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

namespace PaperVerification.IsotropicAttractingCoordinates

open MvPolynomial

variable {R : Type*} [CommRing R] {n s : ℕ}

@[simp] theorem equation_constantCoeff (p : Fin s ↪ Fin n) (c : ℕ) (i j : Fin s) :
    (equation (R := R) p c i j).constantCoeff = formMatrix c (p i) (p j) := by
  classical
  simp [equation, row_constantCoeff, mul_ite]

/-- Weight zero leaves exactly the original pivot-pair coefficient. -/
theorem equation_eq_constant_of_zero_weight (p : Fin s ↪ Fin n) (c : ℕ)
    (i j : Fin s) (hc : (p i).val + (p j).val = c) :
    equation (R := R) p c i j = C (formMatrix c (p i) (p j)) := by
  have hh := equation_homogeneous (R := R) p c i j
  have hd : c - (p i).val - (p j).val = 0 := by omega
  rw [hd] at hh
  calc
    _ = weightedHomogeneousComponent (coordinateWeight p) 0 (equation p c i j) :=
      (weightedHomogeneousComponent_eq_self hh).symm
    _ = C ((equation p c i j).coeff 0) :=
      weightedHomogeneousComponent_zero _ (fun v => ne_of_gt (coordinateWeight_pos p v))
    _ = _ := congrArg C (equation_constantCoeff p c i j)

variable {k : ℕ} {p : Fin s ↪ Fin (2*k+1)}

/-- A forbidden pivot edge gives the unit ideal, rather than an extra
nonempty component with a nonisotropic torus limit. -/
theorem isotropyIdeal_eq_top_of_not_independent (hp : ¬ IndependentPivots p) :
    isotropyIdeal (R := R) p (2*k+1) (2*k) = ⊤ := by
  classical
  unfold IndependentPivots at hp
  push Not at hp
  obtain ⟨i, j, hij, he⟩ := hp
  have hpi : p i ≠ p j := fun h => hij (p.injective h)
  have obtain_unit (c : ℕ) (hc : c = 2*k+1 ∨ c = 2*k)
      (hsum : (p i).val + (p j).val = c) :
      (1 : MvPolynomial (Coordinate p) R) ∈ isotropyIdeal p (2*k+1) (2*k) := by
    have hmem : equation (R := R) p c i j ∈ isotropyIdeal p (2*k+1) (2*k) := by
      apply Ideal.subset_span
      rcases hc with rfl | rfl
      · exact ⟨(true, i, j), rfl⟩
      · exact ⟨(false, i, j), rfl⟩
    rw [equation_eq_constant_of_zero_weight p c i j hsum] at hmem
    rcases lt_or_gt_of_ne hpi with hlt | hgt
    · have hcoeff : formMatrix (R := R) c (p i) (p j) = -1 := by
        simp [formMatrix, hsum, hlt, not_lt_of_gt hlt]
      have hn := neg_mem hmem
      simpa only [hcoeff, map_neg, map_one, neg_neg] using hn
    · have hcoeff : formMatrix (R := R) c (p i) (p j) = 1 := by
        simp [formMatrix, hsum, hgt]
      simpa only [hcoeff, map_one] using hmem
  apply (Ideal.eq_top_iff_one _).mpr
  by_cases h : (p i).val + (p j).val = 2*k
  · exact obtain_unit (2*k) (Or.inr rfl) h
  · exact obtain_unit (2*k+1) (Or.inl rfl) (he h)

end PaperVerification.IsotropicAttractingCoordinates
end
end
end ComponentSource_13

run_cmd Lean.logInfo "COMPONENT_SOURCE_END: PaperVerification.IsotropicAttractingEmpty"

section ComponentSource_14
/- Original module: PaperVerification.IsotropicAttractingSchemeFiltration -/


/-!
# A finite filtration of the actual common-isotropic projective scheme

The stage at `m` is the original homogeneous quotient with the first `m`
Plücker coordinates set to zero. Its inclusion is a genuine closed
immersion. The next complement is its genuine pivot basic open, whose
full coordinate ring was computed in the preceding files. Independent
pivots give affine spaces, and every other pivot gives an empty scheme.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

namespace PaperVerification.IsotropicAttractingCharts

open MvPolynomial AlgebraicGeometry CategoryTheory TopologicalSpace
open PaperVerification.AlternatingForms
open PaperVerification.IsotropicAttractingCoordinates

attribute [local instance] MvPolynomial.gradedAlgebra

variable {K : Type} [Field K] [CharZero K] {n t : ℕ}

/-- The actual projective scheme at a set of vanishing original
homogeneous coordinates. -/
def filtrationScheme (E : Set (PluckerIndex (t+2) n)) (c₁ c₂ : ℕ) : Scheme :=
  Proj (HomogeneousQuotientProjective.grading (filtrationIdeal (K := K) E c₁ c₂)
    (filtrationIdeal_isHomogeneous E c₁ c₂))

theorem originalIdeal_le_filtrationIdeal
    (E : Set (PluckerIndex (t+2) n)) (c₁ c₂ : ℕ) :
    isotropicPluckerIdeal (t := t) (canonicalForms (K := K) (n := n) c₁ c₂) ≤
      filtrationIdeal E c₁ c₂ := le_sup_left

/-- Inclusion into the original common-isotropic projective scheme. -/
def filtrationToOriginal (E : Set (PluckerIndex (t+2) n)) (c₁ c₂ : ℕ) :
    filtrationScheme (K := K) E c₁ c₂ ⟶
      Proj (isotropicProjectiveGrading (t := t) (canonicalForms (K := K) (n := n) c₁ c₂)) :=
  HomogeneousQuotientProjective.quotientProjMap
    (isotropicPluckerIdeal (canonicalForms (K := K) (n := n) c₁ c₂)) (filtrationIdeal E c₁ c₂)
    (isotropicPluckerIdeal_isHomogeneous (canonicalForms (K := K) (n := n) c₁ c₂))
    (filtrationIdeal_isHomogeneous E c₁ c₂) (originalIdeal_le_filtrationIdeal E c₁ c₂)

instance filtrationToOriginal_isClosedImmersion
    (E : Set (PluckerIndex (t+2) n)) (c₁ c₂ : ℕ) :
    IsClosedImmersion (filtrationToOriginal (K := K) E c₁ c₂) :=
  inferInstanceAs (IsClosedImmersion (HomogeneousQuotientProjective.quotientProjMap _ _ _ _ _))

/-- Inclusion of a later filtration stage into an earlier stage. -/
def filtrationInclusion {E F : Set (PluckerIndex (t+2) n)} (hEF : E ⊆ F) (c₁ c₂ : ℕ) :
    filtrationScheme (K := K) F c₁ c₂ ⟶ filtrationScheme (K := K) E c₁ c₂ :=
  HomogeneousQuotientProjective.quotientProjMap
    (filtrationIdeal E c₁ c₂) (filtrationIdeal F c₁ c₂)
    (filtrationIdeal_isHomogeneous E c₁ c₂)
    (filtrationIdeal_isHomogeneous F c₁ c₂) (filtrationIdeal_mono hEF c₁ c₂)

instance filtrationInclusion_isClosedImmersion
    {E F : Set (PluckerIndex (t+2) n)} (hEF : E ⊆ F) (c₁ c₂ : ℕ) :
    IsClosedImmersion (filtrationInclusion (K := K) hEF c₁ c₂) :=
  inferInstanceAs (IsClosedImmersion (HomogeneousQuotientProjective.quotientProjMap _ _ _ _ _))

/-- The exact underlying prime-ideal condition on the actual stage image. -/
theorem filtrationToOriginal_range
    (E : Set (PluckerIndex (t+2) n)) (c₁ c₂ : ℕ)
    (x : Proj (isotropicProjectiveGrading (t := t) (canonicalForms (K := K) (n := n) c₁ c₂))) :
    x ∈ Set.range (filtrationToOriginal E c₁ c₂) ↔
      ∀ I ∈ E, Ideal.Quotient.mk (isotropicPluckerIdeal (canonicalForms (K := K) (n := n) c₁ c₂)) (X I)
        ∈ x.asHomogeneousIdeal.toIdeal := by
  have hr := HomogeneousQuotientProjective.quotientProjMap_range
    (isotropicPluckerIdeal (t := t) (canonicalForms (K := K) (n := n) c₁ c₂))
    (filtrationIdeal (K := K) E c₁ c₂)
    (isotropicPluckerIdeal_isHomogeneous (canonicalForms (K := K) (n := n) c₁ c₂))
    (filtrationIdeal_isHomogeneous E c₁ c₂) (originalIdeal_le_filtrationIdeal E c₁ c₂) x
  refine hr.trans ?_
  rw [filtrationIdeal, sup_le_iff, Ideal.span_le]
  constructor
  · rintro ⟨_, hE⟩ I hI
    exact hE ⟨I, hI, rfl⟩
  · intro hE
    constructor
    · intro f hf
      change Ideal.Quotient.mk (isotropicPluckerIdeal (canonicalForms (K := K) (n := n) c₁ c₂)) f ∈
        x.asHomogeneousIdeal.toIdeal
      exact (Ideal.Quotient.eq_zero_iff_mem.mpr hf).symm ▸ Ideal.zero_mem _
    · rintro _ ⟨I, hI, rfl⟩
      exact hE I hI

/-- The actual pivot basic open in a homogeneous filtration stage. -/
def filtrationChart (E : Set (PluckerIndex (t+2) n)) (p : PluckerIndex (t+2) n)
    (c₁ c₂ : ℕ) : (filtrationScheme (K := K) E c₁ c₂).Opens :=
  Proj.basicOpen
    (HomogeneousQuotientProjective.grading (filtrationIdeal E c₁ c₂)
      (filtrationIdeal_isHomogeneous E c₁ c₂))
    (Ideal.Quotient.mk (filtrationIdeal E c₁ c₂) (X p))

/-- The stratum is an actual locally closed subscheme of the original
common-isotropic scheme, with its original full quotient structure. -/
def filtrationChartToOriginal (E : Set (PluckerIndex (t+2) n))
    (p : PluckerIndex (t+2) n) (c₁ c₂ : ℕ) :
    (filtrationChart (K := K) E p c₁ c₂).toScheme ⟶
      Proj (isotropicProjectiveGrading (t := t) (canonicalForms (K := K) (n := n) c₁ c₂)) :=
  (filtrationChart E p c₁ c₂).ι ≫ filtrationToOriginal E c₁ c₂

/-- The affine chart of the actual homogeneous filtration has precisely
the original full echelon coordinate ring. -/
def filtrationChartIsoCell (E : Set (PluckerIndex (t+2) n))
    (p : PluckerIndex (t+2) n) (hE : EarlierSet p E) (c₁ c₂ : ℕ) :
    (filtrationChart (K := K) E p c₁ c₂).toScheme ≅
      Spec (CommRingCat.of (MvPolynomial (Coordinate (indexEmbedding p)) K ⧸
        isotropyIdeal (indexEmbedding p) c₁ c₂)) :=
  HomogeneousQuotientCharts.projectiveBasicOpenIsoNormalized
    (filtrationIdeal E c₁ c₂) (filtrationIdeal_isHomogeneous E c₁ c₂) p ≪≫
      Scheme.Spec.mapIso (normalizedFiltrationCellEquiv p E hE c₁ c₂).symm.toRingEquiv.toCommRingCatIso.op

/-- Each permitted stratum is an actual affine space. Its coordinate set
is finite because it is a subset of the original finite matrix entries. -/
def filtrationChartIsoAffine {k : ℕ} (E : Set (PluckerIndex (t+2) (2*k+1)))
    (p : PluckerIndex (t+2) (2*k+1)) (hE : EarlierSet p E)
    (hp : IndependentPivots (indexEmbedding p)) :
    (filtrationChart (K := K) E p (2*k+1) (2*k)).toScheme ≅
      Spec (CommRingCat.of (MvPolynomial {i : Coordinate (indexEmbedding p) //
        i ∉ Set.range (pivotEmbedding hp)} K)) :=
  filtrationChartIsoCell E p hE (2*k+1) (2*k) ≪≫
    Scheme.Spec.mapIso (attractingCoordinateRingEquiv hp).symm.toRingEquiv.toCommRingCatIso.op

/-- A forbidden pivot gives the empty actual stratum. -/
theorem filtrationChart_isEmpty_of_not_independent {k : ℕ}
    (E : Set (PluckerIndex (t+2) (2*k+1))) (p : PluckerIndex (t+2) (2*k+1))
    (hE : EarlierSet p E) (hp : ¬ IndependentPivots (indexEmbedding p)) :
    IsEmpty (filtrationChart (K := K) E p (2*k+1) (2*k)).toScheme := by
  have htop := isotropyIdeal_eq_top_of_not_independent (R := K) hp
  let e := filtrationChartIsoCell (K := K) E p hE (2*k+1) (2*k)
  have hsub : Subsingleton (MvPolynomial (Coordinate (indexEmbedding p)) K ⧸
      isotropyIdeal (indexEmbedding p) (2*k+1) (2*k)) := by
    rw [htop]
    infer_instance
  letI := hsub
  letI : IsEmpty (Spec (CommRingCat.of (MvPolynomial (Coordinate (indexEmbedding p)) K ⧸
      isotropyIdeal (indexEmbedding p) (2*k+1) (2*k)))) :=
    inferInstanceAs (IsEmpty (PrimeSpectrum _))
  exact Function.isEmpty e.hom

/-- Every finite stage is a genuine closed subset of the same original
projective scheme. -/
theorem isClosed_filtration_image (E : Set (PluckerIndex (t+2) n)) (c₁ c₂ : ℕ) :
    IsClosed (Set.range (filtrationToOriginal (K := K) E c₁ c₂)) :=
  (IsClosedImmersion.isClosedEmbedding (filtrationToOriginal E c₁ c₂)).isClosed_range

/-- The zero-th stage is the whole original projective scheme. -/
theorem filtration_image_zero (c₁ c₂ : ℕ) :
    Set.range (filtrationToOriginal (K := K) (pivotPrefix (t+2) n 0) c₁ c₂) = Set.univ := by
  ext x
  simp only [filtrationToOriginal_range, pivotPrefix_zero, Set.mem_empty_iff_false,
    IsEmpty.forall_iff, implies_true, Set.mem_univ]

/-- The actual affine stratum at a position in the finite weight order. -/
def orderedFiltrationCell (i : Fin (pivotCount (t+2) n)) (c₁ c₂ : ℕ) : Scheme :=
  (filtrationChart (K := K) (pivotPrefix (t+2) n i.val)
    (weightOrderedPivots (t+2) n i) c₁ c₂).toScheme

/-- Uniform affine-space description for every nonempty cell, including
the zero-dimensional cell whose polynomial coordinate type is empty. -/
def orderedFiltrationCellIsoAffine {k : ℕ}
    (i : Fin (pivotCount (t+2) (2*k+1)))
    (hp : IndependentPivots (indexEmbedding (weightOrderedPivots (t+2) (2*k+1) i))) :
    orderedFiltrationCell (K := K) i (2*k+1) (2*k) ≅
      Spec (CommRingCat.of (MvPolynomial {v : Coordinate
        (indexEmbedding (weightOrderedPivots (t+2) (2*k+1) i)) //
          v ∉ Set.range (pivotEmbedding hp)} K)) :=
  filtrationChartIsoAffine _ _ (pivotPrefix_earlier (t+2) (2*k+1) i) hp


/-- The underlying image of the actual basic-open stratum adds exactly
nonvanishing of its pivot coordinate to the closed-stage conditions. -/
theorem filtrationChartToOriginal_range
    (E : Set (PluckerIndex (t+2) n)) (p : PluckerIndex (t+2) n) (c₁ c₂ : ℕ)
    (x : Proj (isotropicProjectiveGrading (t := t) (canonicalForms (K := K) (n := n) c₁ c₂))) :
    x ∈ Set.range (filtrationChartToOriginal E p c₁ c₂) ↔
      x ∈ Set.range (filtrationToOriginal E c₁ c₂) ∧
      Ideal.Quotient.mk (isotropicPluckerIdeal (canonicalForms (K := K) (n := n) c₁ c₂)) (X p)
        ∉ x.asHomogeneousIdeal.toIdeal := by
  constructor
  · rintro ⟨y, rfl⟩
    constructor
    · exact ⟨y.val, rfl⟩
    · exact y.property
  · rintro ⟨⟨y, rfl⟩, hy⟩
    exact ⟨⟨y, hy⟩, rfl⟩

/-- The next stage adds precisely the next pivot coordinate. -/
theorem ordered_filtration_successor_mem
    (i : Fin (pivotCount (t+2) n)) (c₁ c₂ : ℕ)
    (x : Proj (isotropicProjectiveGrading (t := t) (canonicalForms (K := K) (n := n) c₁ c₂))) :
    x ∈ Set.range (filtrationToOriginal (pivotPrefix (t+2) n (i.val+1)) c₁ c₂) ↔
      x ∈ Set.range (filtrationToOriginal (pivotPrefix (t+2) n i.val) c₁ c₂) ∧
      Ideal.Quotient.mk (isotropicPluckerIdeal (canonicalForms (K := K) (n := n) c₁ c₂))
        (X (weightOrderedPivots (t+2) n i)) ∈ x.asHomogeneousIdeal.toIdeal := by
  rw [filtrationToOriginal_range, filtrationToOriginal_range,
    pivotPrefix_successor]
  constructor
  · intro h
    exact ⟨fun I hI => h I (Set.mem_insert_of_mem _ hI), h _ (Set.mem_insert _ _)⟩
  · rintro ⟨h, hp⟩ I hI
    rcases Set.mem_insert_iff.mp hI with rfl | hI
    · exact hp
    · exact h I hI

/-- Every displayed affine cell is exactly one difference of successive
actual closed-stage images. -/
theorem ordered_filtration_stratum
    (i : Fin (pivotCount (t+2) n)) (c₁ c₂ : ℕ) :
    Set.range (filtrationChartToOriginal (K := K)
      (pivotPrefix (t+2) n i.val) (weightOrderedPivots (t+2) n i) c₁ c₂) =
      Set.range (filtrationToOriginal (pivotPrefix (t+2) n i.val) c₁ c₂) \
        Set.range (filtrationToOriginal (pivotPrefix (t+2) n (i.val+1)) c₁ c₂) := by
  ext x
  rw [filtrationChartToOriginal_range, Set.mem_sdiff, ordered_filtration_successor_mem]
  tauto

/-- The closed-stage images form a finite decreasing filtration. -/
theorem ordered_filtration_antitone (c₁ c₂ : ℕ) :
    Antitone (fun m => Set.range
      (filtrationToOriginal (K := K) (pivotPrefix (t+2) n m) c₁ c₂)) := by
  intro a b hab x hx
  rw [filtrationToOriginal_range] at hx ⊢
  intro I hI
  exact hx I (pivotPrefix_mono (t+2) n hab hI)

/-- After the last Plücker coordinate vanishes, no projective point
remains. The proof uses the original actual basic-open cover. -/
theorem filtration_image_final (c₁ c₂ : ℕ) :
    Set.range (filtrationToOriginal (K := K)
      (pivotPrefix (t+2) n (pivotCount (t+2) n)) c₁ c₂) = ∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro x hx
  rw [filtrationToOriginal_range, pivotPrefix_all] at hx
  have hcover := isotropicProjBasicOpen_cover (t := t) (canonicalForms (K := K) (n := n) c₁ c₂)
  have hm : x ∈ (⨆ p : PluckerIndex (t+2) n,
      Proj.basicOpen (isotropicProjectiveGrading (t := t) (canonicalForms (K := K) (n := n) c₁ c₂))
        (Ideal.Quotient.mk (isotropicPluckerIdeal (canonicalForms (K := K) (n := n) c₁ c₂)) (X p))) := by
    rw [hcover]
    trivial
  obtain ⟨p, hp⟩ := TopologicalSpace.Opens.mem_iSup.mp hm
  exact hp (hx p (Set.mem_univ _))

end PaperVerification.IsotropicAttractingCharts
end
end
end ComponentSource_14

run_cmd Lean.logInfo "COMPONENT_SOURCE_END: PaperVerification.IsotropicAttractingSchemeFiltration"

section ComponentSource_15
/- Original module: PaperVerification.GradedProjScalarMap -/


/-!
# Scalar compatibility for genuine graded Proj maps

A graded ring map preserving the original coefficient algebra induces a
morphism over its spectrum.  This applies to all homogeneous quotient
closed immersions, without an invertibility hypothesis.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open AlgebraicGeometry CategoryTheory _root_.HomogeneousLocalization
open scoped HomogeneousIdeal

namespace PaperVerification

section GradedHom

variable {K A B : Type} [CommRing K] [CommRing A] [CommRing B]
  [Algebra K A] [Algebra K B]
  {𝒜 : ℕ → Submodule K A} {ℬ : ℕ → Submodule K B}
  [GradedAlgebra 𝒜] [GradedAlgebra ℬ]

/-- A scalar-preserving graded ring map induces an actual morphism over
the scalar spectrum.  Invertibility is unnecessary. -/
theorem gradedProjMap_over_hom (f : 𝒜 →+*ᵍ ℬ) (hf : ℬ₊ ≤ 𝒜₊.map f)
    (hc : ∀ c : K, f (algebraMap K A c) = algebraMap K B c) :
    Proj.map f hf ≫ gradedProjStructureMap 𝒜 = gradedProjStructureMap ℬ := by
  have haway (s : A) (c : K) :
      Away.map f s (fromZeroRingHom 𝒜 _ (algebraMap K (𝒜 0) c)) =
        fromZeroRingHom ℬ _ (algebraMap K (ℬ 0) c) := by
    apply _root_.HomogeneousLocalization.val_injective
    change Localization.mk (f (algebraMap K A c)) ⟨f 1,_⟩ =
      Localization.mk (algebraMap K B c) ⟨1,_⟩
    simp only [map_one,hc]
  apply (Proj.mapAffineOpenCover f hf).openCover.hom_ext
  intro s
  change Proj.awayι ℬ (f s.2.1) (f.map_mem s.2.2) s.1.2 ≫
      Proj.map f hf ≫ gradedProjStructureMap 𝒜 =
    Proj.awayι ℬ (f s.2.1) (f.map_mem s.2.2) s.1.2 ≫ gradedProjStructureMap ℬ
  simp only [gradedProjStructureMap, Category.assoc,
    Proj.awayι_comp_map_assoc f hf s.1.2 s.2.1 s.2.2,
    Proj.awayι_toSpecZero_assoc, Proj.awayι_toSpecZero]
  rw [← Spec.map_comp, ← Spec.map_comp, ← Spec.map_comp]
  congr 1
  ext c
  exact congrArg _root_.HomogeneousLocalization.val (haway s.2.1 c)

end GradedHom

namespace HomogeneousQuotientProjective

open MvPolynomial
attribute [local instance] MvPolynomial.gradedAlgebra

variable {K σ : Type} [Field K]
  (I J : Ideal (MvPolynomial σ K))
  (hI : I.IsHomogeneous (homogeneousSubmodule σ K))
  (hJ : J.IsHomogeneous (homogeneousSubmodule σ K)) (hIJ : I ≤ J)

theorem quotientProjMap_over :
    quotientProjMap I J hI hJ hIJ ≫ HomogeneousQuotientCharts.structureMap I hI =
      HomogeneousQuotientCharts.structureMap J hJ :=
  gradedProjMap_over_hom _ _ (fun _ => rfl)

end HomogeneousQuotientProjective

end PaperVerification
end
end
end ComponentSource_15

run_cmd Lean.logInfo "COMPONENT_SOURCE_END: PaperVerification.GradedProjScalarMap"

section ComponentSource_16
/- Original module: PaperVerification.IsotropicAttractingFiltrationOver -/


/-!
# The complete affine paving is over the original coefficient field

All closed-stage maps and affine-cell isomorphisms preserve the actual
structure morphism.  This is needed when passing to complex-valued points
or to the genuine dimension-graded Chow groups.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open AlgebraicGeometry CategoryTheory _root_.HomogeneousLocalization
open scoped HomogeneousIdeal

namespace PaperVerification

namespace IsotropicAttractingCharts

open MvPolynomial
open AlternatingForms IsotropicAttractingCoordinates

attribute [local instance] MvPolynomial.gradedAlgebra

variable {K : Type} [Field K] [CharZero K] {n t : ℕ}

def filtrationStructureMap (E : Set (PluckerIndex (t+2) n)) (c₁ c₂ : ℕ) :
    filtrationScheme (K := K) E c₁ c₂ ⟶ Spec (CommRingCat.of K) :=
  HomogeneousQuotientCharts.structureMap (filtrationIdeal E c₁ c₂)
    (filtrationIdeal_isHomogeneous E c₁ c₂)

theorem filtrationToOriginal_over (E : Set (PluckerIndex (t+2) n)) (c₁ c₂ : ℕ) :
    filtrationToOriginal (K := K) E c₁ c₂ ≫ isotropicStructureMap (canonicalForms c₁ c₂) =
      filtrationStructureMap E c₁ c₂ :=
  HomogeneousQuotientProjective.quotientProjMap_over _ _ _ _ _

theorem filtrationInclusion_over {E F : Set (PluckerIndex (t+2) n)}
    (hEF : E ⊆ F) (c₁ c₂ : ℕ) :
    filtrationInclusion (K := K) hEF c₁ c₂ ≫ filtrationStructureMap E c₁ c₂ =
      filtrationStructureMap F c₁ c₂ :=
  HomogeneousQuotientProjective.quotientProjMap_over _ _ _ _ _

theorem filtrationChartIsoCell_hom_over (E : Set (PluckerIndex (t+2) n))
    (p : PluckerIndex (t+2) n) (hE : EarlierSet p E) (c₁ c₂ : ℕ) :
    (filtrationChartIsoCell (K := K) E p hE c₁ c₂).hom ≫
      Spec.map (CommRingCat.ofHom (algebraMap K
        (MvPolynomial (Coordinate (indexEmbedding p)) K ⧸
          isotropyIdeal (indexEmbedding p) c₁ c₂))) =
      (filtrationChart E p c₁ c₂).ι ≫ filtrationStructureMap E c₁ c₂ := by
  rw [filtrationChartIsoCell, Iso.trans_hom, Category.assoc,
    specAlgEquiv_hom_over]
  exact HomogeneousQuotientCharts.projectiveBasicOpenIsoNormalized_hom_over _ _ _

theorem filtrationChartIsoAffine_hom_over {k : ℕ}
    (E : Set (PluckerIndex (t+2) (2*k+1))) (p : PluckerIndex (t+2) (2*k+1))
    (hE : EarlierSet p E) (hp : IndependentPivots (indexEmbedding p)) :
    (filtrationChartIsoAffine (K := K) E p hE hp).hom ≫
      Spec.map (CommRingCat.ofHom (algebraMap K
        (MvPolynomial {v : Coordinate (indexEmbedding p) //
          v ∉ Set.range (pivotEmbedding hp)} K))) =
      (filtrationChart E p (2*k+1) (2*k)).ι ≫
        filtrationStructureMap E (2*k+1) (2*k) := by
  rw [filtrationChartIsoAffine, Iso.trans_hom, Category.assoc,
    specAlgEquiv_hom_over]
  exact filtrationChartIsoCell_hom_over _ _ _ _ _

end IsotropicAttractingCharts
end PaperVerification
end
end
end ComponentSource_16

run_cmd Lean.logInfo "COMPONENT_SOURCE_END: PaperVerification.IsotropicAttractingFiltrationOver"

section ComponentSource_17
/- Original module: PaperVerification.IsotropicAttractingClosedCells -/


/-!
# The affine strata are closed in genuine ambient open subsets

This file supplies the geometry needed by both Chow localization and the
ordinary singular Thom sequence.  Consecutive projective stages are actual
closed complements.  Reversing the filtration realizes each nonempty affine
cell as a genuine closed immersion into an open subset of the original
smooth common-isotropic scheme.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

namespace PaperVerification.IsotropicAttractingCharts

open AlgebraicGeometry CategoryTheory TopologicalSpace MvPolynomial
open PaperVerification.AlternatingForms

attribute [local instance] MvPolynomial.gradedAlgebra

variable {K : Type} [Field K] [CharZero K] {n t : ℕ}

theorem filtrationInclusion_range {E F : Set (PluckerIndex (t+2) n)}
    (hEF : E ⊆ F) (c₁ c₂ : ℕ) (x : filtrationScheme (K := K) E c₁ c₂) :
    x ∈ Set.range (filtrationInclusion hEF c₁ c₂) ↔
      ∀ I ∈ F, Ideal.Quotient.mk (filtrationIdeal E c₁ c₂) (X I)
        ∈ x.asHomogeneousIdeal.toIdeal := by
  have hr := HomogeneousQuotientProjective.quotientProjMap_range
    (filtrationIdeal (K := K) E c₁ c₂) (filtrationIdeal (K := K) F c₁ c₂)
    (filtrationIdeal_isHomogeneous E c₁ c₂) (filtrationIdeal_isHomogeneous F c₁ c₂)
    (filtrationIdeal_mono hEF c₁ c₂) x
  refine hr.trans ?_
  rw [filtrationIdeal, sup_le_iff, Ideal.span_le]
  constructor
  · rintro ⟨_,h⟩ I hI
    exact h ⟨I,hI,rfl⟩
  · intro h
    constructor
    · intro q hq
      change Ideal.Quotient.mk (filtrationIdeal (K := K) E c₁ c₂) q ∈ x.asHomogeneousIdeal.toIdeal
      rw [Ideal.Quotient.eq_zero_iff_mem.mpr
        (show q ∈ filtrationIdeal E c₁ c₂ from Ideal.mem_sup_left hq)]
      exact Ideal.zero_mem _
    · rintro _ ⟨I,hI,rfl⟩
      exact h I hI

/-- The actual closed immersion of the next homogeneous stage. -/
def orderedFiltrationInclusion (i : Fin (pivotCount (t+2) n)) (c₁ c₂ : ℕ) :
    filtrationScheme (K := K) (pivotPrefix (t+2) n (i.val+1)) c₁ c₂ ⟶
      filtrationScheme (K := K) (pivotPrefix (t+2) n i.val) c₁ c₂ :=
  filtrationInclusion (pivotPrefix_mono (t+2) n (Nat.le_succ i.val)) c₁ c₂

instance orderedFiltrationInclusion_isClosedImmersion
    (i : Fin (pivotCount (t+2) n)) (c₁ c₂ : ℕ) :
    IsClosedImmersion (orderedFiltrationInclusion (K := K) i c₁ c₂) :=
  inferInstanceAs (IsClosedImmersion (filtrationInclusion _ _ _))

/-- Inside the current stage, the next stage is exactly the vanishing
locus of the current pivot coordinate. -/
theorem orderedFiltrationInclusion_range (i : Fin (pivotCount (t+2) n)) (c₁ c₂ : ℕ)
    (x : filtrationScheme (K := K) (pivotPrefix (t+2) n i.val) c₁ c₂) :
    x ∈ Set.range (orderedFiltrationInclusion i c₁ c₂) ↔
      Ideal.Quotient.mk (filtrationIdeal (pivotPrefix (t+2) n i.val) c₁ c₂)
        (X (weightOrderedPivots (t+2) n i)) ∈ x.asHomogeneousIdeal.toIdeal := by
  rw [orderedFiltrationInclusion, filtrationInclusion_range, pivotPrefix_successor]
  constructor
  · intro h
    exact h _ (Set.mem_insert _ _)
  · intro hp I hI
    rcases Set.mem_insert_iff.mp hI with rfl | hI
    · exact hp
    · rw [Ideal.Quotient.eq_zero_iff_mem.mpr
        (show X I ∈ filtrationIdeal (K := K) (pivotPrefix (t+2) n i.val) c₁ c₂ from
          (show Ideal.span (X '' pivotPrefix (t+2) n i.val) ≤
            filtrationIdeal (K := K) (pivotPrefix (t+2) n i.val) c₁ c₂ from le_sup_right)
              (Ideal.subset_span ⟨I,hI,rfl⟩))]
      exact Ideal.zero_mem _

/-- The exact closed/open complement assertion used by the genuine Chow
localization theorem, with the actual stage and cell morphisms. -/
theorem orderedFiltration_closed_open_complement
    (i : Fin (pivotCount (t+2) n)) (c₁ c₂ : ℕ) :
    Set.range (orderedFiltrationInclusion (K := K) i c₁ c₂) =
      (Set.range (filtrationChart (K := K) (pivotPrefix (t+2) n i.val)
        (weightOrderedPivots (t+2) n i) c₁ c₂).ι)ᶜ := by
  ext x
  rw [orderedFiltrationInclusion_range, Scheme.Opens.range_ι]
  change _ ↔ ¬ ¬ _
  exact not_not.symm

/-- The reversed filtration consists of actual opens of the original
projective scheme. -/
def orderedComplement (m : ℕ) (c₁ c₂ : ℕ) :
    (Proj (isotropicProjectiveGrading (t := t) (canonicalForms (K := K) (n := n) c₁ c₂))).Opens :=
  ⟨(Set.range (filtrationToOriginal (K := K) (pivotPrefix (t+2) n m) c₁ c₂))ᶜ,
    (isClosed_filtration_image _ _ _).isOpen_compl⟩

theorem orderedComplement_mono (c₁ c₂ : ℕ) :
    Monotone (fun m => orderedComplement (K := K) (n := n) (t := t) m c₁ c₂) := by
  intro a b hab
  exact Set.compl_subset_compl.mpr (ordered_filtration_antitone c₁ c₂ hab)

theorem orderedComplement_zero (c₁ c₂ : ℕ) :
    orderedComplement (K := K) (n := n) (t := t) 0 c₁ c₂ = ⊥ := by
  apply TopologicalSpace.Opens.ext
  change (Set.range (filtrationToOriginal (K := K) (pivotPrefix (t+2) n 0) c₁ c₂))ᶜ = ∅
  rw [filtration_image_zero, Set.compl_univ]

theorem orderedComplement_final (c₁ c₂ : ℕ) :
    orderedComplement (K := K) (n := n) (t := t) (pivotCount (t+2) n) c₁ c₂ = ⊤ := by
  apply TopologicalSpace.Opens.ext
  change (Set.range (filtrationToOriginal (K := K)
    (pivotPrefix (t+2) n (pivotCount (t+2) n)) c₁ c₂))ᶜ = Set.univ
  rw [filtration_image_final, Set.compl_empty]

/-- Pulling the next ambient complement back to the current closed stage
gives exactly its original pivot chart. -/
theorem orderedComplement_preimage (i : Fin (pivotCount (t+2) n)) (c₁ c₂ : ℕ) :
    filtrationToOriginal (K := K) (pivotPrefix (t+2) n i.val) c₁ c₂ ⁻¹ᵁ
      orderedComplement (i.val+1) c₁ c₂ =
        filtrationChart (pivotPrefix (t+2) n i.val)
          (weightOrderedPivots (t+2) n i) c₁ c₂ := by
  ext x
  change ¬ (filtrationToOriginal (K := K) (pivotPrefix (t+2) n i.val) c₁ c₂) x ∈
    Set.range (filtrationToOriginal (pivotPrefix (t+2) n (i.val+1)) c₁ c₂) ↔ _
  rw [ordered_filtration_successor_mem]
  have hx : (filtrationToOriginal (K := K) (pivotPrefix (t+2) n i.val) c₁ c₂) x ∈
      Set.range (filtrationToOriginal (pivotPrefix (t+2) n i.val) c₁ c₂) := ⟨x,rfl⟩
  simp only [hx, true_and]
  rfl

/-- The cell is a genuine closed subscheme of the next ambient open.
This is base change of the original projective closed immersion. -/
def orderedCellClosedMap (i : Fin (pivotCount (t+2) n)) (c₁ c₂ : ℕ) :
    orderedFiltrationCell (K := K) i c₁ c₂ ⟶
      (orderedComplement (K := K) (n := n) (t := t) (i.val+1) c₁ c₂).toScheme :=
  (Scheme.isoOfEq _ (orderedComplement_preimage (K := K) i c₁ c₂)).inv ≫
    (filtrationToOriginal (pivotPrefix (t+2) n i.val) c₁ c₂ ∣_
      orderedComplement (i.val+1) c₁ c₂)

instance orderedCellClosedMap_isClosedImmersion
    (i : Fin (pivotCount (t+2) n)) (c₁ c₂ : ℕ) :
    IsClosedImmersion (orderedCellClosedMap (K := K) i c₁ c₂) := by
  unfold orderedCellClosedMap
  infer_instance

theorem orderedCellClosedMap_comp_ι (i : Fin (pivotCount (t+2) n)) (c₁ c₂ : ℕ) :
    orderedCellClosedMap (K := K) i c₁ c₂ ≫
      (orderedComplement (K := K) (n := n) (t := t) (i.val+1) c₁ c₂).ι =
        filtrationChartToOriginal (pivotPrefix (t+2) n i.val)
          (weightOrderedPivots (t+2) n i) c₁ c₂ := by
  rw [orderedCellClosedMap, Category.assoc, morphismRestrict_ι,
    Scheme.isoOfEq_inv_ι_assoc]
  rfl

end PaperVerification.IsotropicAttractingCharts
end
end
end ComponentSource_17

run_cmd Lean.logInfo "COMPONENT_SOURCE_END: PaperVerification.IsotropicAttractingClosedCells"

section ComponentSource_18
/- Original module: PaperVerification.IsotropicAttractingOpenFiltration -/


/-!
# Closed affine cells in the increasing open filtration

The morphism from one ambient open to the next is the actual restriction
inclusion.  Its closed complement is exactly the already constructed affine
cell, with the same original scheme structure and the same structure map.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace PaperVerification.IsotropicAttractingCharts

open AlgebraicGeometry CategoryTheory
open PaperVerification.AlternatingForms

variable {K : Type} [Field K] [CharZero K] {n t : ℕ}

/-- The actual inclusion of successive ambient open subsets. -/
def orderedOpenInclusion (m : ℕ) (c₁ c₂ : ℕ) :
    (orderedComplement (K := K) (n := n) (t := t) m c₁ c₂).toScheme ⟶
      (orderedComplement (K := K) (n := n) (t := t) (m+1) c₁ c₂).toScheme :=
  Scheme.homOfLE _ (orderedComplement_mono c₁ c₂ (Nat.le_succ m))

instance orderedOpenInclusion_isOpenImmersion (m : ℕ) (c₁ c₂ : ℕ) :
    IsOpenImmersion (orderedOpenInclusion (K := K) (n := n) (t := t) m c₁ c₂) := by
  unfold orderedOpenInclusion
  infer_instance

theorem orderedOpenInclusion_comp_ι (m : ℕ) (c₁ c₂ : ℕ) :
    orderedOpenInclusion (K := K) (n := n) (t := t) m c₁ c₂ ≫
      (orderedComplement (K := K) (n := n) (t := t) (m+1) c₁ c₂).ι =
        (orderedComplement (K := K) (n := n) (t := t) m c₁ c₂).ι :=
  Scheme.homOfLE_ι _ _

theorem orderedOpenInclusion_range (m : ℕ) (c₁ c₂ : ℕ)
    (x : (orderedComplement (K := K) (n := n) (t := t) (m+1) c₁ c₂).toScheme) :
    x ∈ Set.range (orderedOpenInclusion (K := K) (n := n) (t := t) m c₁ c₂) ↔
      x.val ∈ orderedComplement (K := K) (n := n) (t := t) m c₁ c₂ := by
  constructor
  · rintro ⟨y,rfl⟩
    simpa only [orderedOpenInclusion, Scheme.homOfLE_apply] using y.property
  · intro hx
    refine ⟨⟨x.val,hx⟩,?_⟩
    apply Subtype.ext
    exact Scheme.homOfLE_apply _ _

/-- The actual cell is the closed complement of the preceding ambient
open inside the next one. This is the pair used by the Thom sequence. -/
theorem orderedCellClosedMap_range (i : Fin (pivotCount (t+2) n)) (c₁ c₂ : ℕ) :
    Set.range (orderedCellClosedMap (K := K) i c₁ c₂) =
      (Set.range (orderedOpenInclusion (K := K) (n := n) (t := t) i.val c₁ c₂))ᶜ := by
  ext x
  rw [Set.mem_compl_iff, orderedOpenInclusion_range]
  have hr : x ∈ Set.range (orderedCellClosedMap (K := K) i c₁ c₂) ↔
      x.val ∈ Set.range (filtrationChartToOriginal (K := K)
        (pivotPrefix (t+2) n i.val) (weightOrderedPivots (t+2) n i) c₁ c₂) := by
    rw [← orderedCellClosedMap_comp_ι]
    constructor
    · rintro ⟨y,rfl⟩
      exact ⟨y,rfl⟩
    · rintro ⟨y,hy⟩
      exact ⟨y,Subtype.ext hy⟩
  rw [hr, ordered_filtration_stratum, Set.mem_sdiff]
  change (_ ∧ _) ↔ ¬ ¬ _
  have hx := x.property
  change ¬ x.val ∈ Set.range (filtrationToOriginal (K := K)
    (pivotPrefix (t+2) n (i.val+1)) c₁ c₂) at hx
  simp only [hx, not_false_eq_true, and_true, not_not]

end PaperVerification.IsotropicAttractingCharts
end
end
end ComponentSource_18

run_cmd Lean.logInfo "COMPONENT_SOURCE_END: PaperVerification.IsotropicAttractingOpenFiltration"

section ComponentSource_19
/- Original module: PaperVerification.IsotropicAttractingCount -/


/-!
# Counting the actual attracting-chart indices

The geometric charts are indexed by increasing Plücker indices satisfying
the two literal isotropy conditions.  This file identifies that indexing
type with the independent subsets already counted in `OddPathIndependent`.
The equivalence retains the original chart indices; no geometric dimension
or cohomological assertion is built into the counting type.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

namespace PaperVerification.IsotropicAttractingCharts

open PaperVerification.AlternatingForms
open PaperVerification.IsotropicAttractingCoordinates
open PaperVerification.OddPathIndependent

/-- Increasing Plücker indices are precisely order embeddings. -/
def pluckerIndexOrderEmbeddingEquiv (s n : ℕ) :
    PluckerIndex s n ≃ (Fin s ↪o Fin n) where
  toFun p := OrderEmbedding.ofStrictMono p.val p.property
  invFun e := ⟨e, e.strictMono⟩
  left_inv p := by apply Subtype.ext; rfl
  right_inv e := by ext i; rfl

/-- Taking the image gives the underlying subset of an increasing index. -/
def pluckerIndexSubsetEquiv (s n : ℕ) :
    PluckerIndex s n ≃ {S : Finset (Fin n) // S.card = s} :=
  (pluckerIndexOrderEmbeddingEquiv s n).trans
    (SeparatedSubsets.orderEmbeddingEquivSubsets n s)

@[simp] theorem pluckerIndexSubsetEquiv_val (s n : ℕ) (p : PluckerIndex s n) :
    (pluckerIndexSubsetEquiv s n p).val = Finset.univ.map (indexEmbedding p) := rfl

theorem independentPivots_iff_chainIndependent {k s : ℕ}
    (p : PluckerIndex s (2*k+1)) :
    IndependentPivots (indexEmbedding p) ↔
      ChainIndependent k (Finset.univ.map (indexEmbedding p)) := by
  classical
  constructor
  · intro hp a ha b hb
    obtain ⟨i, _, rfl⟩ := Finset.mem_map.mp ha
    obtain ⟨j, _, rfl⟩ := Finset.mem_map.mp hb
    by_cases hij : i = j
    · exact Or.inl (congrArg (indexEmbedding p) hij)
    · exact Or.inr (hp i j hij)
  · intro hp i j hij
    have hi : indexEmbedding p i ∈ Finset.univ.map (indexEmbedding p) :=
      Finset.mem_map.mpr ⟨i, Finset.mem_univ _, rfl⟩
    have hj : indexEmbedding p j ∈ Finset.univ.map (indexEmbedding p) :=
      Finset.mem_map.mpr ⟨j, Finset.mem_univ _, rfl⟩
    rcases hp _ hi _ hj with he | he
    · exact (hij ((indexEmbedding p).injective he)).elim
    · exact he

/-- The indices of the nonempty attracting cells. -/
abbrev IndependentPluckerIndices (k s : ℕ) :=
  {p : PluckerIndex s (2*k+1) // IndependentPivots (indexEmbedding p)}

/-- The chart indexing type and the independently counted subset type agree. -/
def independentPluckerEquivCoordinateSubsets (k s : ℕ) :
    IndependentPluckerIndices k s ≃ CoordinateSubsets k s where
  toFun p := ⟨(pluckerIndexSubsetEquiv s (2*k+1) p.val).val,
    (pluckerIndexSubsetEquiv s (2*k+1) p.val).property,
    (independentPivots_iff_chainIndependent p.val).mp p.property⟩
  invFun S := ⟨(pluckerIndexSubsetEquiv s (2*k+1)).symm ⟨S.val, S.property.1⟩, by
    apply (independentPivots_iff_chainIndependent _).mpr
    change ChainIndependent k
      (pluckerIndexSubsetEquiv s (2*k+1)
        ((pluckerIndexSubsetEquiv s (2*k+1)).symm ⟨S.val, S.property.1⟩)).val
    rw [Equiv.apply_symm_apply]
    exact S.property.2⟩
  left_inv p := by
    apply Subtype.ext
    exact (pluckerIndexSubsetEquiv s (2*k+1)).symm_apply_apply p.val
  right_inv S := by
    apply Subtype.ext
    change ((pluckerIndexSubsetEquiv s (2*k+1))
      ((pluckerIndexSubsetEquiv s (2*k+1)).symm ⟨S.val,S.property.1⟩)).val = S.val
    exact congrArg (fun T : {S : Finset (Fin (2*k+1)) // S.card = s} => T.val)
      ((pluckerIndexSubsetEquiv s (2*k+1)).apply_symm_apply ⟨S.val, S.property.1⟩)

/-- The complete binomial count for the actual attracting cells. -/
theorem card_independentPluckerIndices (k s : ℕ) (hs : s ≤ k+1) :
    Nat.card (IndependentPluckerIndices k s) = Nat.choose (2*k+2-s) s := by
  rw [Nat.card_congr (independentPluckerEquivCoordinateSubsets k s)]
  exact card_coordinateSubsets k s hs

end PaperVerification.IsotropicAttractingCharts
end
end
end ComponentSource_19

run_cmd Lean.logInfo "COMPONENT_SOURCE_END: PaperVerification.IsotropicAttractingCount"

section ComponentSource_20
/- Original module: PaperVerification.IsotropicAttractingCellBudget -/


/-!
# The exact size of the finite affine paving

The budget is one precisely for an independent original pivot and zero for
an empty stratum. Its sum counts every nonempty cell once, independently of
the arbitrary tie-breaking in the finite Plücker weight order.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

namespace PaperVerification.IsotropicAttractingCharts

open PaperVerification.AlternatingForms
open PaperVerification.IsotropicAttractingCoordinates
open scoped BigOperators
attribute [local instance] Classical.propDecidable

def cellBudget (k s m : ℕ) : ℕ := by
  classical
  exact if h : m < pivotCount s (2*k+1) then
    if IndependentPivots (indexEmbedding (weightOrderedPivots s (2*k+1) ⟨m,h⟩)) then 1 else 0
  else 0

theorem cellBudget_at (k s : ℕ) (i : Fin (pivotCount s (2*k+1))) :
    cellBudget k s i.val =
      if IndependentPivots (indexEmbedding (weightOrderedPivots s (2*k+1) i)) then 1 else 0 := by
  classical
  simp only [cellBudget, dite_eq_left i.isLt]

def orderedIndependentEquiv (k s : ℕ) :
    {i : Fin (pivotCount s (2*k+1)) //
      IndependentPivots (indexEmbedding (weightOrderedPivots s (2*k+1) i))} ≃
        IndependentPluckerIndices k s :=
  Equiv.subtypeEquivOfSubtype
    (p := fun p : PluckerIndex s (2*k+1) => IndependentPivots (indexEmbedding p))
    (weightOrderedPivots s (2*k+1))

theorem sum_cellBudget (k s : ℕ) (hs : s ≤ k+1) :
    ∑ m ∈ Finset.range (pivotCount s (2*k+1)), cellBudget k s m =
      Nat.choose (2*k+2-s) s := by
  classical
  rw [← Fin.sum_univ_eq_sum_range]
  simp only [cellBudget_at]
  have hc : (∑ i : Fin (pivotCount s (2*k+1)),
      if IndependentPivots (indexEmbedding (weightOrderedPivots s (2*k+1) i)) then 1 else 0) =
        Nat.card {i : Fin (pivotCount s (2*k+1)) //
          IndependentPivots (indexEmbedding (weightOrderedPivots s (2*k+1) i))} := by
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
    simp
  rw [hc, Nat.card_congr (orderedIndependentEquiv k s)]
  exact card_independentPluckerIndices k s hs

end PaperVerification.IsotropicAttractingCharts
end
end
end ComponentSource_20

run_cmd Lean.logInfo "COMPONENT_SOURCE_END: PaperVerification.IsotropicAttractingCellBudget"

section ComponentSource_21
/- Original module: PaperVerification.IsotropicAttractingCanonicalComparison -/


/-!
# The attracting-chart coordinates are the paper's actual canonical pencil

The elimination files use the chain order `b₀,…,bₖ,aₖ,…,a₁`.  The original
geometric proof uses `b₀,a₁,b₁,…,aₖ,bₖ`.  The explicit permutation below
identifies both literal exterior two-forms, hence their original homogeneous
ideals and projective zero schemes.  Smoothness is transported over the
ground field, with no extra geometric hypothesis.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace PaperVerification.IsotropicAttractingCharts

open AlgebraicGeometry CategoryTheory
open PaperVerification.AlternatingForms
open PaperVerification.IsotropicAttractingCoordinates
open PaperVerification.OddPathIndependent
open scoped BigOperators

variable {K : Type} [Field K]

/-- The exact coordinate permutation on vectors. -/
def pathChainLinearEquiv (k : ℕ) : (Fin (2*k+1) → K) ≃ₗ[K] (Fin (2*k+1) → K) where
  toFun x i := x ((pathChainEquiv k).symm i)
  invFun x i := x (pathChainEquiv k i)
  left_inv x := by funext i; exact congrArg x ((pathChainEquiv k).symm_apply_apply i)
  right_inv x := by funext i; exact congrArg x ((pathChainEquiv k).apply_symm_apply i)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem orbitExteriorCoefficient_pathChain (k : ℕ) (i j : Fin (2*k+1))
    (f : ⋀[K]^2 (Fin (2*k+1) → K)) :
    orbitExteriorCoefficientMatrix
      (exteriorPower.map 2 (pathChainLinearEquiv (K := K) k).toLinearMap f)
      (pathChainEquiv k i) (pathChainEquiv k j) =
      orbitExteriorCoefficientMatrix f i j := by
  have h : (orbitExteriorCoefficient (K := K) (pathChainEquiv k i) (pathChainEquiv k j)).comp
      (exteriorPower.map 2 (pathChainLinearEquiv k).toLinearMap) =
        orbitExteriorCoefficient i j := by
    apply exteriorPower.linearMap_ext
    apply AlternatingMap.ext
    intro w
    simp only [LinearMap.compAlternatingMap_apply, LinearMap.comp_apply,
      exteriorPower.map_apply_ιMulti, orbitExteriorCoefficient_word,
      Function.comp_apply, LinearEquiv.coe_coe, pathChainLinearEquiv,
      Equiv.symm_apply_apply]
    change w 0 ((pathChainEquiv k).symm (pathChainEquiv k i)) *
        w 1 ((pathChainEquiv k).symm (pathChainEquiv k j)) -
      w 0 ((pathChainEquiv k).symm (pathChainEquiv k j)) *
        w 1 ((pathChainEquiv k).symm (pathChainEquiv k i)) = _
    simp only [Equiv.symm_apply_apply]
  exact congrArg (fun L : (⋀[K]^2 (Fin (2*k+1) → K)) →ₗ[K] K => L f) h

theorem coefficientMatrix_twoForm_upper {n : ℕ} (f : StrictPairs n → K)
    (i j : Fin n) (hij : i < j) :
    orbitExteriorCoefficientMatrix (twoFormOfCoefficients f (Pi.basisFun K (Fin n))) i j =
      f ⟨(i,j),hij⟩ :=
  orbitTwoFormOfSlots_coefficient (strictPairSlots n) f ⟨(i,j),hij⟩

/-- The chain coefficient convention is the literal alternating matrix
used by the polynomial equations. -/
theorem coefficientMatrix_canonicalCoefficient {n : ℕ} (c : ℕ) (i j : Fin n) :
    orbitExteriorCoefficientMatrix
      (twoFormOfCoefficients (canonicalCoefficient (K := K) c) (Pi.basisFun K (Fin n))) i j =
        formMatrix c i j := by
  rcases lt_trichotomy i j with h | rfl | h
  · exact coefficientMatrix_twoForm_upper _ i j h
  · rw [orbitExteriorCoefficientMatrix_diagonal, formMatrix_self]
  · rw [orbitExteriorCoefficientMatrix_skew,
      coefficientMatrix_twoForm_upper _ j i h, formMatrix_swap]
    rfl

/-- A path coefficient is nonzero exactly on its correctly colored edge. -/
theorem oddPluckerForms_edge_value (k : ℕ) (l : Fin 2) (a : StrictPairs (2*k+1)) :
    oddPluckerForms (K := K) k l a =
      if a.val.1.val % 2 = l.val ∧ a.val.2.val = a.val.1.val + 1 then 1 else 0 := by
  classical
  have ha := a.property
  have hb := a.val.2.isLt
  have hl := l.isLt
  unfold oddPluckerForms
  by_cases h : a.val.1.val % 2 = l.val ∧ a.val.2.val = a.val.1.val + 1
  · rw [if_pos h]
    let i : Fin k := ⟨a.val.1.val / 2, by omega⟩
    have hai : a = oddPluckerEdge k l i := by
      apply Subtype.ext
      apply Prod.ext <;> apply Fin.ext <;> dsimp [oddPluckerEdge, i] <;> omega
    rw [Finset.sum_eq_single i]
    · simp [hai]
    · intro j _ hji
      have hne : a ≠ oddPluckerEdge k l j := by
        intro he
        have hv := congrArg (fun q : StrictPairs (2*k+1) => q.val.1.val) (hai.symm.trans he)
        have hj : j = i := by apply Fin.ext; dsimp [oddPluckerEdge] at hv; omega
        exact hji hj
      simp [hne]
    · simp
  · rw [if_neg h]
    apply Finset.sum_eq_zero
    intro i _
    have hne : a ≠ oddPluckerEdge k l i := by
      intro he
      apply h
      rw [he]
      dsimp [oddPluckerEdge]
      constructor <;> omega
    simp [hne]

/-- The two anti-diagonals become the literal Section 4 path coefficients,
including their signs. -/
theorem formMatrix_pathChain_upper (k : ℕ) (l : Fin 2)
    (a : StrictPairs (2*k+1)) :
    formMatrix (R := K) (if l = 0 then 2*k+1 else 2*k)
      (pathChainEquiv k a.val.1) (pathChainEquiv k a.val.2) =
        sectionFourPluckerForms k l a := by
  have ha := a.property
  have hi := a.val.1.isLt
  have hj := a.val.2.isLt
  change a.val.1.val < a.val.2.val at ha
  fin_cases l
  · change formMatrix (R := K) (2*k+1)
      (pathChainEquiv k a.val.1) (pathChainEquiv k a.val.2) = oddPluckerForms k 1 a
    rw [oddPluckerForms_edge_value]
    simp only [Fin.val_one, pathChainEquiv, Equiv.coe_fn_mk, formMatrix, pathToChain]
    split_ifs <;> (try simp_all only [Fin.val_mk, Fin.mk_lt_mk, neg_zero, neg_neg, true_and, not_true_eq_false]) <;> omega
  · change formMatrix (R := K) (2*k)
      (pathChainEquiv k a.val.1) (pathChainEquiv k a.val.2) = -oddPluckerForms k 0 a
    rw [oddPluckerForms_edge_value]
    simp only [Fin.val_zero, pathChainEquiv, Equiv.coe_fn_mk, formMatrix, pathToChain]
    split_ifs <;> (try simp_all only [Fin.val_mk, Fin.mk_lt_mk, neg_zero, neg_neg, true_and, not_true_eq_false]) <;> omega

/-- Both actual exterior forms are carried to the chain coordinates. -/
theorem sectionFour_forms_pathChain (k : ℕ) (l : Fin 2) :
    exteriorPower.map 2 (pathChainLinearEquiv (K := K) k).toLinearMap
      (twoFormOfCoefficients (sectionFourPluckerForms k l) (Pi.basisFun K (Fin (2*k+1)))) =
        twoFormOfCoefficients (canonicalForms (2*k+1) (2*k) l)
          (Pi.basisFun K (Fin (2*k+1))) := by
  apply orbitExteriorCoefficientMatrix_injective
  funext u v
  obtain ⟨i, rfl⟩ := (pathChainEquiv k).surjective u
  obtain ⟨j, rfl⟩ := (pathChainEquiv k).surjective v
  rw [orbitExteriorCoefficient_pathChain]
  change _ = orbitExteriorCoefficientMatrix
    (twoFormOfCoefficients (canonicalCoefficient (if l = 0 then 2*k+1 else 2*k))
      (Pi.basisFun K (Fin (2*k+1)))) _ _
  rw [coefficientMatrix_canonicalCoefficient]
  rcases lt_trichotomy i j with h | rfl | h
  · rw [coefficientMatrix_twoForm_upper _ i j h]
    exact (formMatrix_pathChain_upper k l ⟨(i,j),h⟩).symm
  · rw [orbitExteriorCoefficientMatrix_diagonal, formMatrix_self]
  · rw [orbitExteriorCoefficientMatrix_skew, coefficientMatrix_twoForm_upper _ j i h,
      formMatrix_swap]
    exact congrArg Neg.neg (formMatrix_pathChain_upper k l ⟨(j,i),h⟩).symm

variable [CharZero K]

/-- The attracting-coordinate scheme is isomorphic to the paper's actual
Section 4 scheme, through the displayed linear change of basis. -/
def chainSectionFourIso (k t : ℕ) :
    Proj (isotropicProjectiveGrading (t := t)
      (canonicalForms (K := K) (n := 2*k+1) (2*k+1) (2*k))) ≅
      Proj (isotropicProjectiveGrading (t := t) (sectionFourPluckerForms (K := K) k)) :=
  isotropicProjLinearIso (pathChainLinearEquiv k) (sectionFourPluckerForms k)
    (canonicalForms (2*k+1) (2*k)) (sectionFour_forms_pathChain k)

theorem chainSectionFourIso_hom_over (k t : ℕ) :
    (chainSectionFourIso (K := K) k t).hom ≫
      isotropicStructureMap (sectionFourPluckerForms k) =
        isotropicStructureMap (canonicalForms (2*k+1) (2*k)) :=
  isotropicProjLinearIso_hom_over _ _ _ _

/-- Actual smoothness of the ambient scheme used by the affine paving. -/
theorem chainCanonical_isotropicStructureMap_smooth (k t : ℕ) :
    Smooth (isotropicStructureMap (t := t)
      (canonicalForms (K := K) (n := 2*k+1) (2*k+1) (2*k))) := by
  have hpath : Smooth (isotropicStructureMap (t := t) (sectionFourPluckerForms (K := K) k)) :=
    (isotropicStructureMap_smooth_of_ideal_eq _ _ (sectionFour_isotropicPluckerIdeal k t)).mpr
      (canonicalOdd_isotropicStructureMap_smooth k t)
  exact (isotropicStructureMap_smooth_linearEquiv (t := t) (pathChainLinearEquiv k)
    (sectionFourPluckerForms k) (canonicalForms (2*k+1) (2*k))
    (sectionFour_forms_pathChain k)).mp hpath

end PaperVerification.IsotropicAttractingCharts
end
end
end ComponentSource_21

run_cmd Lean.logInfo "COMPONENT_SOURCE_END: PaperVerification.IsotropicAttractingCanonicalComparison"

section ComponentSource_22
/- Original module: PaperVerification.ProjectiveIrreducible -/


/-!
# Irreducibility of the actual projective spectrum of a domain

The homogeneous zero prime is an actual generic point. This gives the
irreducibility needed by the intrinsic complex-manifold construction,
without replacing the projective scheme by its affine coordinate model.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace PaperVerification.AlternatingForms

open AlgebraicGeometry CategoryTheory

universe u

variable {A σ : Type u} [CommRing A] [IsDomain A]
  [SetLike σ A] [AddSubgroupClass σ A]
  (𝒜 : ℕ → σ) [GradedRing 𝒜]

/-- A nonempty `Proj` of a domain has a dense generic point. -/
theorem projective_irreducibleSpace_of_domain [Nonempty (Proj 𝒜)] :
    IrreducibleSpace (Proj 𝒜) := by
  letI : Nonempty (ProjectiveSpectrum 𝒜) := by
    change Nonempty (Proj 𝒜)
    infer_instance
  let x : ProjectiveSpectrum 𝒜 := Classical.choice inferInstance
  let η : ProjectiveSpectrum 𝒜 := {
    asHomogeneousIdeal := ⊥
    isPrime := by simpa only [HomogeneousIdeal.toIdeal_bot] using
      (inferInstance : (⊥ : Ideal A).IsPrime)
    not_irrelevant_le := fun hi => x.not_irrelevant_le (hi.trans bot_le) }
  have hη : closure ({η} : Set (ProjectiveSpectrum 𝒜)) = Set.univ := by
    rw [← ProjectiveSpectrum.zeroLocus_vanishingIdeal_eq_closure,
      ProjectiveSpectrum.vanishingIdeal_singleton]
    change ProjectiveSpectrum.zeroLocus 𝒜 ((⊥ : Ideal A) : Set A) = Set.univ
    exact ProjectiveSpectrum.zeroLocus_bot 𝒜
  apply (irreducibleSpace_def _).mpr
  change IsIrreducible (Set.univ : Set (ProjectiveSpectrum 𝒜))
  rw [← hη]
  exact isIrreducible_singleton.closure

variable {K : Type} [Field K] [CharZero K]

/-- Prime degeneration and the actual coordinate-plane witness establish
irreducibility in the complete odd-dimensional range. -/
theorem canonicalOdd_isotropicProj_irreducible (k t : ℕ) (hs : t+2 ≤ k+1) :
    IrreducibleSpace
      (Proj (isotropicProjectiveGrading (t := t) (oddPluckerForms (K := K) k))) := by
  letI := canonicalOdd_isotropicProj_nonempty (K := K) k t hs
  letI := odd_isotropicPluckerIdeal_isPrime (K := K) k t hs
  exact projective_irreducibleSpace_of_domain _

end PaperVerification.AlternatingForms
end
end
end ComponentSource_22

run_cmd Lean.logInfo "COMPONENT_SOURCE_END: PaperVerification.ProjectiveIrreducible"


set_option pp.explicit false
set_option pp.proofs false
set_option pp.deepTerms false
set_option maxHeartbeats 0

open Lean Elab Command in
run_cmd do
  let env := (← getEnv).setExporting false
  let opts ← getOptions
  if true && env.header.trustLevel != 0 then
    throwError "The final environment has nonzero kernel trust level"
  if Lean.debug.skipKernelTC.get opts then
    throwError "The final environment disabled kernel type checking"
  if Lean.Elab.inServer.get opts then
    throwError "The final environment unexpectedly uses server mode"
  let required : Array (Name × String) := #[
    (`PaperVerification.TriangularPolynomialCoordinates.triangularEquiv, "definition"),
    (`PaperVerification.TriangularPolynomialCoordinates.triangularQuotientEquiv, "definition"),
    (`PaperVerification.IsotropicAttractingCoordinates.attractingCoordinateRingEquiv, "definition"),
    (`PaperVerification.IsotropicAttractingCoordinates.isotropyIdeal_eq_top_of_not_independent, "theorem"),
    (`PaperVerification.IsotropicAttractingCharts.canonicalForms, "definition"),
    (`PaperVerification.IsotropicAttractingCharts.originalCellPolynomialEquiv, "definition"),
    (`PaperVerification.IsotropicAttractingCharts.normalizedFiltrationPolynomialEquiv, "definition"),
    (`PaperVerification.IsotropicAttractingCharts.filtrationScheme, "definition"),
    (`PaperVerification.IsotropicAttractingCharts.filtrationToOriginal, "definition"),
    (`PaperVerification.IsotropicAttractingCharts.filtrationInclusion, "definition"),
    (`PaperVerification.IsotropicAttractingCharts.filtrationChart, "definition"),
    (`PaperVerification.IsotropicAttractingCharts.filtrationChartIsoCell, "definition"),
    (`PaperVerification.IsotropicAttractingCharts.filtrationChartIsoAffine, "definition"),
    (`PaperVerification.IsotropicAttractingCharts.orderedFiltrationCellIsoAffine, "definition"),
    (`PaperVerification.IsotropicAttractingCharts.weightOrderedPivots, "definition"),
    (`PaperVerification.IsotropicAttractingCharts.pivotPrefix, "definition"),
    (`PaperVerification.IsotropicAttractingCharts.orderedComplement, "definition"),
    (`PaperVerification.IsotropicAttractingCharts.orderedCellClosedMap, "definition"),
    (`PaperVerification.IsotropicAttractingCharts.independentPluckerEquivCoordinateSubsets, "definition"),
    (`PaperVerification.IsotropicAttractingCharts.chainSectionFourIso, "definition"),
    (`PaperVerification.IsotropicAttractingCharts.earlyMinorIdeal_eq_negativeCoordinates, "theorem"),
    (`PaperVerification.IsotropicAttractingCharts.normalizedCellEvaluation_kernel, "theorem"),
    (`PaperVerification.IsotropicAttractingCharts.pivotPrefix_earlier, "theorem"),
    (`PaperVerification.IsotropicAttractingCharts.filtrationToOriginal_isClosedImmersion, "theorem"),
    (`PaperVerification.IsotropicAttractingCharts.filtrationInclusion_isClosedImmersion, "theorem"),
    (`PaperVerification.IsotropicAttractingCharts.filtrationToOriginal_range, "theorem"),
    (`PaperVerification.IsotropicAttractingCharts.filtrationChart_isEmpty_of_not_independent, "theorem"),
    (`PaperVerification.IsotropicAttractingCharts.filtration_image_zero, "theorem"),
    (`PaperVerification.IsotropicAttractingCharts.filtration_image_final, "theorem"),
    (`PaperVerification.IsotropicAttractingCharts.ordered_filtration_stratum, "theorem"),
    (`PaperVerification.IsotropicAttractingCharts.ordered_filtration_antitone, "theorem"),
    (`PaperVerification.IsotropicAttractingCharts.filtrationToOriginal_over, "theorem"),
    (`PaperVerification.IsotropicAttractingCharts.filtrationInclusion_over, "theorem"),
    (`PaperVerification.IsotropicAttractingCharts.filtrationChartIsoCell_hom_over, "theorem"),
    (`PaperVerification.IsotropicAttractingCharts.filtrationChartIsoAffine_hom_over, "theorem"),
    (`PaperVerification.IsotropicAttractingCharts.orderedFiltration_closed_open_complement, "theorem"),
    (`PaperVerification.IsotropicAttractingCharts.orderedComplement_mono, "theorem"),
    (`PaperVerification.IsotropicAttractingCharts.orderedComplement_zero, "theorem"),
    (`PaperVerification.IsotropicAttractingCharts.orderedComplement_final, "theorem"),
    (`PaperVerification.IsotropicAttractingCharts.orderedComplement_preimage, "theorem"),
    (`PaperVerification.IsotropicAttractingCharts.orderedCellClosedMap_isClosedImmersion, "theorem"),
    (`PaperVerification.IsotropicAttractingCharts.orderedCellClosedMap_comp_ι, "theorem"),
    (`PaperVerification.IsotropicAttractingCharts.card_independentPluckerIndices, "theorem"),
    (`PaperVerification.IsotropicAttractingCharts.sum_cellBudget, "theorem"),
    (`PaperVerification.IsotropicAttractingCharts.sectionFour_forms_pathChain, "theorem"),
    (`PaperVerification.IsotropicAttractingCharts.chainSectionFourIso_hom_over, "theorem"),
    (`PaperVerification.IsotropicAttractingCharts.chainCanonical_isotropicStructureMap_smooth, "theorem"),
    (`PaperVerification.range_projMap_of_surjective, "theorem"),
    (`PaperVerification.gradedProjMap_over_hom, "theorem"),
    (`PaperVerification.HomogeneousQuotientProjective.quotientProjMap_range, "theorem"),
    (`PaperVerification.HomogeneousQuotientProjective.quotientProjMap_over, "theorem"),
    (`PaperVerification.AlternatingForms.projective_irreducibleSpace_of_domain, "theorem"),
    (`PaperVerification.AlternatingForms.canonicalOdd_isotropicProj_irreducible, "theorem"),
    (`PaperVerification.IsotropicAttractingCharts.orderedOpenInclusion, "definition"),
    (`PaperVerification.IsotropicAttractingCharts.orderedOpenInclusion_isOpenImmersion, "theorem"),
    (`PaperVerification.IsotropicAttractingCharts.orderedOpenInclusion_comp_ι, "theorem"),
    (`PaperVerification.IsotropicAttractingCharts.orderedOpenInclusion_range, "theorem"),
    (`PaperVerification.IsotropicAttractingCharts.orderedCellClosedMap_range, "theorem")
  ]
  let localNames := env.checked.get.constants.foldStage2 (fun acc name _ => acc.push name) (#[] : Array Name)
  if localNames.isEmpty then throwError "Empty authored declaration audit"
  let mut names := localNames
  for (name, _) in required do
    unless names.contains name do names := names.push name
  let mut rows : Array Json := #[]
  for name in names do
    let some info := env.checked.get.find? name | throwError "Missing checked declaration {name}"
    let kind := match info with
      | .thmInfo _ => "theorem"
      | .defnInfo _ => "definition"
      | .opaqueInfo _ => "opaque"
      | .axiomInfo _ => "axiom"
      | .inductInfo _ => "inductive"
      | .ctorInfo _ => "constructor"
      | .recInfo _ => "recursor"
      | .quotInfo _ => "quotient primitive"
    if kind == "axiom" then throwError "Authored axiom {name}"
    let value := info.value? (allowOpaque := true)
    if kind == "theorem" || kind == "definition" || kind == "opaque" then
      unless value.isSome do throwError "No actual body {name}"
    for (requiredName, expectedKind) in required do
      if name == requiredName && kind != expectedKind then
        throwError "Endpoint kind mismatch {name}: expected {expectedKind}, got {kind}"
    let axioms ← collectAxioms name
    for ax in axioms do
      if ax != ``propext && ax != ``Classical.choice && ax != ``Quot.sound then
        throwError "Unapproved transitive axiom {name}: {ax}"
    let mut fields := [("name", toJson name.toString), ("kind", toJson kind),
      ("actual_body_available", toJson value.isSome),
      ("universe_parameters", toJson (info.levelParams.map Name.toString)),
      ("type_dependencies", toJson (info.type.getUsedConstants.map Name.toString)),
      ("body_dependencies", toJson ((value.map Expr.getUsedConstants).getD #[] |>.map Name.toString)),
      ("transitive_axioms", toJson (axioms.map Name.toString))]
    if required.any (fun e => e.1 == name) then
      let typeText ← liftTermElabM <| return (← Meta.ppExpr info.type).pretty
      fields := fields ++ [("readable_type", toJson typeText)]
    rows := rows.push (Json.mkObj fields)
  IO.FS.createDirAll ".lake/reports"
  let path := ".lake/reports/" ++ (← getEnv).mainModule.toString ++ ".json"
  IO.FS.writeFile path (Json.mkObj [("accepted", toJson true),
    ("nonce", toJson "900c6b17770fbf1ab6a4ac6bd8274895"), ("declaration_count", toJson localNames.size),
    ("kernel_trust_level", toJson env.header.trustLevel.toNat),
    ("kernel_type_checking_enabled", toJson (!Lean.debug.skipKernelTC.get opts)),
    ("server_mode", toJson (Lean.Elab.inServer.get opts)),
    ("required_endpoint_count", toJson required.size),
    ("all_new_declarations_read_from_checked_environment", toJson true),
    ("declarations", toJson rows)]).pretty
  logInfo "LITERAL_COMPONENT_KERNEL_AUDIT_COMPLETE:900c6b17770fbf1ab6a4ac6bd8274895"
