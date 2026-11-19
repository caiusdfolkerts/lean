module

public import PaperVerification.AlternatingFormsOddAffineCompletion

/-!
# A polynomial coordinate ring for the odd common-isotropic big cell

The nonpivot entries outside the head columns are free coordinates.
The constant-block completion constructs the other entries as actual
polynomials in these coordinates.  The resulting two algebra maps are
proved inverse using uniqueness over arbitrary coefficient algebras.
Thus the displayed chart ring is a polynomial algebra, without reduction,
localization at an additional determinant, or a smoothness assumption.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

namespace PaperVerification.AlternatingForms

open MvPolynomial

variable {K : Type*} [Field K]

abbrev OddAffineFreeVariable (k r : ℕ) (h : r ≤ k) :=
  {a : PluckerChartVariable (oddAffinePivot k r h) //
    ¬oddAffineIsHead r a.2.val}

def oddAffineFreeAssignment (k r : ℕ) (h : r ≤ k)
    (a : PluckerChartVariable (oddAffinePivot k r h)) :
    MvPolynomial (OddAffineFreeVariable k r h) K :=
  if ha : ¬oddAffineIsHead r a.2.val then X ⟨a,ha⟩ else 0

def oddAffineFreeEvaluation (k r : ℕ) (h : r ≤ k) :
    MvPolynomial (PluckerChartVariable (oddAffinePivot k r h)) K →ₐ[K]
      MvPolynomial (OddAffineFreeVariable k r h) K :=
  aeval (oddAffineFreeAssignment k r h)

def oddAffineFreeMatrix (k r : ℕ) (h : r ≤ k) :
    Matrix (Fin (r+1)) (Fin (2*k+1))
      (MvPolynomial (OddAffineFreeVariable k r h) K) :=
  (pluckerChartMatrix (K := K) (oddAffinePivot k r h)).map
    (oddAffineFreeEvaluation (K := K) k r h)

theorem oddAffineFreeMatrix_pivot (k r : ℕ) (h : r ≤ k) :
    (oddAffineFreeMatrix (K := K) k r h).submatrix id (oddAffinePivot k r h).val = 1 := by
  apply Matrix.ext
  intro i j
  change oddAffineFreeEvaluation (K := K) k r h
      (pluckerChartMatrix (K := K) (oddAffinePivot k r h) i
        ((oddAffinePivot k r h).val j)) = _
  have hp := congrArg
    (fun B : Matrix (Fin (r+1)) (Fin (r+1))
      (MvPolynomial (PluckerChartVariable (oddAffinePivot k r h)) K) => B i j)
    (pluckerChartMatrix_pivot (K := K) (oddAffinePivot k r h))
  simp only [Matrix.of_apply] at hp
  rw [hp]
  simp only [Matrix.one_apply, apply_ite, map_one, map_zero]
  split_ifs <;> rfl

theorem oddAffineFreeMatrix_free (k r : ℕ) (h : r ≤ k)
    (a : OddAffineFreeVariable k r h) :
    oddAffineFreeMatrix (K := K) k r h a.val.1 a.val.2.val = X a := by
  change oddAffineFreeEvaluation (K := K) k r h
      (pluckerChartMatrix (K := K) (oddAffinePivot k r h) a.val.1 a.val.2.val) = _
  rw [pluckerChartMatrix_nonpivot]
  simp only [oddAffineFreeEvaluation, aeval_X, oddAffineFreeAssignment, dif_pos a.property]

theorem oddAffine_head_not_pivot (k r : ℕ) (h : r ≤ k) (j : Fin (2*k+1))
    (hj : oddAffineIsHead r j) : j ∉ Set.range (oddAffinePivot k r h).val := by
  rintro ⟨i,hi⟩
  have hv := congrArg Fin.val hi
  dsimp [oddAffinePivot] at hv
  have := hj.1
  omega

theorem oddAffineFreeMatrix_head (k r : ℕ) (h : r ≤ k)
    (i : Fin (r+1)) (j : Fin (2*k+1)) (hj : oddAffineIsHead r j) :
    oddAffineFreeMatrix (K := K) k r h i j = 0 := by
  have hnp := oddAffine_head_not_pivot k r h j hj
  change oddAffineFreeEvaluation (K := K) k r h
    (pluckerChartMatrix (K := K) (oddAffinePivot k r h) i j) = 0
  rw [pluckerChartMatrix_nonpivot (oddAffinePivot k r h) i ⟨j,hnp⟩]
  simp only [oddAffineFreeEvaluation, aeval_X, oddAffineFreeAssignment,
    dif_neg (not_not.mpr hj)]

/-- An actual polynomial family of normalized common-isotropic matrices. -/
def oddAffineParamMatrix (k r : ℕ) (h : r ≤ k) :
    Matrix (Fin (r+1)) (Fin (2*k+1))
      (MvPolynomial (OddAffineFreeVariable k r h) K) :=
  oddAffineCompletion (K := K) (oddAffineFreeMatrix k r h)

theorem oddAffineParamMatrix_pivot (k r : ℕ) (h : r ≤ k) :
    (oddAffineParamMatrix (K := K) k r h).submatrix id (oddAffinePivot k r h).val = 1 :=
  oddAffineCompletion_pivot h _ (oddAffineFreeMatrix_pivot k r h)

theorem oddAffineParamMatrix_free (k r : ℕ) (h : r ≤ k)
    (a : OddAffineFreeVariable k r h) :
    oddAffineParamMatrix (K := K) k r h a.val.1 a.val.2.val = X a := by
  rw [oddAffineParamMatrix,
    oddAffineCompletion_off_head _ _ _ a.property, oddAffineFreeMatrix_free]

def oddAffineParamPoint (k t : ℕ) (h : t+1 ≤ k) :
    IsotropicChartPoint (oddAffinePivot k (t+1) h) (oddPluckerForms (K := K) k)
      (MvPolynomial (OddAffineFreeVariable k (t+1) h) K) where
  matrix := oddAffineParamMatrix k (t+1) h
  pivot := oddAffineParamMatrix_pivot k (t+1) h
  isotropic := by
    intro l i j
    fin_cases l
    · exact (oddMatrixFirstPair_eq (K := K) (oddAffineParamMatrix (K := K) k (t+1) h) i j).trans
        (oddAffineCompletion_first h _ (oddAffineFreeMatrix_pivot k (t+1) h) i j)
    · exact (oddMatrixSecondPair_eq (K := K) (oddAffineParamMatrix (K := K) k (t+1) h) i j).trans
        (oddAffineCompletion_second h _ (oddAffineFreeMatrix_pivot k (t+1) h) i j)

/-- On this actual chart, the free entries determine an isotropic point
over every commutative `K`-algebra. -/
theorem oddAffineChartPoint_ext_free
    {R : Type*} [CommRing R] [Algebra K R] (k t : ℕ) (h : t+1 ≤ k)
    (A B : IsotropicChartPoint (oddAffinePivot k (t+1) h)
      (oddPluckerForms (K := K) k) R)
    (hfree : ∀ a : OddAffineFreeVariable k (t+1) h,
      A.matrix a.val.1 a.val.2.val = B.matrix a.val.1 a.val.2.val) : A = B := by
  apply IsotropicChartPoint.ext_matrix
  apply oddAffine_isotropic_ext (K := K) h A.matrix B.matrix B.pivot
  · intro i j
    exact (oddMatrixFirstPair_eq (K := K) A.matrix i j).symm.trans
      (A.isotropic 0 i j)
  · intro i j
    exact (oddMatrixSecondPair_eq (K := K) A.matrix i j).symm.trans
      (A.isotropic 1 i j)
  · intro i j
    exact (oddMatrixFirstPair_eq (K := K) B.matrix i j).symm.trans
      (B.isotropic 0 i j)
  · intro i j
    exact (oddMatrixSecondPair_eq (K := K) B.matrix i j).symm.trans
      (B.isotropic 1 i j)
  · intro i j hj
    by_cases hp : j ∈ Set.range (oddAffinePivot k (t+1) h).val
    · obtain ⟨a,rfl⟩ := hp
      have hA := congrArg (fun C : Matrix (Fin (t+2)) (Fin (t+2)) R => C i a) A.pivot
      have hB := congrArg (fun C : Matrix (Fin (t+2)) (Fin (t+2)) R => C i a) B.pivot
      exact hA.trans hB.symm
    · exact hfree ⟨(i,⟨j,hp⟩),hj⟩

def oddAffineChartToPolynomial (k t : ℕ) (h : t+1 ≤ k) :
    IsotropicChartRing (oddAffinePivot k (t+1) h) (oddPluckerForms (K := K) k) →ₐ[K]
      MvPolynomial (OddAffineFreeVariable k (t+1) h) K :=
  (oddAffineParamPoint k t h).toAlgHom

def oddAffinePolynomialToChart (k t : ℕ) (h : t+1 ≤ k) :
    MvPolynomial (OddAffineFreeVariable k (t+1) h) K →ₐ[K]
      IsotropicChartRing (oddAffinePivot k (t+1) h) (oddPluckerForms (K := K) k) :=
  aeval (fun a => Ideal.Quotient.mk _ (X a.val))

theorem oddAffineChartToPolynomial_free (k t : ℕ) (h : t+1 ≤ k)
    (a : OddAffineFreeVariable k (t+1) h) :
    oddAffineChartToPolynomial (K := K) k t h (Ideal.Quotient.mk _ (X a.val)) = X a := by
  rw [← pluckerChartMatrix_nonpivot (oddAffinePivot k (t+1) h) a.val.1 a.val.2]
  change (oddAffineParamPoint (K := K) k t h).toAlgHom (Ideal.Quotient.mk _ _) = _
  rw [IsotropicChartPoint.toAlgHom_entry]
  exact oddAffineParamMatrix_free k (t+1) h a

theorem oddAffineChartToPolynomial_rightInverse (k t : ℕ) (h : t+1 ≤ k) :
    (oddAffineChartToPolynomial (K := K) k t h).comp (oddAffinePolynomialToChart k t h) =
      AlgHom.id K (MvPolynomial (OddAffineFreeVariable k (t+1) h) K) := by
  apply MvPolynomial.algHom_ext
  intro a
  change oddAffineChartToPolynomial k t h (oddAffinePolynomialToChart k t h (X a)) = X a
  rw [oddAffinePolynomialToChart, aeval_X, oddAffineChartToPolynomial_free]

theorem oddAffineChartToPolynomial_leftInverse (k t : ℕ) (h : t+1 ≤ k) :
    (oddAffinePolynomialToChart (K := K) k t h).comp (oddAffineChartToPolynomial k t h) =
      AlgHom.id K (IsotropicChartRing (oddAffinePivot k (t+1) h) (oddPluckerForms k)) := by
  apply (isotropicChartPointEquiv (oddAffinePivot k (t+1) h) (oddPluckerForms k)).injective
  apply oddAffineChartPoint_ext_free k t h
  intro a
  change oddAffinePolynomialToChart k t h
      (oddAffineChartToPolynomial k t h
        (Ideal.Quotient.mk _ (pluckerChartMatrix (oddAffinePivot k (t+1) h)
          a.val.1 a.val.2.val))) =
      Ideal.Quotient.mk _ (pluckerChartMatrix (oddAffinePivot k (t+1) h)
        a.val.1 a.val.2.val)
  rw [pluckerChartMatrix_nonpivot, oddAffineChartToPolynomial_free]
  simp only [oddAffinePolynomialToChart, aeval_X]

/-- The original row-isotropy quotient is a polynomial algebra in the
remaining nonpivot entries.  Both maps above have their literal meanings. -/
def oddAffineChartEquiv (k t : ℕ) (h : t+1 ≤ k) :
    IsotropicChartRing (oddAffinePivot k (t+1) h) (oddPluckerForms (K := K) k) ≃ₐ[K]
      MvPolynomial (OddAffineFreeVariable k (t+1) h) K :=
  AlgEquiv.ofAlgHom (oddAffineChartToPolynomial k t h) (oddAffinePolynomialToChart k t h)
    (oddAffineChartToPolynomial_rightInverse k t h) (oddAffineChartToPolynomial_leftInverse k t h)

end PaperVerification.AlternatingForms
