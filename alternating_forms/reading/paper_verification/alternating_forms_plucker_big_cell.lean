module

public import PaperVerification.AlternatingFormsUniversalMinors

/-!
# The actual affine big cell in the maximal-minor presentation

Fixing a nonzero Plücker coordinate to one gives the polynomial ring in the
nonpivot entries of the unique row-reduced matrix. Both algebra maps are
explicit: maximal minors in one direction, signed replacement minors in the
other. The inverse identity follows from the universal Cramer identities.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
open scoped BigOperators
open MvPolynomial Matrix

namespace PaperVerification.AlternatingForms

variable {K : Type*} [Field K] {s n : ℕ}

abbrev PluckerChartVariable (p : PluckerIndex s n) :=
  Fin s × {j : Fin n // j ∉ Set.range p.val}

/-- The literal row-reduced matrix in a Plücker chart. -/
def pluckerChartMatrix (p : PluckerIndex s n) :
    Matrix (Fin s) (Fin n) (MvPolynomial (PluckerChartVariable p) K) :=
  Matrix.of fun i j => if j=p.val i then 1 else if h : j ∈ Set.range p.val then 0
    else X (i,⟨j,h⟩)

theorem pluckerChartMatrix_pivot (p : PluckerIndex s n) :
    Matrix.of (fun i j : Fin s => pluckerChartMatrix (K := K) p i (p.val j)) =
      (1 : Matrix (Fin s) (Fin s) (MvPolynomial (PluckerChartVariable p) K)) := by
  classical
  apply Matrix.ext
  intro i j
  by_cases hij : i = j
  · subst j
    simp [pluckerChartMatrix,Matrix.of_apply,Matrix.one_apply]
  · have hji : p.val j ≠ p.val i := fun h => hij (p.property.injective h).symm
    have hj : p.val j ∈ Set.range p.val := ⟨j,rfl⟩
    simp [pluckerChartMatrix,Matrix.of_apply,Matrix.one_apply,hij,hji,hj]

theorem pluckerChartMatrix_nonpivot (p : PluckerIndex s n)
    (i : Fin s) (j : {j : Fin n // j ∉ Set.range p.val}) :
    pluckerChartMatrix (K := K) p i j.val = X (i,j) := by
  classical
  have hne : j.val≠p.val i := fun h => j.property ⟨i,h.symm⟩
  simp only [pluckerChartMatrix, Matrix.of_apply, if_neg hne, dif_neg j.property]

def pluckerBigCellIdeal (p : PluckerIndex s n) :
    Ideal (MvPolynomial (PluckerIndex s n) K) :=
  matrixPluckerIdeal ⊔ Ideal.span {X p-1}

abbrev PluckerBigCell (p : PluckerIndex s n) :=
  MvPolynomial (PluckerIndex s n) K ⧸ pluckerBigCellIdeal p

def pluckerBigCellClass (p : PluckerIndex s n) :
    MvPolynomial (PluckerIndex s n) K →ₐ[K] PluckerBigCell (K := K) p :=
  Ideal.Quotient.mkₐ K _

theorem pluckerBigCellClass_pivot (p : PluckerIndex s n) :
    pluckerBigCellClass (K := K) p (X p)=1 := by
  have hincl : Ideal.span ({X p-1} : Set (MvPolynomial (PluckerIndex s n) K)) ≤
      pluckerBigCellIdeal (K := K) p := le_sup_right
  have h : X p-1 ∈ pluckerBigCellIdeal (K := K) p :=
    hincl (Ideal.subset_span (Set.mem_singleton _))
  exact (Ideal.Quotient.mk_eq_mk_iff_sub_mem (X p) 1).mpr h

theorem pluckerBigCellClass_cramer_pivot (p : PluckerIndex s n) (i j : Fin s) :
    pluckerBigCellClass (K := K) p (cramerPluckerCoordinate p i (p.val j)) =
      (1 : Matrix (Fin s) (Fin s) (PluckerBigCell (K := K) p)) i j := by
  have h := (Ideal.Quotient.mk_eq_mk_iff_sub_mem
    (cramerPluckerCoordinate (K := K) p i (p.val j)) (if i=j then X p else 0)).mpr
      ((show matrixPluckerIdeal (K := K) ≤ pluckerBigCellIdeal p from le_sup_left)
        (cramerPlucker_pivot_relation (K := K) p i j))
  change pluckerBigCellClass p (cramerPluckerCoordinate p i (p.val j)) =
    pluckerBigCellClass p (if i=j then X p else 0) at h
  simpa only [apply_ite,map_zero,pluckerBigCellClass_pivot,Matrix.one_apply] using h

theorem pluckerBigCellClass_cramer_minor (p I : PluckerIndex s n) :
    Matrix.det (Matrix.of fun i j : Fin s =>
      pluckerBigCellClass (K := K) p (cramerPluckerCoordinate p i (I.val j))) =
      pluckerBigCellClass p (X I) := by
  have h := (Ideal.Quotient.mk_eq_mk_iff_sub_mem
    (Matrix.det (Matrix.of fun i j : Fin s => cramerPluckerCoordinate (K := K) p i (I.val j)))
    ((X p)^(s-1)*X I)).mpr
      ((show matrixPluckerIdeal (K := K) ≤ pluckerBigCellIdeal p from le_sup_left)
        (cramerPlucker_minor_relation (K := K) p I))
  change pluckerBigCellClass p _ = pluckerBigCellClass p _ at h
  rw [AlgHom.map_det,map_mul,map_pow,pluckerBigCellClass_pivot,one_pow,one_mul] at h
  have hm : (pluckerBigCellClass (K := K) p).mapMatrix
      (Matrix.of fun i j : Fin s => cramerPluckerCoordinate p i (I.val j)) =
      Matrix.of (fun i j : Fin s =>
        pluckerBigCellClass p (cramerPluckerCoordinate p i (I.val j))) := by
    apply Matrix.ext
    intro i j
    rfl
  rw [hm] at h
  exact h

theorem pluckerBigCellIdeal_le_chartKernel (p : PluckerIndex s n) :
    pluckerBigCellIdeal (K := K) p ≤
      RingHom.ker (matrixMinorEvaluation (K := K) (pluckerChartMatrix (K := K) p)).toRingHom := by
  apply sup_le
  · exact matrixPluckerIdeal_le_matrixMinorKernel _
  · apply Ideal.span_le.mpr
    intro q hq
    obtain rfl := Set.mem_singleton_iff.mp hq
    change matrixMinorEvaluation (K := K) (pluckerChartMatrix (K := K) p) (X p-1)=0
    simp only [map_sub,map_one,matrixMinorEvaluation,aeval_X,pluckerChartMatrix_pivot,
      Matrix.det_one,sub_self]

/-- The forward chart map sends each actual Plücker coordinate to its minor. -/
def pluckerBigCellToMatrix (p : PluckerIndex s n) :
    PluckerBigCell (K := K) p →ₐ[K] MvPolynomial (PluckerChartVariable p) K :=
  Ideal.Quotient.liftₐ _ (matrixMinorEvaluation (pluckerChartMatrix p))
    (fun q hq => pluckerBigCellIdeal_le_chartKernel p hq)

/-- The inverse chart map uses the actual signed replacement minors. -/
def pluckerMatrixToBigCell (p : PluckerIndex s n) :
    MvPolynomial (PluckerChartVariable p) K →ₐ[K] PluckerBigCell (K := K) p :=
  aeval fun a => pluckerBigCellClass p (cramerPluckerCoordinate p a.1 a.2.val)

theorem pluckerBigCellToMatrix_class (p : PluckerIndex s n)
    (q : MvPolynomial (PluckerIndex s n) K) :
    pluckerBigCellToMatrix p (pluckerBigCellClass p q) =
      matrixMinorEvaluation (pluckerChartMatrix p) q := rfl

theorem pluckerMatrixToBigCell_entry (p : PluckerIndex s n) (i : Fin s) (j : Fin n) :
    pluckerMatrixToBigCell (K := K) p (pluckerChartMatrix p i j) =
      pluckerBigCellClass p (cramerPluckerCoordinate p i j) := by
  classical
  by_cases hj : j∈Set.range p.val
  · obtain ⟨k,rfl⟩ := hj
    have he := congrArg
      (fun M : Matrix (Fin s) (Fin s) (MvPolynomial (PluckerChartVariable p) K) => M i k)
      (pluckerChartMatrix_pivot (K := K) p)
    change pluckerChartMatrix (K := K) p i (p.val k) =
      (1 : Matrix (Fin s) (Fin s) (MvPolynomial (PluckerChartVariable p) K)) i k at he
    rw [he,pluckerBigCellClass_cramer_pivot]
    simp only [Matrix.one_apply,apply_ite,map_one,map_zero]
    split_ifs <;> rfl
  · rw [pluckerChartMatrix_nonpivot p i ⟨j,hj⟩]
    simp only [pluckerMatrixToBigCell,aeval_X]

theorem pluckerBigCellToMatrix_leftInverse (p : PluckerIndex s n) :
    (pluckerMatrixToBigCell (K := K) p).comp (pluckerBigCellToMatrix p) =
      AlgHom.id K (PluckerBigCell (K := K) p) := by
  apply Ideal.Quotient.algHom_ext
  apply MvPolynomial.algHom_ext
  intro I
  change pluckerMatrixToBigCell p
    (pluckerBigCellToMatrix p (pluckerBigCellClass p (X I))) =
      pluckerBigCellClass p (X I)
  rw [pluckerBigCellToMatrix_class,matrixMinorEvaluation,aeval_X,AlgHom.map_det]
  have he : (pluckerMatrixToBigCell p).mapMatrix
      (Matrix.of fun i j : Fin s => pluckerChartMatrix (K := K) p i (I.val j)) =
      Matrix.of (fun i j : Fin s => pluckerBigCellClass p
        (cramerPluckerCoordinate p i (I.val j))) := by
    ext i j
    exact pluckerMatrixToBigCell_entry p i (I.val j)
  rw [he]
  exact pluckerBigCellClass_cramer_minor p I

theorem pluckerBigCellToMatrix_rightInverse (p : PluckerIndex s n) :
    (pluckerBigCellToMatrix (K := K) p).comp (pluckerMatrixToBigCell p) =
      AlgHom.id K (MvPolynomial (PluckerChartVariable p) K) := by
  apply MvPolynomial.algHom_ext
  intro a
  change pluckerBigCellToMatrix p (pluckerMatrixToBigCell p (X a))=X a
  rw [pluckerMatrixToBigCell,aeval_X,pluckerBigCellToMatrix_class,
    matrixMinorEvaluation_cramer,pluckerChartMatrix_pivot,Matrix.cramer_one]
  change pluckerChartMatrix p a.1 a.2.val = X a
  exact pluckerChartMatrix_nonpivot p a.1 a.2

/-- A literal affine-coordinate-ring isomorphism for every maximal-minor big
cell, over the original field and with all sizes retained. -/
def pluckerBigCellEquiv (p : PluckerIndex s n) :
    PluckerBigCell (K := K) p ≃ₐ[K] MvPolynomial (PluckerChartVariable p) K :=
  AlgEquiv.ofAlgHom (pluckerBigCellToMatrix p) (pluckerMatrixToBigCell p)
    (pluckerBigCellToMatrix_rightInverse p) (pluckerBigCellToMatrix_leftInverse p)

theorem pluckerBigCellEquiv_coordinate (p I : PluckerIndex s n) :
    pluckerBigCellEquiv (K := K) p (pluckerBigCellClass p (X I)) =
      Matrix.det (Matrix.of fun i j : Fin s => pluckerChartMatrix p i (I.val j)) := by
  change matrixMinorEvaluation (pluckerChartMatrix p) (X I)=_
  simp only [matrixMinorEvaluation,aeval_X]

end PaperVerification.AlternatingForms
