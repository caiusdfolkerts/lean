module

public import PaperVerification.AlternatingFormsPluckerBigCell
public import PaperVerification.AlternatingFormsChart
public import PaperVerification.AlternatingFormsDeterminantPairExpansion

/-!
# Linear isotropy equations on the actual Plücker big cell

An alternating form is recorded by its coefficients on increasing pairs.
The Plücker equation is the signed coordinate expression for its wedge with
an arbitrary coordinate word. Evaluating it on a matrix with isotropic rows
is proved by the determinant expansion, retaining every row-pair equation.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
open scoped BigOperators
open MvPolynomial Matrix

namespace PaperVerification.AlternatingForms

variable {K : Type*} [Field K] {t n m : ℕ}

/-- Evaluation of the alternating form with the displayed independent coefficients. -/
def alternatingRowPair {R : Type*} [CommRing R] [Algebra K R]
    (f : StrictPairs n → K) (A : Matrix (Fin (t+2)) (Fin n) R)
    (i j : Fin (t+2)) : R :=
  ∑ a : StrictPairs n, f a •
    (A i a.val.1*A j a.val.2 - A i a.val.2*A j a.val.1)

theorem alternatingRowPair_self {R : Type*} [CommRing R] [Algebra K R]
    (f : StrictPairs n → K) (A : Matrix (Fin (t+2)) (Fin n) R) (i : Fin (t+2)) :
    alternatingRowPair f A i i = 0 := by
  simp [alternatingRowPair,mul_comm]

theorem alternatingRowPair_swap {R : Type*} [CommRing R] [Algebra K R]
    (f : StrictPairs n → K) (A : Matrix (Fin (t+2)) (Fin n) R) (i j : Fin (t+2)) :
    alternatingRowPair f A j i = -alternatingRowPair f A i j := by
  rw [alternatingRowPair,alternatingRowPair,←Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro a ha
  rw [←smul_neg]
  congr 1
  ring

/-- The literal coefficient expression of `f ∧ z_J`. Repeated coordinates
are allowed in `J` and are handled by the alternating determinant. -/
def pluckerIsotropyEquation (f : StrictPairs n → K) (J : Fin t → Fin n) :
    MvPolynomial (PluckerIndex (t+2) n) K :=
  ∑ a : StrictPairs n, f a •
    orderedPluckerCoordinate (Fin.cons a.val.1 (Fin.cons a.val.2 J))

def determinantTail {R : Type*} [CommRing R]
    (A : Matrix (Fin (t+2)) (Fin n) R) (J : Fin t → Fin n)
    (σ : Equiv.Perm (Fin (t+2))) : R :=
  ∏ i : Fin t, A (σ i.succ.succ) (J i)

theorem determinant_two_columns {R : Type*} [CommRing R]
    (A : Matrix (Fin (t+2)) (Fin n) R) (a b : Fin n) (J : Fin t → Fin n) :
    Matrix.det (Matrix.of (fun i j : Fin (t+2) => A i ((Fin.cons a (Fin.cons b J) : Fin (t+2) → Fin n) j))) =
      ∑ σ : Equiv.Perm (Fin (t+2)), Equiv.Perm.sign σ •
        (A (σ 0) a * A (σ (Fin.succ 0)) b * determinantTail A J σ) := by
  simp only [Matrix.det_apply,Matrix.of_apply,Fin.prod_univ_succ,Fin.cons_zero,Fin.cons_succ,
    determinantTail,mul_assoc]

theorem determinant_two_columns_swap {R : Type*} [CommRing R]
    (A : Matrix (Fin (t+2)) (Fin n) R) (a b : Fin n) (J : Fin t → Fin n) :
    Matrix.det (Matrix.of (fun i j : Fin (t+2) => A i ((Fin.cons b (Fin.cons a J) : Fin (t+2) → Fin n) j))) =
      -Matrix.det (Matrix.of (fun i j : Fin (t+2) => A i ((Fin.cons a (Fin.cons b J) : Fin (t+2) → Fin n) j))) := by
  classical
  let σ : Equiv.Perm (Fin (t+2)) := Equiv.swap 0 (Fin.succ 0)
  have hne : (0 : Fin (t+2)) ≠ Fin.succ 0 := (Fin.succ_ne_zero 0).symm
  have he : (Matrix.of (fun i j : Fin (t+2) => A i ((Fin.cons a (Fin.cons b J) : Fin (t+2) → Fin n) j))).submatrix id σ =
      Matrix.of (fun i j : Fin (t+2) => A i ((Fin.cons b (Fin.cons a J) : Fin (t+2) → Fin n) j)) := by
    apply Matrix.ext
    intro i j
    refine Fin.cases ?_ (fun j => Fin.cases ?_ (fun k => ?_) j) j
    · simp [σ,Matrix.submatrix,Matrix.of_apply,hne]
    · simp [σ,Matrix.submatrix,Matrix.of_apply,hne]
    · have hk0 : k.succ.succ ≠ (0 : Fin (t+2)) := Fin.succ_ne_zero _
      have hk1 : k.succ.succ ≠ (Fin.succ 0 : Fin (t+2)) := by
        intro h
        exact Fin.succ_ne_zero k (Fin.succ_injective _ h)
      simp only [σ,Matrix.submatrix_apply,id_eq,Matrix.of_apply,
        Equiv.swap_apply_of_ne_of_ne hk0 hk1,Fin.cons_succ]
  have h := Matrix.det_permute' σ (Matrix.of (fun i j : Fin (t+2) => A i ((Fin.cons a (Fin.cons b J) : Fin (t+2) → Fin n) j)))
  rw [he] at h
  simpa only [σ,Equiv.Perm.sign_swap hne,Units.val_neg,Units.val_one,
    Int.cast_neg,Int.cast_one,neg_one_mul] using h

/-- Two times the wedge equation is a sum of the actual row-pair equations.
This is a determinant identity over every commutative algebra. -/
theorem twice_matrixMinorEvaluation_isotropy {R : Type*} [CommRing R] [Algebra K R]
    (f : StrictPairs n → K) (A : Matrix (Fin (t+2)) (Fin n) R) (J : Fin t → Fin n) :
    (2 : K) • matrixMinorEvaluation A (pluckerIsotropyEquation f J) =
      ∑ σ : Equiv.Perm (Fin (t+2)), Equiv.Perm.sign σ •
        (alternatingRowPair f A (σ 0) (σ (Fin.succ 0)) * determinantTail A J σ) := by
  classical
  have hpair (a : StrictPairs n) :
      (2 : K) • (f a • Matrix.det
        (Matrix.of (fun i j : Fin (t+2) => A i ((Fin.cons a.val.1 (Fin.cons a.val.2 J) : Fin (t+2) → Fin n) j)))) =
      f a • (Matrix.det (Matrix.of (fun i j : Fin (t+2) => A i ((Fin.cons a.val.1 (Fin.cons a.val.2 J) : Fin (t+2) → Fin n) j))) -
        Matrix.det (Matrix.of (fun i j : Fin (t+2) => A i ((Fin.cons a.val.2 (Fin.cons a.val.1 J) : Fin (t+2) → Fin n) j)))) := by
    rw [determinant_two_columns_swap A a.val.1 a.val.2 J]
    simp only [sub_neg_eq_add,smul_add,two_smul]
  simp only [pluckerIsotropyEquation,map_sum,map_smul,
    matrixMinorEvaluation_orderedCoordinate,Finset.smul_sum,hpair]
  simp_rw [determinant_two_columns,←Finset.sum_sub_distrib,Finset.smul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro σ hσ
  rw [alternatingRowPair,Finset.sum_mul,Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro a ha
  simp only [smul_sub,Units.smul_def,Algebra.smul_def,smul_eq_mul]
  ring

/-- Group determinant permutations into first-column transposition pairs.
This is the characteristic-free two-column expansion, with no division. -/
theorem determinant_two_columns_paired {R : Type*} [CommRing R]
    (A : Matrix (Fin (t+2)) (Fin n) R) (a b : Fin n) (J : Fin t → Fin n) :
    Matrix.det (Matrix.of (fun i j : Fin (t+2) => A i ((Fin.cons a (Fin.cons b J) : Fin (t+2) → Fin n) j))) =
      ∑ σ ∈ (Finset.univ.filter fun σ : Equiv.Perm (Fin (t+2)) =>
          σ 0 < σ (Fin.succ 0)), Equiv.Perm.sign σ •
        ((A (σ 0) a * A (σ (Fin.succ 0)) b -
          A (σ 0) b * A (σ (Fin.succ 0)) a) * determinantTail A J σ) := by
  simpa only [Matrix.of_apply, Fin.cons_zero, Fin.cons_succ, determinantTail] using
    determinant_pair_expansion (Matrix.of (fun i j : Fin (t+2) => A i ((Fin.cons a (Fin.cons b J) : Fin (t+2) → Fin n) j)))

/-- The actual wedge equation is an exact linear combination of the
row-pair equations over every commutative coefficient algebra. -/
theorem matrixMinorEvaluation_isotropy_rowPairs {R : Type*}
    [CommRing R] [Algebra K R]
    (f : StrictPairs n → K) (A : Matrix (Fin (t+2)) (Fin n) R) (J : Fin t → Fin n) :
    matrixMinorEvaluation A (pluckerIsotropyEquation f J) =
      ∑ σ ∈ (Finset.univ.filter fun σ : Equiv.Perm (Fin (t+2)) =>
          σ 0 < σ (Fin.succ 0)), Equiv.Perm.sign σ •
        (alternatingRowPair f A (σ 0) (σ (Fin.succ 0)) * determinantTail A J σ) := by
  classical
  simp only [pluckerIsotropyEquation, map_sum, map_smul,
    matrixMinorEvaluation_orderedCoordinate]
  simp_rw [determinant_two_columns_paired, Finset.smul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro σ hσ
  rw [alternatingRowPair, Finset.sum_mul, Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro a ha
  simp only [Units.smul_def, Algebra.smul_def, smul_eq_mul]
  ring

/-- Isotropic rows annihilate every actual linear Plücker isotropy equation
in every characteristic, including two. -/
theorem matrixMinorEvaluation_isotropy_eq_zero
    {R : Type*} [CommRing R] [Algebra K R]
    (f : StrictPairs n → K) (A : Matrix (Fin (t+2)) (Fin n) R)
    (hA : ∀ i j, alternatingRowPair f A i j=0) (J : Fin t → Fin n) :
    matrixMinorEvaluation A (pluckerIsotropyEquation f J)=0 := by
  rw [matrixMinorEvaluation_isotropy_rowPairs]
  simp only [hA, zero_mul, smul_zero, Finset.sum_const_zero]

def isotropicChartIdeal (p : PluckerIndex (t+2) n) (forms : Fin m → StrictPairs n → K) :
    Ideal (MvPolynomial (PluckerChartVariable p) K) :=
  Ideal.span (Set.range fun a : Fin m × StrictPairs (t+2) =>
    alternatingRowPair (forms a.1) (pluckerChartMatrix p) a.2.val.1 a.2.val.2)

theorem alternatingRowPair_mem_chartIdeal (p : PluckerIndex (t+2) n)
    (forms : Fin m → StrictPairs n → K) (l : Fin m) (i j : Fin (t+2)) :
    alternatingRowPair (forms l) (pluckerChartMatrix p) i j ∈ isotropicChartIdeal p forms := by
  rcases lt_trichotomy i j with hij | hij | hij
  · exact Ideal.subset_span ⟨(l,⟨(i,j),hij⟩),rfl⟩
  · subst j
    rw [alternatingRowPair_self]
    exact Ideal.zero_mem _
  · rw [alternatingRowPair_swap]
    exact (isotropicChartIdeal p forms).neg_mem (Ideal.subset_span ⟨(l,⟨(j,i),hij⟩),rfl⟩)

def isotropicPluckerIdeal (forms : Fin m → StrictPairs n → K) :
    Ideal (MvPolynomial (PluckerIndex (t+2) n) K) :=
  matrixPluckerIdeal ⊔ Ideal.span (Set.range fun a : Fin m × (Fin t → Fin n) =>
    pluckerIsotropyEquation (forms a.1) a.2)

/-- The chart map into the quotient by the actual pairwise restriction equations. -/
def isotropicChartEvaluation (p : PluckerIndex (t+2) n)
    (forms : Fin m → StrictPairs n → K) :
    MvPolynomial (PluckerIndex (t+2) n) K →ₐ[K]
      (MvPolynomial (PluckerChartVariable p) K ⧸ isotropicChartIdeal p forms) :=
  (Ideal.Quotient.mkₐ K (isotropicChartIdeal p forms)).comp
    (matrixMinorEvaluation (pluckerChartMatrix p))

theorem isotropicPluckerIdeal_le_chartKernel
    (p : PluckerIndex (t+2) n) (forms : Fin m → StrictPairs n → K) :
    isotropicPluckerIdeal forms ≤ RingHom.ker (isotropicChartEvaluation p forms).toRingHom := by
  classical
  apply sup_le
  · intro q hq
    change (Ideal.Quotient.mkₐ K _) (matrixMinorEvaluation _ q)=0
    rw [show matrixMinorEvaluation (pluckerChartMatrix (K := K) p) q=0 from
      matrixPluckerIdeal_le_matrixMinorKernel _ hq,map_zero]
  · apply Ideal.span_le.mpr
    rintro _ ⟨⟨l,J⟩,rfl⟩
    let q := Ideal.Quotient.mkₐ K (isotropicChartIdeal p forms)
    let A := (pluckerChartMatrix (K := K) p).map q
    have he : q.comp (matrixMinorEvaluation (pluckerChartMatrix p)) =
        matrixMinorEvaluation A := by
      apply MvPolynomial.algHom_ext
      intro I
      simp only [AlgHom.comp_apply,matrixMinorEvaluation,aeval_X,AlgHom.map_det]
      rfl
    change q (matrixMinorEvaluation (pluckerChartMatrix p) (pluckerIsotropyEquation (forms l) J))=0
    rw [←AlgHom.comp_apply,he]
    apply matrixMinorEvaluation_isotropy_eq_zero
    intro i j
    have hmem := alternatingRowPair_mem_chartIdeal p forms l i j
    have hz : q (alternatingRowPair (forms l) (pluckerChartMatrix p) i j)=0 :=
      Ideal.Quotient.eq_zero_iff_mem.mpr hmem
    simpa only [alternatingRowPair,map_sum,map_smul,map_sub,map_mul,A,
      AlgHom.mapMatrix_apply,Matrix.map_apply] using hz

end PaperVerification.AlternatingForms
