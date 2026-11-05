module

public import PaperVerification.AlternatingFormsPluckerDimension
public import Mathlib.Logic.Equiv.Fintype
public import Mathlib.LinearAlgebra.Matrix.Notation
public import Mathlib.Tactic.FinCases

/-!
# The converse between Plücker isotropy and row isotropy on a big cell

Selecting the complementary pivot columns turns a Plücker wedge equation into
each actual row-pair restriction equation. The determinant identity is integral;
no radical, pointwise vanishing principle, or dimension assumption is used.
This file is a fresh reconstruction after loss of the earlier source.
-/

@[expose] public section
noncomputable section
open scoped BigOperators
open MvPolynomial Matrix

namespace PaperVerification.AlternatingForms

variable {K : Type*} [Field K] {t n m : ℕ}

/-- Split the first two columns from the remaining pivot columns. -/
def chartTwoTailEquiv (t : ℕ) : Fin 2 ⊕ Fin t ≃ Fin (t+2) :=
  (finSumFinEquiv : Fin 2 ⊕ Fin t ≃ Fin (2+t)).trans
    (finCongr (Nat.add_comm 2 t))

@[simp] theorem chartTwoTailEquiv_zero (t : ℕ) :
    chartTwoTailEquiv t (Sum.inl 0)=0 := by
  apply Fin.ext
  simp [chartTwoTailEquiv]

@[simp] theorem chartTwoTailEquiv_one (t : ℕ) :
    chartTwoTailEquiv t (Sum.inl 1)=(0 : Fin (t+1)).succ := by
  apply Fin.ext
  simp [chartTwoTailEquiv]

@[simp] theorem chartTwoTailEquiv_tail (t : ℕ) (i : Fin t) :
    chartTwoTailEquiv t (Sum.inr i)=i.succ.succ := by
  apply Fin.ext
  simp [chartTwoTailEquiv, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]

/-- Any ordered pair of distinct rows can be made the first two rows. -/
theorem exists_chart_row_permutation (i j : Fin (t+2)) (hij : i≠j) :
    ∃ σ : Equiv.Perm (Fin (t+2)), σ 0=i ∧ σ (Fin.succ 0)=j := by
  let a : Fin 2 → Fin (t+2) := fun z ↦ chartTwoTailEquiv t (Sum.inl z)
  let b : Fin 2 → Fin (t+2) := ![i,j]
  have ha : Function.Injective a := (chartTwoTailEquiv t).injective.comp Sum.inl_injective
  have hb : Function.Injective b := by
    intro u v h
    fin_cases u <;> fin_cases v <;> simp_all [b]
  obtain ⟨σ,hσ⟩ := Equiv.Perm.exists_extending_pair a b ha hb
  refine ⟨σ, ?_, ?_⟩
  · simpa only [a,b,chartTwoTailEquiv_zero,Matrix.cons_val_zero] using hσ 0
  · simpa only [a,b,chartTwoTailEquiv_one,Matrix.cons_val_one,Matrix.cons_val_zero] using hσ 1

/-- With the other columns fixed to complementary pivots, the determinant is
the indicated two by two minor, up to the actual row-permutation sign. -/
theorem determinant_complementary_pivots
    {R : Type*} [CommRing R]
    (A : Matrix (Fin (t+2)) (Fin n) R) (p : Fin (t+2) → Fin n)
    (hp : (fun i j ↦ A i (p j)) = (1 : Matrix (Fin (t+2)) (Fin (t+2)) R))
    (σ : Equiv.Perm (Fin (t+2))) (a b : Fin n) :
    ((Equiv.Perm.sign σ : ℤ) : R) *
        Matrix.det (Matrix.of fun (i j : Fin (t+2)) ↦ A i
          (Fin.cons (α := fun _ : Fin (t+2) => Fin n) a
            (Fin.cons (α := fun _ : Fin (t+1) => Fin n) b
              (fun z : Fin t ↦ p (σ z.succ.succ))) j)) =
      A (σ 0) a * A (σ (Fin.succ 0)) b -
        A (σ 0) b * A (σ (Fin.succ 0)) a := by
  classical
  let M : Matrix (Fin (t+2)) (Fin (t+2)) R :=
    Matrix.of fun (i j : Fin (t+2)) ↦ A i (Fin.cons (α := fun _ : Fin (t+2) => Fin n) a
            (Fin.cons (α := fun _ : Fin (t+1) => Fin n) b
              (fun z : Fin t ↦ p (σ z.succ.succ))) j)
  let U : Matrix (Fin 2) (Fin 2) R :=
    !![A (σ 0) a, A (σ 0) b;
       A (σ (Fin.succ 0)) a, A (σ (Fin.succ 0)) b]
  let L : Matrix (Fin t) (Fin 2) R :=
    fun i j ↦ if j=0 then A (σ i.succ.succ) a else A (σ i.succ.succ) b
  have hp' (i j : Fin (t+2)) : A i (p j) = if i=j then 1 else 0 := by
    exact congrFun (congrFun hp i) j
  have hblock :
      (M.submatrix σ id).submatrix (chartTwoTailEquiv t) (chartTwoTailEquiv t) =
        Matrix.fromBlocks U 0 L 1 := by
    ext i j
    cases i with
    | inl i =>
      cases j with
      | inl j =>
        fin_cases i <;> fin_cases j <;>
          simp [M,U,Matrix.submatrix_apply]
      | inr j =>
        fin_cases i <;>
          simp [M,Matrix.submatrix_apply,hp',σ.injective.eq_iff,Fin.succ_ne_zero,
            Ne.symm (Fin.succ_ne_zero j.succ),Ne.symm (Fin.succ_succ_ne_one j)]
    | inr i =>
      cases j with
      | inl j =>
        fin_cases j <;> simp [M,L,Matrix.submatrix_apply,Matrix.fromBlocks_apply₂₁] <;> rfl
      | inr j =>
        simp [M,Matrix.submatrix_apply,hp',σ.injective.eq_iff,Matrix.one_apply]
  calc
    ((Equiv.Perm.sign σ : ℤ) : R) * Matrix.det M =
        Matrix.det (M.submatrix σ id) := (Matrix.det_permute σ M).symm
    _ = Matrix.det ((M.submatrix σ id).submatrix
        (chartTwoTailEquiv t) (chartTwoTailEquiv t)) :=
      (Matrix.det_submatrix_equiv_self _ _).symm
    _ = Matrix.det U := by rw [hblock,Matrix.det_fromBlocks_zero₁₂,Matrix.det_one,mul_one]
    _ = _ := by simp only [U,Matrix.det_fin_two_of]

/-- A complementary-pivot wedge equation is precisely a row-pair restriction.
This identity is valid over every commutative K-algebra. -/
theorem matrixMinorEvaluation_complementary_isotropy
    {R : Type*} [CommRing R] [Algebra K R]
    (f : StrictPairs n → K) (A : Matrix (Fin (t+2)) (Fin n) R)
    (p : Fin (t+2) → Fin n)
    (hp : (fun i j ↦ A i (p j)) = (1 : Matrix (Fin (t+2)) (Fin (t+2)) R))
    (σ : Equiv.Perm (Fin (t+2))) :
    ((Equiv.Perm.sign σ : ℤ) : R) *
      matrixMinorEvaluation (K := K) A
        (pluckerIsotropyEquation f (fun z ↦ p (σ z.succ.succ))) =
      alternatingRowPair f A (σ 0) (σ (Fin.succ 0)) := by
  classical
  simp only [pluckerIsotropyEquation,map_sum,map_smul,
    matrixMinorEvaluation_orderedCoordinate,alternatingRowPair,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a ha
  rw [mul_smul_comm,determinant_complementary_pivots A p hp σ a.val.1 a.val.2]

/-- The row-isotropy ideal is the image of the actual Plücker isotropy ideal.
This is ideal equality, retaining the scheme structure on the chart. -/
theorem isotropicPluckerIdeal_map_chart_eq [CharZero K]
    (p : PluckerIndex (t+2) n) (forms : Fin m → StrictPairs n → K) :
    (isotropicPluckerIdeal forms).map
      (matrixMinorEvaluation (K := K) (pluckerChartMatrix (K := K) p)).toRingHom =
        isotropicChartIdeal p forms := by
  classical
  apply le_antisymm
  · apply Ideal.map_le_iff_le_comap.mpr
    intro q hq
    have h := isotropicPluckerIdeal_le_chartKernel p forms hq
    change (Ideal.Quotient.mkₐ K (isotropicChartIdeal p forms))
      (matrixMinorEvaluation (K := K) (pluckerChartMatrix p) q)=0 at h
    change matrixMinorEvaluation (K := K) (pluckerChartMatrix p) q ∈ isotropicChartIdeal p forms
    exact Ideal.Quotient.eq_zero_iff_mem.mp h
  · apply Ideal.span_le.mpr
    rintro _ ⟨⟨l,ij⟩,rfl⟩
    obtain ⟨σ,hσ0,hσ1⟩ := exists_chart_row_permutation ij.val.1 ij.val.2
      (ne_of_lt ij.property)
    let J : Fin t → Fin n := fun z ↦ p.val (σ z.succ.succ)
    have hmem :
        matrixMinorEvaluation (K := K) (pluckerChartMatrix (K := K) p)
          (pluckerIsotropyEquation (forms l) J) ∈
          (isotropicPluckerIdeal forms).map
            (matrixMinorEvaluation (K := K) (pluckerChartMatrix p)).toRingHom :=
      Ideal.mem_map_of_mem _
        (Ideal.mem_sup_right (Ideal.subset_span ⟨(l,J),rfl⟩))
    have he := matrixMinorEvaluation_complementary_isotropy (forms l)
      (pluckerChartMatrix (K := K) p) p.val (pluckerChartMatrix_pivot p) σ
    rw [hσ0,hσ1] at he
    change alternatingRowPair (forms l) (pluckerChartMatrix p) ij.val.1 ij.val.2 ∈ _
    rw [←he]
    exact Ideal.mul_mem_left _ _ hmem

theorem matrixMinorEvaluation_chart_kernel (p : PluckerIndex (t+2) n) :
    RingHom.ker (matrixMinorEvaluation (K := K) (pluckerChartMatrix (K := K) p)).toRingHom =
      pluckerBigCellIdeal (K := K) p := by
  ext q
  change matrixMinorEvaluation (K := K) (pluckerChartMatrix p) q=0 ↔ _
  rw [←pluckerBigCellToMatrix_class]
  change pluckerBigCellEquiv (K := K) p (pluckerBigCellClass (K := K) p q)=0 ↔ _
  have he : pluckerBigCellEquiv (K := K) p (pluckerBigCellClass (K := K) p q)=0 ↔
      pluckerBigCellClass (K := K) p q=0 := by
    constructor
    · intro h
      apply (pluckerBigCellEquiv (K := K) p).injective
      simpa only [map_zero] using h
    · intro h
      rw [h,map_zero]
  exact he.trans Ideal.Quotient.eq_zero_iff_mem

/-- The full kernel includes exactly the original isotropy ideal and the
normalization of the selected pivot coordinate. -/
theorem isotropicChartEvaluation_kernel [CharZero K]
    (p : PluckerIndex (t+2) n) (forms : Fin m → StrictPairs n → K) :
    RingHom.ker (isotropicChartEvaluation p forms).toRingHom =
      isotropicPluckerIdeal forms ⊔ Ideal.span {X p-1} := by
  have h := Ideal.comap_map_of_surjective
    (matrixMinorEvaluation (K := K) (pluckerChartMatrix (K := K) p)).toRingHom
    (matrixMinorEvaluation_chart_surjective p) (isotropicPluckerIdeal forms)
  rw [isotropicPluckerIdeal_map_chart_eq p forms,
    ←RingHom.ker_eq_comap_bot,matrixMinorEvaluation_chart_kernel] at h
  have hk : RingHom.ker (isotropicChartEvaluation p forms).toRingHom =
      (isotropicChartIdeal p forms).comap
        (matrixMinorEvaluation (K := K) (pluckerChartMatrix p)).toRingHom := by
    ext q
    change (Ideal.Quotient.mkₐ K (isotropicChartIdeal p forms))
      (matrixMinorEvaluation (K := K) (pluckerChartMatrix p) q)=0 ↔ _
    exact Ideal.Quotient.eq_zero_iff_mem
  rw [hk,h,pluckerBigCellIdeal]
  have hle : matrixPluckerIdeal (K := K) (s := t+2) (n := n) ≤
      isotropicPluckerIdeal (t := t) forms := le_sup_left
  rw [←sup_assoc,sup_of_le_left hle]

/-- The actual normalized Plücker quotient is the affine scheme chart cut out
by the pairwise row restrictions. Both quotient ideals are stated literally. -/
def isotropicPluckerBigCellEquiv [CharZero K]
    (p : PluckerIndex (t+2) n) (forms : Fin m → StrictPairs n → K) :
    (MvPolynomial (PluckerIndex (t+2) n) K ⧸
      (isotropicPluckerIdeal forms ⊔ Ideal.span {X p-1})) ≃ₐ[K]
      (MvPolynomial (PluckerChartVariable p) K ⧸ isotropicChartIdeal p forms) :=
  (Ideal.quotientEquivAlgOfEq K (isotropicChartEvaluation_kernel p forms).symm).trans
    (Ideal.quotientKerAlgEquivOfSurjective (isotropicChartEvaluation_surjective p forms))

end PaperVerification.AlternatingForms
