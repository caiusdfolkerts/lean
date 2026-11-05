module

public import PaperVerification.FermionNewtonColumns
public import PaperVerification.FermionNewtonRationalRecursion
public import PaperVerification.FermionNewtonMatrixRecurrence
public import Mathlib.Data.Fin.Embedding

/-!
# The literal all-one Newton matrix and its first-coordinate blocks

The matrix is built from the exact active suffixes and residue columns.
All three sign cases have their actual block decompositions proved here.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace PaperVerification.Fermion.Newton

open Polynomial
open scoped BigOperators Matrix

variable {L : Type*} [Field L] {n : ℕ}

def activeTail (i : Fin n) : Finset (Fin n) := Finset.univ.filter (i ≤ ·)

@[simp] theorem activeTail_zero : activeTail (0 : Fin (n + 1)) = Finset.univ := by
  ext i
  simp [activeTail]

theorem activeTail_succ (i : Fin n) :
    activeTail i.succ = (activeTail i).map (Fin.succEmb n) := by
  ext j
  refine Fin.cases ?_ (fun j ↦ ?_) j
  · simp [activeTail, Finset.mem_map, Fin.succEmb]
  · simp [activeTail, Finset.mem_map', Fin.succEmb]

theorem earlierPositive_succ (σ : Fin (n + 1) → ℤ) (i : Fin n) :
    earlierPositive σ i.succ =
      if σ 0 = 1 then insert 0 ((earlierPositive (σ ∘ Fin.succ) i).map (Fin.succEmb n))
      else (earlierPositive (σ ∘ Fin.succ) i).map (Fin.succEmb n) := by
  ext j
  refine Fin.cases ?_ (fun j ↦ ?_) j
  · by_cases h : σ 0 = 1 <;> simp [earlierPositive, h, Finset.mem_map, Fin.succEmb]
  · by_cases h : σ 0 = 1 <;> simp [earlierPositive, h, Finset.mem_map',
      Fin.succEmb, Function.comp_apply]

theorem earlierNegative_succ (σ : Fin (n + 1) → ℤ) (i : Fin n) :
    earlierNegative σ i.succ =
      if σ 0 = -1 then insert 0 ((earlierNegative (σ ∘ Fin.succ) i).map (Fin.succEmb n))
      else (earlierNegative (σ ∘ Fin.succ) i).map (Fin.succEmb n) := by
  ext j
  refine Fin.cases ?_ (fun j ↦ ?_) j
  · by_cases h : σ 0 = -1 <;> simp [earlierNegative, h, Finset.mem_map, Fin.succEmb]
  · by_cases h : σ 0 = -1 <;> simp [earlierNegative, h, Finset.mem_map',
      Fin.succEmb, Function.comp_apply]

def allOneNumerator (σ : Fin n → ℤ) (x : Fin n → L) (i : Fin n) : L[X] :=
  X * Lagrange.nodal (earlierPositive σ i) x

def allOneNewtonMatrix (σ : Fin n → ℤ) (x β : Fin n → L) : Matrix (Fin n) (Fin n) L :=
  fun k i ↦ rationalColumn (allOneNumerator σ x i) (earlierNegative σ i) (activeTail i) x β k

theorem allOneNumerator_succ_of_ne_one
    (σ : Fin (n + 1) → ℤ) (x : Fin (n + 1) → L) (i : Fin n) (hσ : σ 0 ≠ 1) :
    allOneNumerator σ x i.succ = allOneNumerator (σ ∘ Fin.succ) (x ∘ Fin.succ) i := by
  rw [allOneNumerator, earlierPositive_succ, if_neg hσ, nodal_map_embedding]
  rfl

theorem allOneNumerator_succ_of_one
    (σ : Fin (n + 1) → ℤ) (x : Fin (n + 1) → L) (i : Fin n) (hσ : σ 0 = 1) :
    allOneNumerator σ x i.succ =
      allOneNumerator (σ ∘ Fin.succ) (x ∘ Fin.succ) i * (X - C (x 0)) := by
  rw [allOneNumerator, earlierPositive_succ, if_pos hσ,
    nodal_insert _ x 0 (by simp [Finset.mem_map, Fin.succEmb]), nodal_map_embedding]
  change X * ((X - C (x 0)) * Lagrange.nodal (earlierPositive (σ ∘ Fin.succ) i)
    (x ∘ Fin.succ)) =
      (X * Lagrange.nodal (earlierPositive (σ ∘ Fin.succ) i) (x ∘ Fin.succ)) * (X - C (x 0))
  ring

@[simp] theorem allOneNewtonMatrix_first_column
    (σ : Fin (n + 1) → ℤ) (x β : Fin (n + 1) → L) (k : Fin (n + 1)) :
    allOneNewtonMatrix σ x β k 0 = x k := by
  simp [allOneNewtonMatrix, allOneNumerator, earlierPositive, earlierNegative,
    activeTail, rationalColumn, Lagrange.nodal]

theorem allOneNewtonMatrix_first_row_nonnegative
    (σ : Fin (n + 1) → ℤ) (x β : Fin (n + 1) → L)
    (hσ : σ 0 ≠ -1) (i : Fin n) : allOneNewtonMatrix σ x β 0 i.succ = 0 := by
  simp [allOneNewtonMatrix, rationalColumn, activeTail, earlierNegative, hσ]

theorem allOneNewtonMatrix_suffix_flat
    (σ : Fin (n + 1) → ℤ) (x β : Fin (n + 1) → L) (hσ : σ 0 = 0) (k i : Fin n) :
    allOneNewtonMatrix σ x β k.succ i.succ =
      allOneNewtonMatrix (σ ∘ Fin.succ) (x ∘ Fin.succ) (β ∘ Fin.succ) k i := by
  rw [allOneNewtonMatrix, allOneNumerator_succ_of_ne_one σ x i (by omega),
    earlierNegative_succ, if_neg (by omega), activeTail_succ]
  exact rationalColumn_map_embedding (Fin.succEmb n) _ _ _ x β k

theorem allOneNewtonMatrix_suffix_up
    (σ : Fin (n + 1) → ℤ) (x β : Fin (n + 1) → L) (hσ : σ 0 = 1) (k i : Fin n) :
    allOneNewtonMatrix σ x β k.succ i.succ = (x k.succ - x 0) *
      allOneNewtonMatrix (σ ∘ Fin.succ) (x ∘ Fin.succ) (β ∘ Fin.succ) k i := by
  rw [allOneNewtonMatrix, allOneNumerator_succ_of_one σ x i hσ,
    earlierNegative_succ, if_neg (by omega), activeTail_succ,
    rationalColumn_mul_polynomial, eval_sub, eval_X, eval_C]
  congr 1
  exact rationalColumn_map_embedding (Fin.succEmb n) _ _ _ x β k

theorem allOneNewtonMatrix_suffix_down
    (σ : Fin (n + 1) → ℤ) (x β : Fin (n + 1) → L) (hσ : σ 0 = -1) (k i : Fin n) :
    allOneNewtonMatrix σ x β k.succ i.succ =
      allOneNewtonMatrix (σ ∘ Fin.succ) (x ∘ Fin.succ) (β ∘ Fin.succ) k i / (x k.succ - x 0) := by
  rw [allOneNewtonMatrix, allOneNumerator_succ_of_ne_one σ x i (by omega),
    earlierNegative_succ, if_pos hσ, activeTail_succ]
  exact rationalColumn_negative_suffix (Fin.succEmb n) _ _ _ x β 0
    (by rintro ⟨j, hj⟩; exact Fin.succ_ne_zero j hj) k

theorem allOneNewtonMatrix_first_row_down
    (σ : Fin (n + 1) → ℤ) (x β : Fin (n + 1) → L) (hσ : σ 0 = -1) (i : Fin n) :
    allOneNewtonMatrix σ x β 0 i.succ =
      x 0 * ((Lagrange.nodal (earlierPositive (σ ∘ Fin.succ) i) (x ∘ Fin.succ)).eval (x 0) /
        ((Lagrange.nodal (earlierNegative (σ ∘ Fin.succ) i) (x ∘ Fin.succ)).eval (x 0) * β 0) *
          ∑ k ∈ activeTail i, β k.succ / (x 0 - x k.succ)) := by
  rw [allOneNewtonMatrix, allOneNumerator_succ_of_ne_one σ x i (by omega),
    earlierNegative_succ, if_pos hσ, activeTail_succ,
    rationalColumn_negative_new_row (Fin.succEmb n) _ _ _ x β 0
      (by rintro ⟨j, hj⟩; exact Fin.succ_ne_zero j hj)]
  simp only [allOneNumerator, eval_mul, eval_X, Fin.coe_succEmb]
  ring

def allOneHeight (σ : Fin n → ℤ) (i : Fin n) : ℤ :=
  1 + ∑ j ∈ Finset.univ.filter (fun j ↦ j < i), σ j

@[simp] theorem allOneHeight_zero (σ : Fin (n + 1) → ℤ) : allOneHeight σ 0 = 1 := by
  simp [allOneHeight]

theorem allOneHeight_succ (σ : Fin (n + 1) → ℤ) (i : Fin n) :
    allOneHeight σ i.succ = allOneHeight (σ ∘ Fin.succ) i + σ 0 := by
  simp only [allOneHeight, Finset.sum_filter, Fin.sum_univ_succ, Function.comp_apply]
  simp only [Fin.succ_pos, if_true, Fin.succ_lt_succ_iff]
  ring

/-- This converts the signed height used by the auxiliary expansion into
the exact numerator/denominator degree test in the Schur calculation. -/
theorem allOneHeight_eq_card_difference
    (σ : Fin n → ℤ) (hσ : ∀ i, σ i = -1 ∨ σ i = 0 ∨ σ i = 1) (i : Fin n) :
    allOneHeight σ i = 1 + (earlierPositive σ i).card - (earlierNegative σ i).card := by
  have hterm (j : Fin n) :
      (if j < i then σ j else 0) =
        (if j < i ∧ σ j = 1 then (1 : ℤ) else 0) -
          (if j < i ∧ σ j = -1 then (1 : ℤ) else 0) := by
    rcases hσ j with h | h | h <;> by_cases hji : j < i <;> simp [h, hji]
  simp only [allOneHeight, Finset.sum_filter]
  simp_rw [hterm]
  rw [Finset.sum_sub_distrib]
  simp only [earlierPositive, earlierNegative, ← Finset.sum_filter, Finset.sum_const,
    nsmul_eq_mul, mul_one, Nat.cast_id]
  ring

theorem allOneNewtonMatrix_eq_adjoin
    (σ : Fin (n + 1) → ℤ) (x β : Fin (n + 1) → L) (scale : Fin n → L)
    (hscale : ∀ k i,
      allOneNewtonMatrix σ x β k.succ i.succ = scale k *
        allOneNewtonMatrix (σ ∘ Fin.succ) (x ∘ Fin.succ) (β ∘ Fin.succ) k i) :
    allOneNewtonMatrix σ x β =
      adjoinPowerColumn (x 0) (x ∘ Fin.succ)
        (fun i ↦ allOneNewtonMatrix σ x β 0 i.succ) scale
        (allOneNewtonMatrix (σ ∘ Fin.succ) (x ∘ Fin.succ) (β ∘ Fin.succ)) := by
  ext k i
  refine Fin.cases ?_ (fun k ↦ ?_) k <;> refine Fin.cases ?_ (fun i ↦ ?_) i
  · exact allOneNewtonMatrix_first_column σ x β 0
  · rfl
  · exact allOneNewtonMatrix_first_column σ x β k.succ
  · exact hscale k i

section Coefficients

variable {E : Type*} [Field E]

theorem allOneNewtonMatrix_map (f : L →+* E) (σ : Fin n → ℤ) (x β : Fin n → L) :
    (allOneNewtonMatrix σ x β).map f = allOneNewtonMatrix σ (f ∘ x) (f ∘ β) := by
  ext k i
  change f (rationalColumn _ _ _ _ _ _) = _
  rw [rationalColumn_map_coefficients]
  have hN : (allOneNumerator σ x i).map f = allOneNumerator σ (f ∘ x) i := by
    simp only [allOneNumerator, Polynomial.map_mul, Polynomial.map_X, nodal_map_coefficients]
  rw [hN]
  rfl

end Coefficients

/-- Once the determinant at the new size is known nonzero, the literal
block formulas establish the full auxiliary assertion at that size. The
only inductive assertion is the exact corresponding suffix pattern. -/
theorem allOneExpansionPattern_of_suffix
    (σ : Fin (n + 1) → ℤ) (x β : Fin (n + 1) → L)
    (hσ : σ 0 = -1 ∨ σ 0 = 0 ∨ σ 0 = 1)
    (hx : Function.Injective x) (hx0 : x 0 ≠ 0)
    (hM : (allOneNewtonMatrix σ x β).det ≠ 0)
    (hS : (allOneNewtonMatrix (σ ∘ Fin.succ) (x ∘ Fin.succ) (β ∘ Fin.succ)).det ≠ 0)
    (hpattern : PowerExpansionPattern (allOneHeight (σ ∘ Fin.succ))
      (matrixPowerExpansion
        (allOneNewtonMatrix (σ ∘ Fin.succ) (x ∘ Fin.succ) (β ∘ Fin.succ)) (x ∘ Fin.succ))) :
    PowerExpansionPattern (allOneHeight σ)
      (matrixPowerExpansion (allOneNewtonMatrix σ x β) x) := by
  let S := allOneNewtonMatrix (σ ∘ Fin.succ) (x ∘ Fin.succ) (β ∘ Fin.succ)
  let A := matrixPowerExpansion (allOneNewtonMatrix σ x β) x
  let B := matrixPowerExpansion S (x ∘ Fin.succ)
  have hzy (i : Fin n) : x i.succ ≠ x 0 := fun h ↦ Fin.succ_ne_zero i (hx h)
  have hS_inj := matrix_mulVec_injective_of_det_ne_zero S hS
  have hB (d : ℕ) : S *ᵥ B d = fun i ↦ x i.succ ^ d :=
    matrixPowerExpansion_solves S hS _ d
  have hnodes : Fin.cases (x 0) (x ∘ Fin.succ) = x := by
    funext i
    exact Fin.cases rfl (fun j ↦ rfl) i
  have hnodespow (e : ℕ) : (fun i ↦ Fin.cases (x 0) (x ∘ Fin.succ) i ^ e) =
      (fun i ↦ x i ^ e) := by
    funext i
    exact congrArg (fun t : L ↦ t ^ e) (congrFun hnodes i)
  apply powerExpansionPattern_of_suffix_recurrences (allOneHeight σ)
    (allOneHeight (σ ∘ Fin.succ)) A B (x 0) (σ 0) hσ
    (allOneHeight_zero σ) (allOneHeight_succ σ) hpattern
  · intro i
    exact matrixPowerExpansion_one_of_first_column _ hM x
      (allOneNewtonMatrix_first_column σ x β) i
  · intro hσ d hd i
    have hmatrix : allOneNewtonMatrix σ x β = adjoinPowerColumn (x 0) (x ∘ Fin.succ) 0 1 S := by
      rw [allOneNewtonMatrix_eq_adjoin σ x β 1
        (fun k j ↦ by simpa only [Pi.one_apply, one_mul] using
          allOneNewtonMatrix_suffix_flat σ x β hσ k j)]
      congr 1
      funext j
      exact allOneNewtonMatrix_first_row_nonnegative σ x β (by omega) j
    apply expansion_flat_suffix (x 0) hx0 (x ∘ Fin.succ) S hS_inj A B
      (fun e ↦ ?_) hB d hd i
    rw [hnodespow]
    rw [← hmatrix]
    exact matrixPowerExpansion_solves _ hM x e
  · intro hσ d hd i
    have hmatrix : allOneNewtonMatrix σ x β =
        adjoinPowerColumn (x 0) (x ∘ Fin.succ) 0 (fun k ↦ x k.succ - x 0) S := by
      rw [allOneNewtonMatrix_eq_adjoin σ x β (fun k ↦ x k.succ - x 0)
        (allOneNewtonMatrix_suffix_up σ x β hσ)]
      congr 1
      funext j
      exact allOneNewtonMatrix_first_row_nonnegative σ x β (by omega) j
    apply expansion_up_suffix (x 0) hx0 (x ∘ Fin.succ) hzy S hS_inj A B
      (fun e ↦ ?_) hB d hd i
    rw [hnodespow]
    simp only [Function.comp_apply]
    rw [← hmatrix]
    exact matrixPowerExpansion_solves _ hM x e
  · intro hσ d hd i
    let row := fun j : Fin n ↦ allOneNewtonMatrix σ x β 0 j.succ
    have hmatrix : allOneNewtonMatrix σ x β =
        adjoinPowerColumn (x 0) (x ∘ Fin.succ) row (fun k ↦ (x k.succ - x 0)⁻¹) S := by
      apply allOneNewtonMatrix_eq_adjoin
      intro k j
      rw [allOneNewtonMatrix_suffix_down σ x β hσ, div_eq_mul_inv, mul_comm]
    apply expansion_down_suffix (x 0) (x ∘ Fin.succ) row hzy S hS_inj A B
      (fun e ↦ ?_) hB d i
    rw [hnodespow]
    simp only [Function.comp_apply]
    rw [← hmatrix]
    exact matrixPowerExpansion_solves _ hM x e

end PaperVerification.Fermion.Newton
