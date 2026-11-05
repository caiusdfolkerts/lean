module

public import PaperVerification.AlternatingFormsOddAffineHead
public import PaperVerification.AlternatingFormsChartUniversal

/-!
# Polynomial completion and uniqueness in the odd isotropic chart

Every pivot-normalized matrix can be made simultaneously isotropic by
changing only its first `r` odd columns.  The required entries are given
by the inverse of a constant linear equivalence.  Consequently the
completion is polynomial in the remaining entries.  Uniqueness is proved
over every commutative coefficient algebra.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

namespace PaperVerification.AlternatingForms

open scoped BigOperators

variable {K R : Type*} [Field K] [CommRing R] [Algebra K R]

theorem oddMatrixFirstPair_self {s k : ℕ}
    (A : Matrix (Fin s) (Fin (2*k+1)) R) (i : Fin s) :
    oddMatrixFirstPair A i i = 0 := by
  simp [oddMatrixFirstPair, mul_comm]

theorem oddMatrixSecondPair_self {s k : ℕ}
    (A : Matrix (Fin s) (Fin (2*k+1)) R) (i : Fin s) :
    oddMatrixSecondPair A i i = 0 := by
  simp [oddMatrixSecondPair, mul_comm]

theorem oddMatrixFirstPair_swap {s k : ℕ}
    (A : Matrix (Fin s) (Fin (2*k+1)) R) (i j : Fin s) :
    oddMatrixFirstPair A j i = -oddMatrixFirstPair A i j := by
  simp only [oddMatrixFirstPair, ← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro a ha
  ring

theorem oddMatrixSecondPair_swap {s k : ℕ}
    (A : Matrix (Fin s) (Fin (2*k+1)) R) (i j : Fin s) :
    oddMatrixSecondPair A j i = -oddMatrixSecondPair A i j := by
  simp only [oddMatrixSecondPair, ← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro a ha
  ring

/-- The unique head correction that kills the two row-isotropy equations. -/
def oddAffineHeadSolution {k r : ℕ}
    (A : Matrix (Fin (r+1)) (Fin (2*k+1)) R) : Fin r → Fin (r+1) → R :=
  (oddChartEquivOver (K := K) (R := R) r).symm
    (fun p => oddMatrixSecondPair A p.val.1 p.val.2,
     fun p => -oddMatrixFirstPair A p.val.1 p.val.2)

def oddAffineCompletion {k r : ℕ}
    (A : Matrix (Fin (r+1)) (Fin (2*k+1)) R) :
    Matrix (Fin (r+1)) (Fin (2*k+1)) R :=
  A + oddAffineHeadMatrix k r (oddAffineHeadSolution (K := K) A)

theorem oddAffineCompletion_pivot {k r : ℕ} (h : r ≤ k)
    (A : Matrix (Fin (r+1)) (Fin (2*k+1)) R)
    (hA : A.submatrix id (oddAffinePivot k r h).val = 1) :
    (oddAffineCompletion (K := K) A).submatrix id (oddAffinePivot k r h).val = 1 := by
  ext i j
  have hp := congrArg (fun B : Matrix (Fin (r+1)) (Fin (r+1)) R => B i j) hA
  change A i ((oddAffinePivot k r h).val j) +
    oddAffineHeadMatrix k r (oddAffineHeadSolution (K := K) A) i
      ((oddAffinePivot k r h).val j) = _
  rw [oddAffineHeadMatrix_pivot, add_zero]
  exact hp

theorem oddAffineCompletion_first {k r : ℕ} (h : r ≤ k)
    (A : Matrix (Fin (r+1)) (Fin (2*k+1)) R)
    (hA : A.submatrix id (oddAffinePivot k r h).val = 1) (i j : Fin (r+1)) :
    oddMatrixFirstPair (oddAffineCompletion (K := K) A) i j = 0 := by
  have hs (p : StrictPairs (r+1)) :
      oddMatrixFirstPair (oddAffineCompletion (K := K) A) p.val.1 p.val.2 = 0 := by
    have hsolve := congrArg (fun Z : (StrictPairs (r+1) → R) × (StrictPairs (r+1) → R) => Z.2 p)
      ((oddChartEquivOver (K := K) (R := R) r).apply_symm_apply
        (fun q => oddMatrixSecondPair A q.val.1 q.val.2,
         fun q => -oddMatrixFirstPair A q.val.1 q.val.2))
    change (oddChartEquivOver (K := K) r (oddAffineHeadSolution (K := K) A)).2 p =
      -oddMatrixFirstPair A p.val.1 p.val.2 at hsolve
    rw [oddChartEquivOver_apply] at hsolve
    dsimp only at hsolve
    rw [oddAffineCompletion, oddMatrixFirstPair_add_head h A hA, hsolve, add_neg_cancel]
  rcases lt_trichotomy i j with hij | hij | hij
  · exact hs ⟨(i,j),hij⟩
  · subst j
    exact oddMatrixFirstPair_self _ i
  · rw [oddMatrixFirstPair_swap, hs ⟨(j,i),hij⟩, neg_zero]

theorem oddAffineCompletion_second {k r : ℕ} (h : r ≤ k)
    (A : Matrix (Fin (r+1)) (Fin (2*k+1)) R)
    (hA : A.submatrix id (oddAffinePivot k r h).val = 1) (i j : Fin (r+1)) :
    oddMatrixSecondPair (oddAffineCompletion (K := K) A) i j = 0 := by
  have hs (p : StrictPairs (r+1)) :
      oddMatrixSecondPair (oddAffineCompletion (K := K) A) p.val.1 p.val.2 = 0 := by
    have hsolve := congrArg (fun Z : (StrictPairs (r+1) → R) × (StrictPairs (r+1) → R) => Z.1 p)
      ((oddChartEquivOver (K := K) (R := R) r).apply_symm_apply
        (fun q => oddMatrixSecondPair A q.val.1 q.val.2,
         fun q => -oddMatrixFirstPair A q.val.1 q.val.2))
    change (oddChartEquivOver (K := K) r (oddAffineHeadSolution (K := K) A)).1 p =
      oddMatrixSecondPair A p.val.1 p.val.2 at hsolve
    rw [oddChartEquivOver_apply] at hsolve
    dsimp only at hsolve
    rw [oddAffineCompletion, oddMatrixSecondPair_add_head h A hA,
      ← neg_sub, hsolve, add_neg_cancel]
  rcases lt_trichotomy i j with hij | hij | hij
  · exact hs ⟨(i,j),hij⟩
  · subst j
    exact oddMatrixSecondPair_self _ i
  · rw [oddMatrixSecondPair_swap, hs ⟨(j,i),hij⟩, neg_zero]

theorem oddAffineCompletion_off_head {k r : ℕ}
    (A : Matrix (Fin (r+1)) (Fin (2*k+1)) R)
    (i : Fin (r+1)) (j : Fin (2*k+1)) (hj : ¬oddAffineIsHead r j) :
    oddAffineCompletion (K := K) A i j = A i j := by
  change A i j + oddAffineHeadMatrix k r (oddAffineHeadSolution (K := K) A) i j = _
  rw [oddAffineHeadMatrix_off_head k r _ i j hj, add_zero]

/-- Two head corrections of the same normalized matrix which give
isotropic rows necessarily coincide. -/
theorem oddAffineHeadSolution_unique {k r : ℕ} (h : r ≤ k)
    (A : Matrix (Fin (r+1)) (Fin (2*k+1)) R)
    (hA : A.submatrix id (oddAffinePivot k r h).val = 1)
    (T : Fin r → Fin (r+1) → R)
    (hF : ∀ i j, oddMatrixFirstPair (A + oddAffineHeadMatrix k r T) i j = 0)
    (hG : ∀ i j, oddMatrixSecondPair (A + oddAffineHeadMatrix k r T) i j = 0) :
    T = oddAffineHeadSolution (K := K) A := by
  apply (oddChartEquivOver (K := K) (R := R) r).injective
  rw [oddAffineHeadSolution, LinearEquiv.apply_symm_apply, oddChartEquivOver_apply]
  apply Prod.ext <;> funext p
  · have hg := hG p.val.1 p.val.2
    rw [oddMatrixSecondPair_add_head h A hA, ← neg_sub, ← sub_eq_add_neg] at hg
    exact (sub_eq_zero.mp hg).symm
  · have hf := hF p.val.1 p.val.2
    rw [oddMatrixFirstPair_add_head h A hA] at hf
    exact eq_neg_of_add_eq_zero_right hf

def oddAffineHeadCoordinates {k r : ℕ} (h : r ≤ k)
    (A : Matrix (Fin (r+1)) (Fin (2*k+1)) R) : Fin r → Fin (r+1) → R :=
  fun a i => A i (oddAffineHeadVertex k r h a)

theorem oddAffine_matrix_eq_add_head {k r : ℕ} (h : r ≤ k)
    (A B : Matrix (Fin (r+1)) (Fin (2*k+1)) R)
    (hoff : ∀ i j, ¬oddAffineIsHead r j → A i j = B i j) :
    A = B + oddAffineHeadMatrix k r (oddAffineHeadCoordinates h (A-B)) := by
  ext i j
  by_cases hj : oddAffineIsHead r j
  · let a : Fin r := ⟨j.val/2,hj.2⟩
    have hv : oddAffineHeadVertex k r h a = j := by
      apply Fin.ext
      dsimp [oddAffineHeadVertex, a]
      have hm := Nat.mod_add_div j.val 2
      have hodd : j.val % 2 = 1 := hj.1
      omega
    rw [← hv]
    change A i (oddAffineHeadVertex k r h a) = B i (oddAffineHeadVertex k r h a) + _
    rw [oddAffineHeadMatrix_head]
    change A i (oddAffineHeadVertex k r h a) = B i (oddAffineHeadVertex k r h a) +
      (A i (oddAffineHeadVertex k r h a) - B i (oddAffineHeadVertex k r h a))
    ring
  · change A i j = B i j + _
    rw [oddAffineHeadMatrix_off_head k r _ i j hj, add_zero]
    exact hoff i j hj

theorem oddAffineHeadMatrix_zero (k r : ℕ) :
    oddAffineHeadMatrix (R := R) k r 0 = 0 := by
  ext i j
  simp [oddAffineHeadMatrix, chartPad]

include K in
/-- Isotropy and the non-head entries determine the whole normalized
matrix, over arbitrary commutative algebras. -/
theorem oddAffine_isotropic_ext {k r : ℕ} (h : r ≤ k)
    (A B : Matrix (Fin (r+1)) (Fin (2*k+1)) R)
    (hB : B.submatrix id (oddAffinePivot k r h).val = 1)
    (hAF : ∀ i j, oddMatrixFirstPair A i j = 0)
    (hAG : ∀ i j, oddMatrixSecondPair A i j = 0)
    (hBF : ∀ i j, oddMatrixFirstPair B i j = 0)
    (hBG : ∀ i j, oddMatrixSecondPair B i j = 0)
    (hoff : ∀ i j, ¬oddAffineIsHead r j → A i j = B i j) : A = B := by
  let T := oddAffineHeadCoordinates h (A-B)
  have hAB : A = B + oddAffineHeadMatrix k r T := oddAffine_matrix_eq_add_head h A B hoff
  have hT := oddAffineHeadSolution_unique (K := K) h B hB T
    (fun i j => hAB ▸ hAF i j) (fun i j => hAB ▸ hAG i j)
  have h0 := oddAffineHeadSolution_unique (K := K) h B hB 0
    (by simpa only [oddAffineHeadMatrix_zero, add_zero] using hBF)
    (by simpa only [oddAffineHeadMatrix_zero, add_zero] using hBG)
  have hz : T = 0 := hT.trans h0.symm
  rw [hAB, hz, oddAffineHeadMatrix_zero, add_zero]

end PaperVerification.AlternatingForms
