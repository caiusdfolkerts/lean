module

public import PaperVerification.AlternatingFormsOddChartScalarExtension
public import PaperVerification.AlternatingFormsOddPluckerDimension
public import Mathlib.Tactic.Ring.Basic
import Lean.Elab.Tactic.Omega

/-!
# The constant invertible block in the odd isotropic big cell

On the chart with pivot columns `b₀,…,bᵣ`, vary the entries in
`a₁,…,aᵣ` and keep all other entries fixed.  The change in the two
isotropy equations is exactly the constant chart map, independently of
the remaining entries.  This is the polynomial elimination step behind
the rationality argument.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

namespace PaperVerification.AlternatingForms

open scoped BigOperators

variable {K R : Type*} [Field K] [CommRing R] [Algebra K R]

def oddAffineEvenVertex (k : ℕ) (i : Fin (k+1)) : Fin (2*k+1) :=
  ⟨2*i.val, by have := i.isLt; omega⟩

def oddAffineOddVertex (k : ℕ) (i : Fin k) : Fin (2*k+1) :=
  ⟨2*i.val+1, by have := i.isLt; omega⟩

def oddAffinePivot (k r : ℕ) (h : r ≤ k) : PluckerIndex (r+1) (2*k+1) :=
  ⟨fun i => ⟨2*i.val, by have := i.isLt; omega⟩, by
    intro i j hij
    change 2*i.val < 2*j.val
    exact Nat.mul_lt_mul_of_pos_left hij (by decide)⟩

def oddAffineHeadVertex (k r : ℕ) (h : r ≤ k) (i : Fin r) : Fin (2*k+1) :=
  ⟨2*i.val+1, by have := i.isLt; omega⟩

def oddAffineIsHead (r : ℕ) {k : ℕ} (j : Fin (2*k+1)) : Prop :=
  j.val % 2 = 1 ∧ j.val / 2 < r

instance (r k : ℕ) : DecidablePred (oddAffineIsHead r (k := k)) :=
  by
    intro j
    unfold oddAffineIsHead
    infer_instance

/-- The matrix supported precisely in the first `r` nonpivot odd columns. -/
def oddAffineHeadMatrix (k r : ℕ) (T : Fin r → Fin (r+1) → R) :
    Matrix (Fin (r+1)) (Fin (2*k+1)) R :=
  fun i j => if j.val % 2 = 1 then chartPad T (j.val/2+1) i.val else 0

theorem oddAffineHeadMatrix_even (k r : ℕ)
    (T : Fin r → Fin (r+1) → R) (i : Fin (r+1)) (a : Fin (k+1)) :
    oddAffineHeadMatrix k r T i (oddAffineEvenVertex k a) = 0 := by
  have h : (2*a.val) % 2 ≠ 1 := by omega
  simp only [oddAffineHeadMatrix, oddAffineEvenVertex, h, ite_false]

theorem oddAffineHeadMatrix_odd (k r : ℕ)
    (T : Fin r → Fin (r+1) → R) (i : Fin (r+1)) (a : Fin k) :
    oddAffineHeadMatrix k r T i (oddAffineOddVertex k a) =
      chartPad T (a.val+1) i.val := by
  have h : (2*a.val+1) % 2 = 1 := by omega
  have hd : (2*a.val+1) / 2 = a.val := by omega
  simp only [oddAffineHeadMatrix, oddAffineOddVertex, h, hd, ite_true]

theorem oddAffineHeadMatrix_head (k r : ℕ) (h : r ≤ k)
    (T : Fin r → Fin (r+1) → R) (i : Fin (r+1)) (a : Fin r) :
    oddAffineHeadMatrix k r T i (oddAffineHeadVertex k r h a) = T a i := by
  change oddAffineHeadMatrix k r T i
      (oddAffineOddVertex k ⟨a.val, lt_of_lt_of_le a.isLt h⟩) = _
  rw [oddAffineHeadMatrix_odd]
  exact chartPad_entry T a i

theorem oddAffineHeadMatrix_pivot (k r : ℕ) (h : r ≤ k)
    (T : Fin r → Fin (r+1) → R) (i j : Fin (r+1)) :
    oddAffineHeadMatrix k r T i ((oddAffinePivot k r h).val j) = 0 := by
  change oddAffineHeadMatrix k r T i
    (oddAffineEvenVertex k ⟨j.val, by have := j.isLt; omega⟩) = 0
  exact oddAffineHeadMatrix_even k r T i _

theorem oddAffineHeadMatrix_off_head (k r : ℕ)
    (T : Fin r → Fin (r+1) → R) (i : Fin (r+1)) (j : Fin (2*k+1))
    (hj : ¬oddAffineIsHead r j) : oddAffineHeadMatrix k r T i j = 0 := by
  simp only [oddAffineHeadMatrix]
  split_ifs with ho
  · have hb : ¬j.val/2 < r := fun hb => hj ⟨ho,hb⟩
    simp only [chartPad]
    split_ifs with hp
    · omega
    · rfl
  · rfl

def oddMatrixFirstPair {s k : ℕ}
    (A : Matrix (Fin s) (Fin (2*k+1)) R) (i j : Fin s) : R :=
  ∑ a : Fin k, (A i (oddAffineEvenVertex k a.castSucc) * A j (oddAffineOddVertex k a) -
    A i (oddAffineOddVertex k a) * A j (oddAffineEvenVertex k a.castSucc))

def oddMatrixSecondPair {s k : ℕ}
    (A : Matrix (Fin s) (Fin (2*k+1)) R) (i j : Fin s) : R :=
  ∑ a : Fin k, (A i (oddAffineOddVertex k a) * A j (oddAffineEvenVertex k a.succ) -
    A i (oddAffineEvenVertex k a.succ) * A j (oddAffineOddVertex k a))

theorem oddMatrixPair_eq_alternatingRowPair {t k : ℕ}
    (A : Matrix (Fin (t+2)) (Fin (2*k+1)) R) (i j : Fin (t+2)) (l : Fin 2) :
    alternatingRowPair (oddPluckerForms (K := K) k l) A i j =
      ∑ a : Fin k, (A i (oddPluckerEdge k l a).val.1 * A j (oddPluckerEdge k l a).val.2 -
        A i (oddPluckerEdge k l a).val.2 * A j (oddPluckerEdge k l a).val.1) := by
  classical
  simp only [alternatingRowPair, oddPluckerForms, Finset.sum_smul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a ha
  simp only [ite_smul, one_smul, zero_smul, Finset.sum_ite_eq', Finset.mem_univ, ite_true]

theorem oddMatrixFirstPair_eq {t k : ℕ}
    (A : Matrix (Fin (t+2)) (Fin (2*k+1)) R) (i j : Fin (t+2)) :
    alternatingRowPair (oddPluckerForms (K := K) k 0) A i j =
      oddMatrixFirstPair A i j := by
  rw [oddMatrixPair_eq_alternatingRowPair]
  rfl

theorem oddMatrixSecondPair_eq {t k : ℕ}
    (A : Matrix (Fin (t+2)) (Fin (2*k+1)) R) (i j : Fin (t+2)) :
    alternatingRowPair (oddPluckerForms (K := K) k 1) A i j =
      oddMatrixSecondPair A i j := by
  rw [oddMatrixPair_eq_alternatingRowPair]
  rfl

private theorem oddAffine_pivot_entry {k r : ℕ} {h : r ≤ k}
    (A : Matrix (Fin (r+1)) (Fin (2*k+1)) R)
    (hA : A.submatrix id (oddAffinePivot k r h).val = 1) (i j : Fin (r+1)) :
    A i ((oddAffinePivot k r h).val j) = if i=j then 1 else 0 := by
  exact congrArg (fun B : Matrix (Fin (r+1)) (Fin (r+1)) R => B i j) hA

private theorem oddAffine_first_product_sum {k r : ℕ} (h : r ≤ k)
    (A : Matrix (Fin (r+1)) (Fin (2*k+1)) R)
    (hA : A.submatrix id (oddAffinePivot k r h).val = 1)
    (T : Fin r → Fin (r+1) → R) (i j : Fin (r+1)) :
    (∑ a : Fin k, A i (oddAffineEvenVertex k a.castSucc) *
      chartPad T (a.val+1) j.val) = chartPad T (i.val+1) j.val := by
  classical
  have hoff (a : Fin k) (hai : a.val ≠ i.val) :
      A i (oddAffineEvenVertex k a.castSucc) * chartPad T (a.val+1) j.val = 0 := by
    by_cases har : a.val < r+1
    · change A i ((oddAffinePivot k r h).val ⟨a.val,har⟩) * _ = 0
      rw [oddAffine_pivot_entry A hA]
      have hne : i ≠ (⟨a.val,har⟩ : Fin (r+1)) := by
        intro he
        exact hai (congrArg Fin.val he).symm
      simp only [hne, ite_false, zero_mul]
    · have hz : chartPad T (a.val+1) j.val = 0 := by
        simp only [chartPad]
        split_ifs with hc
        · omega
        · rfl
      rw [hz, mul_zero]
  by_cases hik : i.val < k
  · let a₀ : Fin k := ⟨i.val,hik⟩
    calc
      _ = A i (oddAffineEvenVertex k a₀.castSucc) *
          chartPad T (a₀.val+1) j.val := by
        apply Finset.sum_eq_single a₀
        · intro a ha hne
          exact hoff a (fun he => hne (Fin.ext he))
        · simp
      _ = _ := by
        change A i ((oddAffinePivot k r h).val i) * chartPad T (i.val+1) j.val = _
        rw [oddAffine_pivot_entry A hA]
        simp
  · have hir : i.val = r := by have := i.isLt; omega
    rw [hir, chartPad_last]
    apply Finset.sum_eq_zero
    intro a ha
    exact hoff a (by have := a.isLt; omega)

private theorem oddAffine_second_product_sum {k r : ℕ} (h : r ≤ k)
    (A : Matrix (Fin (r+1)) (Fin (2*k+1)) R)
    (hA : A.submatrix id (oddAffinePivot k r h).val = 1)
    (T : Fin r → Fin (r+1) → R) (i j : Fin (r+1)) :
    (∑ a : Fin k, A i (oddAffineEvenVertex k a.succ) *
      chartPad T (a.val+1) j.val) = chartPad T i.val j.val := by
  classical
  have hoff (a : Fin k) (hai : a.val+1 ≠ i.val) :
      A i (oddAffineEvenVertex k a.succ) * chartPad T (a.val+1) j.val = 0 := by
    by_cases har : a.val+1 < r+1
    · change A i ((oddAffinePivot k r h).val ⟨a.val+1,har⟩) * _ = 0
      rw [oddAffine_pivot_entry A hA]
      have hne : i ≠ (⟨a.val+1,har⟩ : Fin (r+1)) := by
        intro he
        exact hai (congrArg Fin.val he).symm
      simp only [hne, ite_false, zero_mul]
    · have hz : chartPad T (a.val+1) j.val = 0 := by
        simp only [chartPad]
        split_ifs with hc
        · omega
        · rfl
      rw [hz, mul_zero]
  by_cases hi : i.val = 0
  · rw [hi, chartPad_first]
    apply Finset.sum_eq_zero
    intro a ha
    exact hoff a (by omega)
  · let a₀ : Fin k := ⟨i.val-1, by have := i.isLt; omega⟩
    have ha₀ : a₀.val+1 = i.val := by dsimp [a₀]; omega
    calc
      _ = A i (oddAffineEvenVertex k a₀.succ) * chartPad T (a₀.val+1) j.val := by
        apply Finset.sum_eq_single a₀
        · intro a ha hne
          apply hoff
          intro he
          apply hne
          apply Fin.ext
          dsimp [a₀]
          omega
        · simp
      _ = _ := by
        have hv : oddAffineEvenVertex k a₀.succ = (oddAffinePivot k r h).val i := by
          apply Fin.ext
          simp only [oddAffineEvenVertex, oddAffinePivot, Fin.val_succ, ha₀]
        rw [hv, ha₀, oddAffine_pivot_entry A hA]
        simp

/-- Adding the head matrix changes the first isotropy equation by the
second component of the constant chart map. -/
theorem oddMatrixFirstPair_add_head {k r : ℕ} (h : r ≤ k)
    (A : Matrix (Fin (r+1)) (Fin (2*k+1)) R)
    (hA : A.submatrix id (oddAffinePivot k r h).val = 1)
    (T : Fin r → Fin (r+1) → R) (i j : Fin (r+1)) :
    oddMatrixFirstPair (A + oddAffineHeadMatrix k r T) i j =
      oddMatrixFirstPair A i j +
        (chartPad T (i.val+1) j.val - chartPad T (j.val+1) i.val) := by
  have he : oddMatrixFirstPair (A + oddAffineHeadMatrix k r T) i j =
      oddMatrixFirstPair A i j +
        ((∑ a : Fin k, A i (oddAffineEvenVertex k a.castSucc) * chartPad T (a.val+1) j.val) -
         (∑ a : Fin k, A j (oddAffineEvenVertex k a.castSucc) * chartPad T (a.val+1) i.val)) := by
    simp only [oddMatrixFirstPair, Matrix.add_apply, oddAffineHeadMatrix_even,
      oddAffineHeadMatrix_odd, add_zero, ← Finset.sum_sub_distrib,
      ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro a ha
    ring
  rw [he, oddAffine_first_product_sum h A hA, oddAffine_first_product_sum h A hA]

/-- Adding the head matrix changes the second equation by minus the first
component of the same constant chart map. -/
theorem oddMatrixSecondPair_add_head {k r : ℕ} (h : r ≤ k)
    (A : Matrix (Fin (r+1)) (Fin (2*k+1)) R)
    (hA : A.submatrix id (oddAffinePivot k r h).val = 1)
    (T : Fin r → Fin (r+1) → R) (i j : Fin (r+1)) :
    oddMatrixSecondPair (A + oddAffineHeadMatrix k r T) i j =
      oddMatrixSecondPair A i j +
        (chartPad T j.val i.val - chartPad T i.val j.val) := by
  have he : oddMatrixSecondPair (A + oddAffineHeadMatrix k r T) i j =
      oddMatrixSecondPair A i j +
        ((∑ a : Fin k, A j (oddAffineEvenVertex k a.succ) * chartPad T (a.val+1) i.val) -
         (∑ a : Fin k, A i (oddAffineEvenVertex k a.succ) * chartPad T (a.val+1) j.val)) := by
    simp only [oddMatrixSecondPair, Matrix.add_apply, oddAffineHeadMatrix_even,
      oddAffineHeadMatrix_odd, add_zero, ← Finset.sum_sub_distrib,
      ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro a ha
    ring
  rw [he, oddAffine_second_product_sum h A hA, oddAffine_second_product_sum h A hA]

end PaperVerification.AlternatingForms
