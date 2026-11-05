module

public import PaperVerification.DeterminantDerivation
public import Mathlib.Algebra.MvPolynomial.Derivation
public import Mathlib.Data.Fintype.Sum
public import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
public import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

/-!
# Universal determinant vectors for two Boolean derivatives

For an odd set of columns of size 2r+1, the determinant has r variable rows
and r+1 constant rows. Both directional derivatives replace a variable row
by one of its adjacent constant rows. The determinant therefore lies in the
joint kernel over every commutative coefficient ring.

These are explicit vectors, not generators assumed from an invariant-ring
presentation. Their independence and comparison with the actual Boolean
quotient are separate obligations.
-/

@[expose] public section
noncomputable section

set_option autoImplicit false

namespace PaperVerification.AlternatingForms.EvenDeterminants

open scoped BigOperators
open MvPolynomial

variable {K α : Type*} [CommRing K]

/-- The constant rows are indexed by the left summand and the variable rows
by the right summand. Their interleaved order is used only for leading terms. -/
abbrev OddRows (r : ℕ) := Fin (r + 1) ⊕ Fin r

/-- The actual derivation taking each variable y_i to the specified scalar. -/
def directionalDerivative (b : α → K) :
    Derivation K (MvPolynomial α K) (MvPolynomial α K) :=
  MvPolynomial.mkDerivation K (fun i => C (b i))

@[simp] theorem directionalDerivative_X (b : α → K) (i : α) :
    directionalDerivative b (X i) = C (b i) :=
  MvPolynomial.mkDerivation_X _ _ i

/-- The odd-subset determinant matrix after setting all auxiliary x_i to one. -/
def oddSubsetMatrix (r : ℕ) (b c : α → K) (a : OddRows r → α) :
    Matrix (OddRows r) (OddRows r) (MvPolynomial α K) :=
  Matrix.of fun row col =>
    match row with
    | Sum.inl i => C (b (a col) ^ (r - i.val) * c (a col) ^ i.val)
    | Sum.inr i => C (b (a col) ^ (r - 1 - i.val) * c (a col) ^ i.val) * X (a col)

@[simp] theorem oddSubsetMatrix_even (r : ℕ) (b c : α → K)
    (a : OddRows r → α) (i : Fin (r + 1)) (j : OddRows r) :
    oddSubsetMatrix r b c a (Sum.inl i) j =
      C (b (a j) ^ (r - i.val) * c (a j) ^ i.val) := rfl

@[simp] theorem oddSubsetMatrix_odd (r : ℕ) (b c : α → K)
    (a : OddRows r → α) (i : Fin r) (j : OddRows r) :
    oddSubsetMatrix r b c a (Sum.inr i) j =
      C (b (a j) ^ (r - 1 - i.val) * c (a j) ^ i.val) * X (a j) := rfl

/-- The universal multiaffine determinant vector attached to the selected columns. -/
def oddSubsetDeterminant (r : ℕ) (b c : α → K) (a : OddRows r → α) :
    MvPolynomial α K :=
  (oddSubsetMatrix r b c a).det

@[simp] theorem derivative_first_even (r : ℕ) (b c : α → K)
    (a : OddRows r → α) (i : Fin (r + 1)) (j : OddRows r) :
    directionalDerivative b (oddSubsetMatrix r b c a (Sum.inl i) j) = 0 := by
  simp

@[simp] theorem derivative_second_even (r : ℕ) (b c : α → K)
    (a : OddRows r → α) (i : Fin (r + 1)) (j : OddRows r) :
    directionalDerivative c (oddSubsetMatrix r b c a (Sum.inl i) j) = 0 := by
  simp

theorem derivative_first_odd (r : ℕ) (b c : α → K)
    (a : OddRows r → α) (i : Fin r) (j : OddRows r) :
    directionalDerivative b (oddSubsetMatrix r b c a (Sum.inr i) j) =
      oddSubsetMatrix r b c a (Sum.inl i.castSucc) j := by
  have hexp : r - i.val = (r - 1 - i.val) + 1 := by omega
  simp only [oddSubsetMatrix_odd, oddSubsetMatrix_even, Derivation.leibniz,
    MvPolynomial.derivation_C, directionalDerivative_X, smul_zero, add_zero,
    smul_eq_mul, ← MvPolynomial.C_mul, Fin.val_castSucc]
  congr 1
  rw [hexp, pow_succ]
  ring

theorem derivative_second_odd (r : ℕ) (b c : α → K)
    (a : OddRows r → α) (i : Fin r) (j : OddRows r) :
    directionalDerivative c (oddSubsetMatrix r b c a (Sum.inr i) j) =
      oddSubsetMatrix r b c a (Sum.inl i.succ) j := by
  have hexp : r - 1 - i.val = r - (i.val + 1) := by omega
  simp only [oddSubsetMatrix_odd, oddSubsetMatrix_even, Derivation.leibniz,
    MvPolynomial.derivation_C, directionalDerivative_X, smul_zero, add_zero,
    smul_eq_mul, ← MvPolynomial.C_mul, Fin.val_succ]
  congr 1
  rw [hexp, pow_succ]
  ring

/-- The first literal Boolean directional derivative kills the determinant. -/
theorem oddSubsetDeterminant_first_kernel (r : ℕ) (b c : α → K)
    (a : OddRows r → α) :
    directionalDerivative b (oddSubsetDeterminant r b c a) = 0 := by
  classical
  rw [oddSubsetDeterminant,
    PaperVerification.DeterminantDerivation.derivation_det_rows]
  apply Finset.sum_eq_zero
  intro row hrow
  cases row with
  | inl i =>
    apply Matrix.det_eq_zero_of_row_eq_zero (Sum.inl i)
    intro j
    rw [Matrix.updateRow_self, derivative_first_even]
  | inr i =>
    have hrow :
        (fun j => directionalDerivative b (oddSubsetMatrix r b c a (Sum.inr i) j)) =
          oddSubsetMatrix r b c a (Sum.inl i.castSucc) :=
      funext (derivative_first_odd r b c a i)
    rw [hrow]
    exact Matrix.det_updateRow_eq_zero (Sum.inl_ne_inr)

/-- The second literal Boolean directional derivative kills the determinant. -/
theorem oddSubsetDeterminant_second_kernel (r : ℕ) (b c : α → K)
    (a : OddRows r → α) :
    directionalDerivative c (oddSubsetDeterminant r b c a) = 0 := by
  classical
  rw [oddSubsetDeterminant,
    PaperVerification.DeterminantDerivation.derivation_det_rows]
  apply Finset.sum_eq_zero
  intro row hrow
  cases row with
  | inl i =>
    apply Matrix.det_eq_zero_of_row_eq_zero (Sum.inl i)
    intro j
    rw [Matrix.updateRow_self, derivative_second_even]
  | inr i =>
    have hrow :
        (fun j => directionalDerivative c (oddSubsetMatrix r b c a (Sum.inr i) j)) =
          oddSubsetMatrix r b c a (Sum.inl i.succ) :=
      funext (derivative_second_odd r b c a i)
    rw [hrow]
    exact Matrix.det_updateRow_eq_zero (Sum.inl_ne_inr)

/-- Products of these explicit determinants remain in the same joint kernel. -/
theorem determinant_product_joint_kernel {ι : Type*} (s : Finset ι)
    (r : ι → ℕ) (b c : α → K) (a : (i : ι) → OddRows (r i) → α) :
    directionalDerivative b (∏ i ∈ s, oddSubsetDeterminant (r i) b c (a i)) = 0 ∧
    directionalDerivative c (∏ i ∈ s, oddSubsetDeterminant (r i) b c (a i)) = 0 := by
  classical
  constructor
  · rw [PaperVerification.DeterminantDerivation.derivation_finset_prod]
    simp only [oddSubsetDeterminant_first_kernel, zero_mul, Finset.sum_const_zero]
  · rw [PaperVerification.DeterminantDerivation.derivation_finset_prod]
    simp only [oddSubsetDeterminant_second_kernel, zero_mul, Finset.sum_const_zero]

end PaperVerification.AlternatingForms.EvenDeterminants

