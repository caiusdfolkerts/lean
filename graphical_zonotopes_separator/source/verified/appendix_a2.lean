module

public import verified.extensions
import all verified.extensions
import all verified.main
public import Mathlib.LinearAlgebra.Matrix.ConjTranspose
public import Mathlib.Basic.Complex.BigOperators
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.SplitIfs
public import Mathlib.Algebra.MvPolynomial.CommRing
public import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
public import Mathlib.RingTheory.MvPolynomial.Homogeneous
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Data.Fin.SuccPred
public import Mathlib.Algebra.MvPolynomial.NoZeroDivisors
public import Mathlib.Algebra.Polynomial.RingDivision
public import Mathlib.RingTheory.Polynomial.UniqueFactorization
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

@[expose] public section

set_option debug.skipKernelTC false
set_option linter.all false
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 4000000

section AppendixA2Part0
/- Source: Correspondence/AppendixPathMatrix.lean -/







/-! # The grouped incidence matrix in Appendix A

There are `m` spoke columns and `m+1` path columns, including the two endpoint
columns. All indexing is zero based. The variable attached to a spoke `i` is
`t_(i+2)`; the variable attached to a path column `j` is `t_j`.
-/

@[expose] public section
noncomputable section
open scoped BigOperators Matrix
open Finset Matrix

namespace GraphicalZonotopes.PathDeterminant

variable {R : Type*} [CommRing R]

abbrev Edge (m : ℕ) := Fin m ⊕ Fin (m+1)

/-- Rows are the transposes of the reduced incidence columns. -/
def incidence (m : ℕ) : Matrix (Edge m) (Fin m) R
  | Sum.inl j, i => if j = i then 1 else 0
  | Sum.inr j, i => (if j = i.succ then 1 else 0) -
      (if j = i.castSucc then 1 else 0)

def group (m : ℕ) : Edge m → Fin (m+2)
  | Sum.inl i => i.succ.succ
  | Sum.inr i => i.castSucc

/-- The matrix of Proposition A.2: diagonal `t_i+t_(i+1)+t_(i+2)`;
the adjacent entries are `-t_(i+1)`. The expression by Kronecker deltas
avoids separate conventions at the two ends of the path. -/
def tridiagonal {m : ℕ} (t : Fin (m+2) → R) : Matrix (Fin m) (Fin m) R :=
  fun i j =>
    (if i = j then t i.castSucc.castSucc + t i.succ.castSucc + t i.succ.succ else 0) -
    (if i.succ = j.castSucc then t i.succ.castSucc else 0) -
    (if j.succ = i.castSucc then t i.castSucc.castSucc else 0)

@[simp] theorem tridiagonal_diag {m : ℕ} (t : Fin (m+2) → R) (i : Fin m) :
    tridiagonal t i i = t i.castSucc.castSucc + t i.succ.castSucc + t i.succ.succ := by
  have hi : i.succ ≠ i.castSucc := by
    intro h
    have := congrArg Fin.val h
    simp only [Fin.val_succ,Fin.val_castSucc] at this
    omega
  simp [tridiagonal,hi]

theorem tridiagonal_above {m : ℕ} (t : Fin (m+2) → R) (i j : Fin m)
    (hij : i.val+1 = j.val) : tridiagonal t i j = -t i.succ.castSucc := by
  have hne : i ≠ j := by intro h; subst j; omega
  have hs : i.succ = j.castSucc := Fin.ext hij
  have hn : j.succ ≠ i.castSucc := by
    intro h
    have := congrArg Fin.val h
    simp only [Fin.val_succ,Fin.val_castSucc] at this
    omega
  simp [tridiagonal,hne,hs,hn]

theorem tridiagonal_below {m : ℕ} (t : Fin (m+2) → R) (i j : Fin m)
    (hij : j.val+1 = i.val) : tridiagonal t i j = -t j.succ.castSucc := by
  have hne : i ≠ j := by intro h; subst j; omega
  have hs : j.succ = i.castSucc := Fin.ext hij
  have hn : i.succ ≠ j.castSucc := by
    intro h
    have := congrArg Fin.val h
    simp only [Fin.val_succ,Fin.val_castSucc] at this
    omega
  have ht : i.castSucc.castSucc = j.succ.castSucc := Fin.ext hij.symm
  simp [tridiagonal,hne,hs,hn,ht]

theorem tridiagonal_off_band {m : ℕ} (t : Fin (m+2) → R) (i j : Fin m)
    (hne : i ≠ j) (habove : i.val+1 ≠ j.val) (hbelow : j.val+1 ≠ i.val) :
    tridiagonal t i j = 0 := by
  have ha : i.succ ≠ j.castSucc := fun h => habove (congrArg Fin.val h)
  have hb : j.succ ≠ i.castSucc := fun h => hbelow (congrArg Fin.val h)
  simp [tridiagonal,hne,ha,hb]

/-- Every coordinate is read by its spoke row, so the incidence map has
trivial kernel over every coefficient ring. -/
theorem incidence_mulVec_injective (m : ℕ) :
    Function.Injective (incidence (R := R) m).mulVec := by
  intro x y h
  funext i
  have hi := congrFun h (Sum.inl i)
  simpa [Matrix.mulVec,dotProduct,incidence] using hi

/-- The displayed tridiagonal matrix is exactly the weighted incidence Gram
matrix over every commutative ring. -/
theorem incidence_gram {m : ℕ} (t : Fin (m+2) → R) :
    (incidence m)ᵀ * diagonal (t ∘ group m) * incidence m = tridiagonal t := by
  ext i j
  rw [Matrix.mul_apply]
  simp only [Matrix.mul_diagonal,Matrix.transpose_apply,Fintype.sum_sum_type]
  simp [incidence,group,tridiagonal,mul_sub,sub_mul,
    Finset.sum_sub_distrib,ite_mul,mul_ite,Fin.castSucc_inj]
  split_ifs <;> simp_all <;> try ring
  · have hforward : i.succ = j.castSucc := by assumption
    have hbackward : j.succ = i.castSucc := by assumption
    have hv := congrArg Fin.val hforward
    have hw := congrArg Fin.val hbackward
    simp only [Fin.val_succ, Fin.val_castSucc] at hv hw
    omega
  · have hbackward : j.succ = i.castSucc := by assumption
    simpa only [Fin.castSucc_succ] using
      congrArg t (congrArg Fin.castSucc hbackward)
  · have hforward : i.succ = j.castSucc := by assumption
    simpa only [Fin.castSucc_succ] using
      (congrArg t (congrArg Fin.castSucc hforward)).symm

theorem incidence_conjTranspose (m : ℕ) :
    (incidence (R := ℂ) m)ᴴ = (incidence m)ᵀ := by
  ext i e
  cases e <;> simp [Matrix.conjTranspose_apply,Matrix.transpose_apply,incidence]

end GraphicalZonotopes.PathDeterminant

end
end
end AppendixA2Part0

section AppendixA2Part1
/- Source: Correspondence/AppendixStability.lean -/







/-! # The upper-half-plane assertion in Proposition A.2

The determinant is the literal determinant of the displayed tridiagonal
matrix. Its nonvanishing follows from an injective weighted incidence map.
-/

@[expose] public section
noncomputable section
open scoped BigOperators Matrix
open Finset Matrix

namespace GraphicalZonotopes.PathDeterminant

variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]

/-- A weighted Gram form has the expected sum-of-squares expansion, even
when its weights are complex. -/
theorem weightedGram_quadratic (B : Matrix ι κ ℂ) (t : ι → ℂ) (x : κ → ℂ) :
    star x ⬝ᵥ ((Bᴴ * diagonal t * B) *ᵥ x) =
      ∑ i, t i * (Complex.normSq ((B *ᵥ x) i) : ℂ) := by
  calc
    _ = star (B *ᵥ x) ⬝ᵥ (diagonal t *ᵥ (B *ᵥ x)) := by
      rw [← mulVec_mulVec, ← mulVec_mulVec, dotProduct_mulVec,
        vecMul_conjTranspose]
      have hxstar : star (star x) = x := by
        funext k
        change star (star (x k)) = x k
        exact _root_.star_star (x k)
      rw [hxstar]
    _ = _ := by
      simp only [dotProduct, mulVec_diagonal, Pi.star_apply]
      apply Finset.sum_congr rfl
      intro i hi
      change star ((B *ᵥ x) i) * (t i * (B *ᵥ x) i) = _
      rw [mul_left_comm]
      simp only [Complex.star_def, ← Complex.normSq_eq_conj_mul_self]

/-- Positive imaginary weights make an injective weighted Gram matrix
nonsingular. The column-rank condition is an ordinary injectivity assertion.
-/
theorem weightedGram_det_ne_zero (B : Matrix ι κ ℂ)
    (hB : Function.Injective B.mulVec) (t : ι → ℂ)
    (ht : ∀ i, 0 < (t i).im) : (Bᴴ * diagonal t * B).det ≠ 0 := by
  intro hdet
  obtain ⟨x, hx, hker⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdet
  have hy : B *ᵥ x ≠ 0 := by
    intro h
    apply hx
    apply hB
    simpa only [mulVec_zero] using h
  obtain ⟨j, hj⟩ : ∃ j, (B *ᵥ x) j ≠ 0 := by
    by_contra h
    apply hy
    ext j
    exact not_not.mp (not_exists.mp h j)
  have hsum : (∑ i, t i * (Complex.normSq ((B *ᵥ x) i) : ℂ)) = 0 := by
    rw [← weightedGram_quadratic, hker, dotProduct_zero]
  have him : ∑ i, (t i).im * Complex.normSq ((B *ᵥ x) i) = 0 := by
    have h := congrArg Complex.im hsum
    simpa using h
  have hp : 0 < ∑ i, (t i).im * Complex.normSq ((B *ᵥ x) i) := by
    apply Finset.sum_pos'
    · intro i hi
      exact mul_nonneg (ht i).le (Complex.normSq_nonneg _)
    · exact ⟨j,mem_univ j,mul_pos (ht j) (Complex.normSq_pos.mpr hj)⟩
  exact (ne_of_gt hp) him

/-- The actual tridiagonal determinant is nonzero throughout the product
of open upper half planes, for every matrix size. -/
theorem tridiagonal_det_ne_zero (m : ℕ) (t : Fin (m+2) → ℂ)
    (ht : ∀ j, 0 < (t j).im) : (tridiagonal t).det ≠ 0 := by
  have h := weightedGram_det_ne_zero (incidence m)
    (incidence_mulVec_injective m) (t ∘ group m) (fun e => ht (group m e))
  rwa [incidence_conjTranspose,incidence_gram] at h

/-- The determinant polynomial in the paper's `m+2` independent variables. -/
def polynomial (R : Type*) [CommRing R] (m : ℕ) : MvPolynomial (Fin (m+2)) R :=
  (tridiagonal (fun j => MvPolynomial.X j)).det

/-- Real stability is stated directly by complex evaluation; there is no
finite sampling or additional spectral hypothesis in this predicate. -/
def IsRealStable {σ : Type*} (p : MvPolynomial σ ℝ) : Prop :=
  ∀ t : σ → ℂ, (∀ j, 0 < (t j).im) → MvPolynomial.eval₂ Complex.ofRealHom t p ≠ 0

theorem polynomial_eval (m : ℕ) (t : Fin (m+2) → ℂ) :
    MvPolynomial.eval₂ Complex.ofRealHom t (polynomial ℝ m) = (tridiagonal t).det := by
  change (MvPolynomial.eval₂Hom Complex.ofRealHom t)
    (tridiagonal (fun j => MvPolynomial.X j)).det = _
  rw [RingHom.map_det]
  congr 1
  ext i j
  simp only [RingHom.mapMatrix_apply, tridiagonal]
  split_ifs <;> simp_all [MvPolynomial.coe_eval₂Hom, tridiagonal,
    MvPolynomial.eval₂_sub, MvPolynomial.eval₂_add,
    MvPolynomial.eval₂_X, MvPolynomial.eval₂_zero]

theorem polynomial_realStable (m : ℕ) : IsRealStable (polynomial ℝ m) := by
  intro t ht
  rw [polynomial_eval]
  exact tridiagonal_det_ne_zero m t ht

variable {σ R : Type*} [CommRing R]

theorem homogeneous_det {m : ℕ}
    (M : Matrix (Fin m) (Fin m) (MvPolynomial σ R))
    (hM : ∀ i j, (M i j).IsHomogeneous 1) : M.det.IsHomogeneous m := by
  rw [Matrix.det_apply']
  apply MvPolynomial.IsHomogeneous.sum
  intro s hs
  have hp := MvPolynomial.IsHomogeneous.prod (univ : Finset (Fin m))
    (fun i => M (s i) i) (fun _ => 1) (fun i _ => hM (s i) i)
  have hp' : (∏ i, M (s i) i).IsHomogeneous m := by simpa using hp
  simpa only [map_intCast] using hp'.C_mul (((Equiv.Perm.sign s : ℤ) : R))

theorem polynomial_homogeneous (R : Type*) [CommRing R] (m : ℕ) :
    (polynomial R m).IsHomogeneous m := by
  apply homogeneous_det
  intro i j
  unfold tridiagonal
  apply MvPolynomial.IsHomogeneous.sub
  · apply MvPolynomial.IsHomogeneous.sub
    · split_ifs
      · exact ((MvPolynomial.isHomogeneous_X _ _).add
          (MvPolynomial.isHomogeneous_X _ _)).add (MvPolynomial.isHomogeneous_X _ _)
      · exact MvPolynomial.isHomogeneous_zero _ _ _
    · split_ifs
      · exact MvPolynomial.isHomogeneous_X _ _
      · exact MvPolynomial.isHomogeneous_zero _ _ _
  · split_ifs
    · exact MvPolynomial.isHomogeneous_X _ _
    · exact MvPolynomial.isHomogeneous_zero _ _ _

theorem polynomial_ne_zero (m : ℕ) : polynomial ℝ m ≠ 0 := by
  intro h
  have hs := polynomial_realStable m (fun _ => Complex.I) (fun _ => by simp)
  apply hs
  rw [h,MvPolynomial.eval₂_zero]

theorem polynomial_totalDegree (m : ℕ) : (polynomial ℝ m).totalDegree = m :=
  (polynomial_homogeneous ℝ m).totalDegree (polynomial_ne_zero m)

/-- The homogeneity, degree, and real-stability assertions of Proposition
A.2, for the literal determinant and with no restriction on its size.
The Newton-polytope and absolute-irreducibility assertions are separate.
-/
theorem proposition_A_2_stability (m : ℕ) :
    (polynomial ℝ m).IsHomogeneous m ∧
    (polynomial ℝ m).totalDegree = m ∧ IsRealStable (polynomial ℝ m) :=
  ⟨polynomial_homogeneous ℝ m,polynomial_totalDegree m,polynomial_realStable m⟩

end GraphicalZonotopes.PathDeterminant

end
end
end AppendixA2Part1

section AppendixA2Part2
/- Source: Correspondence/AppendixDeterminantRecurrence.lean -/







/-! # The literal tridiagonal determinant recurrence

This file proves the two-step determinant identity directly from the matrix
of Appendix A. No recurrence is used as the definition of the polynomial.
-/

@[expose] public section
noncomputable section
open scoped BigOperators Matrix
open Finset Matrix

namespace GraphicalZonotopes.PathDeterminant

variable {R : Type*} [CommRing R]

/-- Deleting the first row and column shifts the variable sequence by one. -/
theorem tridiagonal_tail {m : ℕ} (t : Fin (m+3) → R) :
    (tridiagonal t).submatrix Fin.succ Fin.succ =
      tridiagonal (fun j : Fin (m+2) => t j.succ) := by
  ext i j
  simp only [Matrix.submatrix_apply, tridiagonal, Fin.castSucc_succ, Fin.succ_inj]

/-- The entries of the first row beyond its two possible nonzero positions vanish. -/
theorem tridiagonal_zero_succ_succ {m : ℕ} (t : Fin (m+4) → R) (j : Fin m) :
    tridiagonal t 0 j.succ.succ = 0 := by
  apply tridiagonal_off_band
  · intro h
    have hv := congrArg Fin.val h
    simp only [Fin.val_zero, Fin.val_succ] at hv
    omega
  · simp only [Fin.val_zero, Fin.val_succ]
    omega
  · simp only [Fin.val_zero, Fin.val_succ]
    omega

/-- The corresponding entries of the first column vanish. -/
theorem tridiagonal_succ_succ_zero {m : ℕ} (t : Fin (m+4) → R) (i : Fin m) :
    tridiagonal t i.succ.succ 0 = 0 := by
  apply tridiagonal_off_band
  · intro h
    have hv := congrArg Fin.val h
    simp only [Fin.val_zero, Fin.val_succ] at hv
    omega
  · simp only [Fin.val_zero, Fin.val_succ]
    omega
  · simp only [Fin.val_zero, Fin.val_succ]
    omega

/-- Deleting the first two rows and columns shifts the variables twice. -/
theorem tridiagonal_tail_twice {m : ℕ} (t : Fin (m+4) → R) :
    (tridiagonal t).submatrix (fun i : Fin m => i.succ.succ)
        (fun j : Fin m => j.succ.succ) =
      tridiagonal (fun j : Fin (m+2) => t j.succ.succ) := by
  calc
    _ = ((tridiagonal t).submatrix Fin.succ Fin.succ).submatrix
        Fin.succ Fin.succ := rfl
    _ = _ := by rw [tridiagonal_tail, tridiagonal_tail]

/-- The other nonzero first-row cofactor has a first column with one
nonzero entry. Its determinant is therefore a smaller tridiagonal
determinant multiplied by the adjacent entry. -/
theorem tridiagonal_minor_one_det {m : ℕ} (t : Fin (m+4) → R) :
    ((tridiagonal t).submatrix Fin.succ (0 : Fin (m+1)).succ.succAbove).det =
      -t 1 * (tridiagonal (fun j : Fin (m+2) => t j.succ.succ)).det := by
  let N : Matrix (Fin (m+1)) (Fin (m+1)) R :=
    (tridiagonal t).submatrix Fin.succ (0 : Fin (m+1)).succ.succAbove
  change N.det = _
  have h00 : N 0 0 = -t 1 := by
    change tridiagonal t (0 : Fin (m+1)).succ
      ((0 : Fin (m+1)).succ.succAbove 0) = _
    rw [Fin.succ_succAbove_zero]
    simpa using tridiagonal_below t (0 : Fin (m+1)).succ 0 (by simp)
  have hzero : ∀ i : Fin m, N i.succ 0 = 0 := by
    intro i
    change tridiagonal t i.succ.succ
      ((0 : Fin (m+1)).succ.succAbove 0) = 0
    rw [Fin.succ_succAbove_zero]
    exact tridiagonal_succ_succ_zero t i
  have htail : N.submatrix Fin.succ Fin.succ =
      tridiagonal (fun j : Fin (m+2) => t j.succ.succ) := by
    ext i j
    change tridiagonal t i.succ.succ
      ((0 : Fin (m+1)).succ.succAbove j.succ) = _
    rw [Fin.succ_succAbove_succ, Fin.zero_succAbove]
    exact congrFun (congrFun (tridiagonal_tail_twice t) i) j
  rw [Matrix.det_succ_column_zero, Fin.sum_univ_succ]
  simp only [Fin.val_zero, pow_zero, one_mul, Fin.succAbove_zero,
    hzero, mul_zero, zero_mul, Finset.sum_const_zero, add_zero]
  rw [h00, htail]

/-- The characteristic-independent continuant identity for the exact matrix. -/
theorem tridiagonal_det_recurrence {m : ℕ} (t : Fin (m+4) → R) :
    (tridiagonal t).det =
      (t 0 + t 1 + t 2) *
        (tridiagonal (fun j : Fin (m+3) => t j.succ)).det -
      (t 1)^2 *
        (tridiagonal (fun j : Fin (m+2) => t j.succ.succ)).det := by
  have hdiag : tridiagonal t 0 0 = t 0 + t 1 + t 2 := by
    simpa using tridiagonal_diag t 0
  have hnext : tridiagonal t 0 (0 : Fin (m+1)).succ = -t 1 := by
    simpa using tridiagonal_above t 0 (0 : Fin (m+1)).succ (by simp)
  rw [Matrix.det_succ_row_zero, Fin.sum_univ_succ, Fin.sum_univ_succ]
  simp only [Fin.val_zero, Fin.val_succ, Nat.zero_add, pow_zero, pow_one,
    one_mul, Fin.succAbove_zero, tridiagonal_zero_succ_succ,
    mul_zero, zero_mul, Finset.sum_const_zero, add_zero]
  rw [hdiag, hnext, tridiagonal_tail, tridiagonal_minor_one_det]
  ring

end GraphicalZonotopes.PathDeterminant

end
end
end AppendixA2Part2

section AppendixA2Part3
/- Source: Correspondence/AppendixIrreducibility.lean -/









/-! # Absolute irreducibility of the tridiagonal determinant

The determinant is first regarded as a polynomial in its first variable.
Its leading and constant coefficients are relatively prime over every
field. The proof treats positive matrix sizes; the zero-size determinant
is the unit polynomial and is not asserted to be irreducible.
-/

@[expose] public section
noncomputable section
open scoped BigOperators Matrix
open Finset Matrix
open MvPolynomial

namespace GraphicalZonotopes.PathDeterminant

section Ring

variable {R S : Type*} [CommRing R] [CommRing S]

/-- Evaluation commutes with the literal matrix determinant. -/
theorem polynomial_eval₂ (m : ℕ) (f : R →+* S) (t : Fin (m+2) → S) :
    MvPolynomial.eval₂ f t (polynomial R m) = (tridiagonal t).det := by
  change (MvPolynomial.eval₂Hom f t)
    (tridiagonal (fun j => MvPolynomial.X j)).det = _
  rw [RingHom.map_det]
  congr 1
  ext i j
  simp only [RingHom.mapMatrix_apply, tridiagonal]
  split_ifs <;> simp_all [MvPolynomial.coe_eval₂Hom, tridiagonal,
    MvPolynomial.eval₂_sub, MvPolynomial.eval₂_add,
    MvPolynomial.eval₂_X, MvPolynomial.eval₂_zero]

/-- Renaming the variables does not change the determinant construction. -/
theorem polynomial_rename {σ : Type*} {m : ℕ} (f : Fin (m+2) → σ) :
    MvPolynomial.rename f (polynomial R m) =
      (tridiagonal (fun j => MvPolynomial.X (f j))).det := by
  unfold polynomial
  rw [AlgHom.map_det]
  congr 1
  ext i j
  simp only [AlgHom.mapMatrix_apply, tridiagonal]
  split_ifs <;> simp_all [tridiagonal]

/-- Scalar extension is the ordinary coefficient map on this polynomial. -/
theorem polynomial_map (m : ℕ) (f : R →+* S) :
    MvPolynomial.map f (polynomial R m) = polynomial S m := by
  unfold polynomial
  rw [RingHom.map_det]
  congr 1
  ext i j
  simp only [RingHom.mapMatrix_apply, tridiagonal]
  split_ifs <;> simp_all [tridiagonal]

@[simp] theorem polynomial_zero (R : Type*) [CommRing R] :
    polynomial R 0 = 1 := by
  simp [polynomial]

theorem polynomial_one (R : Type*) [CommRing R] :
    polynomial R 1 = X 0 + X 1 + X 2 := by
  unfold polynomial
  rw [Matrix.det_fin_one]
  simpa using tridiagonal_diag (fun j : Fin 3 => (X j : MvPolynomial (Fin 3) R)) 0

/-- The matrix recurrence expressed in the original multivariate ring. -/
theorem polynomial_recurrence (R : Type*) [CommRing R] (m : ℕ) :
    polynomial R (m+2) =
      (X 0 + X 1 + X 2) *
        MvPolynomial.rename Fin.succ (polynomial R (m+1)) -
      (X 1)^2 *
        MvPolynomial.rename (fun j : Fin (m+2) => j.succ.succ) (polynomial R m) := by
  rw [polynomial_rename, polynomial_rename]
  exact tridiagonal_det_recurrence
    (fun j : Fin (m+4) => (X j : MvPolynomial (Fin (m+4)) R))

/-- A polynomial in the tail variables becomes a constant under
the equivalence separating the first variable. -/
theorem finSuccEquiv_rename_succ {n : ℕ} (p : MvPolynomial (Fin n) R) :
    MvPolynomial.finSuccEquiv R n (MvPolynomial.rename Fin.succ p) =
      Polynomial.C p := by
  induction p using MvPolynomial.induction_on with
  | C a =>
      simp [MvPolynomial.rename_C, MvPolynomial.finSuccEquiv_apply]
  | add p q hp hq =>
      simp only [map_add, hp, hq]
  | mul_X p j hp =>
      simp only [map_mul, MvPolynomial.rename_X,
        MvPolynomial.finSuccEquiv_X_succ, hp]

/-- The constant coefficient after the first variable is separated.
The following theorem proves its connection with the actual determinant. -/
def constantCoefficient (R : Type*) [CommRing R] (m : ℕ) :
    MvPolynomial (Fin (m+3)) R :=
  (X 0 + X 1) * polynomial R (m+1) -
    (X 0)^2 * MvPolynomial.rename Fin.succ (polynomial R m)

theorem finSuccEquiv_polynomial_one (R : Type*) [CommRing R] :
    MvPolynomial.finSuccEquiv R 2 (polynomial R 1) =
      Polynomial.X + Polynomial.C (X 0 + X 1) := by
  rw [polynomial_one]
  change (MvPolynomial.finSuccEquiv R 2)
    (X 0 + X (0 : Fin 2).succ + X (1 : Fin 2).succ) = _
  simp only [map_add, MvPolynomial.finSuccEquiv_X_zero,
    MvPolynomial.finSuccEquiv_X_succ, add_assoc]

/-- The exact primitive-linear form used in the irreducibility induction. -/
theorem finSuccEquiv_polynomial_succ_succ (R : Type*) [CommRing R] (m : ℕ) :
    MvPolynomial.finSuccEquiv R (m+3) (polynomial R (m+2)) =
      Polynomial.C (polynomial R (m+1)) * Polynomial.X +
        Polynomial.C (constantCoefficient R m) := by
  have hdouble :
      MvPolynomial.rename (fun j : Fin (m+2) => j.succ.succ) (polynomial R m) =
        MvPolynomial.rename (Fin.succ : Fin (m+3) → Fin (m+4))
          (MvPolynomial.rename Fin.succ (polynomial R m)) := by
    simp only [MvPolynomial.rename_rename, Function.comp_def]
  have h1 : (1 : Fin (m+4)) = (0 : Fin (m+3)).succ := rfl
  have h2 : (2 : Fin (m+4)) = (1 : Fin (m+3)).succ := rfl
  rw [polynomial_recurrence, hdouble, h1, h2]
  simp only [constantCoefficient, map_sub, map_mul, map_add, map_pow,
    MvPolynomial.finSuccEquiv_X_zero, MvPolynomial.finSuccEquiv_X_succ,
    finSuccEquiv_rename_succ]
  ring

theorem polynomial_first_coefficient (R : Type*) [CommRing R] (m : ℕ) :
    (MvPolynomial.finSuccEquiv R (m+3) (polynomial R (m+2))).coeff 1 =
      polynomial R (m+1) := by
  rw [finSuccEquiv_polynomial_succ_succ]
  simp [Polynomial.coeff_C_mul_X]

theorem polynomial_constant_coefficient (R : Type*) [CommRing R] (m : ℕ) :
    (MvPolynomial.finSuccEquiv R (m+3) (polynomial R (m+2))).coeff 0 =
      constantCoefficient R m := by
  rw [finSuccEquiv_polynomial_succ_succ]
  simp [Polynomial.coeff_C_mul_X]

/-- This specialization kills the first matrix row in every characteristic. -/
def singularWeights (R : Type*) [CommRing R] (m : ℕ) : Fin (m+3) → R :=
  fun j => if j.val = 0 then 1 else if j.val = 2 then -1 else 0

theorem singularWeights_first_row (R : Type*) [CommRing R] (m : ℕ) (j : Fin (m+1)) :
    tridiagonal (singularWeights R m) 0 j = 0 := by
  have hbelow : j.succ ≠ (0 : Fin (m+1)).castSucc := by
    intro h
    have hv := congrArg Fin.val h
    simp only [Fin.val_succ, Fin.val_castSucc, Fin.val_zero] at hv
    omega
  have htwo : 2 < m + 3 := by omega
  simp [tridiagonal, singularWeights, hbelow, Nat.mod_eq_of_lt htwo]

end Ring

section Field

variable (K : Type*) [Field K]

/-- The determinant cannot disappear on reducing coefficients in any characteristic. -/
theorem polynomial_ne_zero_field (m : ℕ) : polynomial K m ≠ 0 := by
  have hpos : ∀ k, polynomial K (k+1) ≠ 0 := by
    intro k
    induction k with
    | zero =>
        intro hz
        have hcoef :
            (MvPolynomial.finSuccEquiv K 2 (polynomial K 1)).coeff 1 = 1 := by
          rw [finSuccEquiv_polynomial_one]
          simp
        rw [hz, map_zero, Polynomial.coeff_zero] at hcoef
        exact zero_ne_one hcoef
    | succ k ih =>
        intro hz
        have hcoef := polynomial_first_coefficient K k
        rw [hz, map_zero, Polynomial.coeff_zero] at hcoef
        exact ih hcoef.symm
  cases m with
  | zero => simp
  | succ m => exact hpos m

theorem polynomial_totalDegree_field (m : ℕ) :
    (polynomial K m).totalDegree = m :=
  (polynomial_homogeneous K m).totalDegree (polynomial_ne_zero_field K m)

/-- Uniformly in the size and characteristic, the determinant cannot divide
its first variable. Evaluating at (1,0,-1,0,...) turns such divisibility
into the impossible statement that zero divides one. -/
theorem polynomial_not_dvd_first_variable (m : ℕ) :
    ¬ polynomial K (m+1) ∣ (X 0 : MvPolynomial (Fin (m+3)) K) := by
  intro h
  let v := singularWeights K m
  have hd := map_dvd (MvPolynomial.eval v) h
  have hz : MvPolynomial.eval v (polynomial K (m+1)) = 0 := by
    change MvPolynomial.eval₂ (RingHom.id K) v (polynomial K (m+1)) = 0
    rw [polynomial_eval₂]
    exact Matrix.det_eq_zero_of_row_eq_zero 0 (singularWeights_first_row K m)
  have hx : MvPolynomial.eval v (X 0) = 1 := by
    simp [v, singularWeights]
  rw [hz, hx] at hd
  exact one_ne_zero (zero_dvd_iff.mp hd)

/-- The two coefficients of the primitive-linear form have no common nonunit divisor. -/
theorem polynomial_isRelPrime_constantCoefficient (m : ℕ)
    (hA : Irreducible (polynomial K (m+1))) :
    IsRelPrime (polynomial K (m+1)) (constantCoefficient K m) := by
  apply hA.isRelPrime_iff_not_dvd.mpr
  intro hdiv
  have hp : Prime (polynomial K (m+1)) :=
    UniqueFactorizationMonoid.irreducible_iff_prime.mp hA
  have hCne :
      MvPolynomial.rename (Fin.succ : Fin (m+2) → Fin (m+3))
        (polynomial K m) ≠ 0 := by
    intro h
    apply polynomial_ne_zero_field K m
    exact (MvPolynomial.rename_eq_zero_iff_of_injective _ (Fin.succ_injective _)).mp h
  have hCdeg :
      (MvPolynomial.rename (Fin.succ : Fin (m+2) → Fin (m+3))
        (polynomial K m)).totalDegree ≤ m := by
    calc
      _ ≤ (polynomial K m).totalDegree :=
        MvPolynomial.totalDegree_rename_le _ _
      _ = m := polynomial_totalDegree_field K m
  have hnotC : ¬ polynomial K (m+1) ∣
      MvPolynomial.rename (Fin.succ : Fin (m+2) → Fin (m+3)) (polynomial K m) := by
    intro h
    have hd := MvPolynomial.totalDegree_le_of_dvd_of_isDomain h hCne
    rw [polynomial_totalDegree_field] at hd
    omega
  have hmul : polynomial K (m+1) ∣
      (X 0 + X 1) * polynomial K (m+1) :=
    ⟨X 0 + X 1, mul_comm _ _⟩
  have hprod : polynomial K (m+1) ∣
      (X 0)^2 * MvPolynomial.rename Fin.succ (polynomial K m) := by
    have hd := dvd_sub hmul hdiv
    have heq :
        (X 0 + X 1) * polynomial K (m+1) - constantCoefficient K m =
          (X 0)^2 * MvPolynomial.rename Fin.succ (polynomial K m) := by
      unfold constantCoefficient
      ring
    rwa [heq] at hd
  rcases hp.dvd_mul.mp hprod with hpow | hC
  · exact polynomial_not_dvd_first_variable K m (hp.dvd_of_dvd_pow hpow)
  · exact hnotC hC

/-- Irreducibility of the exact determinant over every field, at every positive size. -/
theorem polynomial_irreducible (m : ℕ) : Irreducible (polynomial K (m+1)) := by
  induction m with
  | zero =>
      apply (MulEquiv.irreducible_iff (MvPolynomial.finSuccEquiv K 2)).mp
      rw [finSuccEquiv_polynomial_one]
      have hrel : IsRelPrime (1 : MvPolynomial (Fin 2) K) (X 0 + X 1) := by
        intro d hd _
        exact isUnit_of_dvd_one hd
      simpa using Polynomial.irreducible_C_mul_X_add_C
        (a := (1 : MvPolynomial (Fin 2) K)) (b := X 0 + X 1) one_ne_zero hrel
  | succ m ih =>
      apply (MulEquiv.irreducible_iff (MvPolynomial.finSuccEquiv K (m+3))).mp
      rw [finSuccEquiv_polynomial_succ_succ]
      exact Polynomial.irreducible_C_mul_X_add_C
        (polynomial_ne_zero_field K (m+1))
        (polynomial_isRelPrime_constantCoefficient K m ih)

/-- Irreducibility after every coefficient homomorphism into a field. -/
theorem polynomial_irreducible_map {L : Type*} [Field L] (f : K →+* L) (m : ℕ) :
    Irreducible (MvPolynomial.map f (polynomial K (m+1))) := by
  rw [polynomial_map]
  exact polynomial_irreducible L m

/-- Absolute irreducibility in Proposition A.2, stated explicitly as
irreducibility after extending scalars to an algebraic closure. -/
theorem proposition_A_2_absoluteIrreducible (m : ℕ) (hm : 0 < m) :
    Irreducible (MvPolynomial.map (algebraMap K (AlgebraicClosure K)) (polynomial K m)) := by
  cases m with
  | zero => omega
  | succ m =>
      exact polynomial_irreducible_map K (algebraMap K (AlgebraicClosure K)) m

end Field

end GraphicalZonotopes.PathDeterminant

end
end
end AppendixA2Part3

#print_proof_audit_bundle [
  GraphicalZonotopes.Path.principal_path_theorem,
  GraphicalZonotopes.Path.polytope_defining_equations,
  GraphicalZonotopes.Path.polytope_defining_equations_real,
  GraphicalZonotopes.Path.polytope_defining_equations_sums,
  GraphicalZonotopes.Path.setFunction_expansion,
  GraphicalZonotopes.Path.every_exposed_edge_is_graph_direction,
  GraphicalZonotopes.generalizedPermutahedron_iff_weak_complete,
  GraphicalZonotopes.minkowskiIndecomposable_iff_polytopal,
  GraphicalZonotopes.sharp_direction_bounds,
  GraphicalZonotopes.generalizedPermutahedron_exposed_edge_is_root,
  GraphicalZonotopes.root_parallel_pair_eq,
  GraphicalZonotopes.direction_bounds_polytopal,
  GraphicalZonotopes.ExtremeSupermodular.spanning_tetrahedra,
  GraphicalZonotopes.edge_bound_of_connected_tetrahedra,
  GraphicalZonotopes.maximum_degree_bound_of_connected_tetrahedra,
  GraphicalZonotopes.Path.setFunction_eq_booleanFormula,
  GraphicalZonotopes.Path.polytope_boolean_defining_equations,
  GraphicalZonotopes.DoubledParts.principal_boolean_phase_theorem,
  GraphicalZonotopes.BooleanFourier.boolean_face_line,
  GraphicalZonotopes.BooleanFourier.faceKernel_finrank,
  GraphicalZonotopes.threeTree_classification_polytopal,
  GraphicalZonotopes.threeTree_classification,
  GraphicalZonotopes.threeTree_classification_literal,
  GraphicalZonotopes.admissible_threeTree_lattice_witness,
  GraphicalZonotopes.threeTree_lattice_dilation_sharp,
  GraphicalZonotopes.threeTree_lattice_lower_bound_polytopal,
  GraphicalZonotopes.Separator.induced_separator_capacity_finite,
  GraphicalZonotopes.Separator.positive_response_gluing_finite,
  GraphicalZonotopes.Separator.clique_separator_capacity_finite,
  GraphicalZonotopes.unit_lattice_classification_sharp,
  GraphicalZonotopes.unit_lattice_classification_polytopal,
  GraphicalZonotopes.unit_translated_lattice_classification_polytopal,
  GraphicalZonotopes.threeTree_translated_lattice_lower_bound,
  GraphicalZonotopes.FourPartCompletion.cartesian_completion,
  GraphicalZonotopes.four_partite_spanning_threeTrees,
  GraphicalZonotopes.four_partite_threeTree_dimension_attained,
  GraphicalZonotopes.threeTree_actual_dimension_admissible,
  GraphicalZonotopes.admissible_threeTree_active_witness,
  GraphicalZonotopes.maximumThreeTreeSupportDimension_eq_polytopal,
  GraphicalZonotopes.optimal_k5_free_dilation,
  GraphicalZonotopes.optimal_k5_free_dilation_attained,
  GraphicalZonotopes.optimal_k5_free_dilation_lower_bound_polytopal,
  GraphicalZonotopes.DoubledParts.one_singleton_decomposition,
  GraphicalZonotopes.FourSmallParts.four_small_parts_decomposition,
  GraphicalZonotopes.boolean_decomposition_every_dimension,
  GraphicalZonotopes.BooleanModule.small_count_lattice_books,
  GraphicalZonotopes.BooleanModule.one_outer_lattice_book,
  GraphicalZonotopes.BooleanModule.small_count_lattice_books_literal,
  GraphicalZonotopes.DiamondBook.paper_theorem_8_1_literal,
  GraphicalZonotopes.DiamondBook.paper_theorem_8_1,
  GraphicalZonotopes.DiamondBook.maximum_dimension,
  GraphicalZonotopes.DiamondBook.diamond_witness_multipartite,
  GraphicalZonotopes.DiamondBook.no_supporting_spanning_threeTree,
  GraphicalZonotopes.BooleanModule.positive_star_interpolation,
  GraphicalZonotopes.BooleanModule.negative_star_interpolation,
  GraphicalZonotopes.BooleanModule.threshold_book_interval,
  GraphicalZonotopes.BooleanModule.book_upper_interval,
  GraphicalZonotopes.maximumIndecomposableDimension_eq_polytopal,
  GraphicalZonotopes.DiamondBook.paper_theorem_8_1_polytopal,
  GraphicalZonotopes.not_fullLatticeSummandAt_zero,
  GraphicalZonotopes.PathJoin.corollary_nine_four,
  GraphicalZonotopes.PathJoin.appendix_B_one,
  GraphicalZonotopes.clique_book_classification,
  GraphicalZonotopes.clique_book_classification_polytopal,
  GraphicalZonotopes.SaturatedDirections.paper_theorem_7_12,
  GraphicalZonotopes.SaturatedDirections.paper_theorem_7_12_polytopal,
  GraphicalZonotopes.SaturatedDirections.paper_theorem_7_12_geometric,
  GraphicalZonotopes.saturatedHubNeighbors_closed_formula,
  GraphicalZonotopes.SparseFamily.paper_theorem_8_2,
  GraphicalZonotopes.SparseFamily.paper_theorem_8_2_polytopal,
  GraphicalZonotopes.TwoHub.exponential_lattice_summand,
  GraphicalZonotopes.TwoHub.exponential_family,
  GraphicalZonotopes.TwoHub.exponential_polytopal_summand,
  GraphicalZonotopes.TwoHub.two_singleton_classification,
  GraphicalZonotopes.TwoHub.classification_polytopal,
  GraphicalZonotopes.TwoHub.full_polytopal_iff,
  GraphicalZonotopes.TwoHub.lattice_polytopal_attainment,
  GraphicalZonotopes.partial_threeTree_piecewise_maximum,
  GraphicalZonotopes.partial_threeTree_full_dimension_spectrum,
  GraphicalZonotopes.threeTree_dimension_and_spectrum,
  GraphicalZonotopes.partial_threeTree_support_classification_polytopal_finite,
  GraphicalZonotopes.partial_threeTree_piecewise_maximum_finite,
  GraphicalZonotopes.partial_threeTree_full_dimension_spectrum_polytopal_finite,
  GraphicalZonotopes.SupportsFullIndecomposable.triangle_free_components_le_one,
  GraphicalZonotopes.SupportsFullIndecomposable.separator_contains_triangle,
  GraphicalZonotopes.SupportsFullIndecomposable.delete_lt_three_preconnected,
  GraphicalZonotopes.weak_summand_exposed_edge_direction,
  GraphicalZonotopes.weakSummand_indecomposable_iff_polytopal,
  GraphicalZonotopes.isWeakMinkowskiSummand_graphical_iff_finite_complement,
  GraphicalZonotopes.isMinkowskiSummand_graphical_iff_finite_complement,
  GraphicalZonotopes.partial_threeTree_polytope_support,
  GraphicalZonotopes.BooleanModule.cliqueCapacity_int_formula,
  GraphicalZonotopes.TwoHub.paper_corollary_8_5,
  GraphicalZonotopes.HamiltonianDeletion.hamiltonian_component_card_delete_le,
  GraphicalZonotopes.IsThreeTree.admissible_of_hamiltonian,
  GraphicalZonotopes.hamiltonian_threeTree_lattice_polytopal_finite,
  GraphicalZonotopes.actualEdgeDirectionLines_finite,
  GraphicalZonotopes.directionCount_eq_geometric_line_count,
  GraphicalZonotopes.three_hub_book_maximum,
  GraphicalZonotopes.TreeJoin.induced_subcubic_iff_subtree,
  GraphicalZonotopes.TreeJoin.maximum_dimension,
  GraphicalZonotopes.TreeJoin.supports_full_iff,
  GraphicalZonotopes.TreeJoin.paper_corollary_6_9_tree_join,
  GraphicalZonotopes.SparseFamily.complete_family,
  GraphicalZonotopes.TwoHub.CellDecisionTree.root_valid,
  GraphicalZonotopes.TwoHub.CellDecisionTree.leaves_card,
  GraphicalZonotopes.TwoHub.CellDecisionTree.root_proper,
  GraphicalZonotopes.TwoHub.PartitionData.partitionDilation_eq,
  GraphicalZonotopes.TwoHub.decision_tree_lattice_summand,
  GraphicalZonotopes.TwoHub.paper_lemma_8_6,
  GraphicalZonotopes.paper_corollary_6_4,
  GraphicalZonotopes.paper_corollary_6_4_stacked,
  GraphicalZonotopes.paper_corollary_6_5,
  GraphicalZonotopes.planar_threeTree_lattice_witness_finite,
  GraphicalZonotopes.HasPlaneDrawing.triangle_apex_separated,
  GraphicalZonotopes.TetrahedronComponents.maximumDimension_eq,
  GraphicalZonotopes.TetrahedronComponents.adj_iff_shared_triangle,
  GraphicalZonotopes.boundaryTriangles_after_attachment,
  Graph.IsArcK5.elim,
  GraphicalZonotopes.paper_corollary_5_2,
  GraphicalZonotopes.full_generalized_permutahedron_triangle_separators,
  GraphicalZonotopes.unit_lattice_active_classification_finite,
  GraphicalZonotopes.HasPlaneStraightLineDrawing.hasPlaneDrawing,
  GraphicalZonotopes.PathDrawing.path_hasPlaneDrawing,
  GraphicalZonotopes.IsPartialThreeTree.incidence_isAcyclic,
  GraphicalZonotopes.PolynomialWeights.minWeight_mul,
  GraphicalZonotopes.PolynomialWeights.maxWeight_mul,
  GraphicalZonotopes.BookSpectrum.prescribed_coordinate_criterion,
  GraphicalZonotopes.BookSpectrum.lattice_dimension_spectrum,
  GraphicalZonotopes.BookSpectrum.positive_dimension_spectrum,
  GraphicalZonotopes.Polyhedral.minimal_face_tight_kernel,
  GraphicalZonotopes.Polyhedral.extremeRay_iff_minimal_face_span,
  GraphicalZonotopes.Polyhedral.extremeRay_iff_minimal_face_finrank,
  GraphicalZonotopes.Separator.positive_response_gluing_minimal_face_finite,
  GraphicalZonotopes.NewtonGeometry.newton_mul_of_basePolytope,
  GraphicalZonotopes.NewtonGeometry.irreducible_of_newton_base_extreme_unit_slack,
  GraphicalZonotopes.NewtonGeometry.corollary_A_3_absoluteIrreducible,
  GraphicalZonotopes.PathDeterminant.proposition_A_2_stability,
  GraphicalZonotopes.PathDeterminant.proposition_A_2_absoluteIrreducible,
  GraphicalZonotopes.PathDeterminant.polynomial_irreducible,
  GraphicalZonotopes.PathDeterminant.polynomial_irreducible_map,
  GraphicalZonotopes.PathDeterminant.tridiagonal_det_recurrence
]
