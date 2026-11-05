module

public import verified.appendix_a2
public import Mathlib.Tactic.NormNum

/-!
# A positive recurrence for the literal tridiagonal determinant

The pair `(D_k, E_k)` is defined over a fixed coefficient ring and a fixed
sequence of variables. A trailing Laplace expansion connects its first
coordinate to the determinant already used in Proposition A.2.
-/

@[expose] public section
noncomputable section
open scoped BigOperators Matrix
open Finset Matrix

namespace GraphicalZonotopes.PathDeterminant

section PositiveRecurrence

variable {R : Type*} [CommSemiring R]

/-- The subtraction-free prefix recurrence. The first coordinate is `D_k`
and the second is the auxiliary polynomial `E_k`. -/
def positivePair (t : ℕ → R) : ℕ → R × R
  | 0 => (1, 1)
  | k + 1 =>
      let p := positivePair t k
      let e := t (k + 2) * p.1 + t k * p.2
      (e + t (k + 1) * p.1, e)

@[simp] theorem positivePair_zero (t : ℕ → R) : positivePair t 0 = (1, 1) := rfl

theorem positivePair_snd_succ (t : ℕ → R) (k : ℕ) :
    (positivePair t (k + 1)).2 =
      t (k + 2) * (positivePair t k).1 + t k * (positivePair t k).2 := rfl

theorem positivePair_fst_succ (t : ℕ → R) (k : ℕ) :
    (positivePair t (k + 1)).1 =
      (positivePair t (k + 1)).2 + t (k + 1) * (positivePair t k).1 := rfl

/-- A fixed ambient multivariate polynomial ring suffices for every prefix.
Only indices strictly below `m+2` are used when the prefix has length `m`. -/
def variableSequence (R : Type*) [CommSemiring R] (m : ℕ) (j : ℕ) :
    MvPolynomial (Fin (m + 2)) R :=
  MvPolynomial.X ⟨j % (m + 2), Nat.mod_lt _ (by omega)⟩

@[simp] theorem variableSequence_fin (R : Type*) [CommSemiring R] (m : ℕ)
    (j : Fin (m + 2)) : variableSequence R m j.val = MvPolynomial.X j := by
  unfold variableSequence
  congr 1
  exact Fin.ext (Nat.mod_eq_of_lt j.isLt)

end PositiveRecurrence

section Ring

variable {R : Type*} [CommRing R]

/-- Deleting the last row and column retains the initial variable sequence. -/
theorem tridiagonal_init {m : ℕ} (t : Fin (m + 3) → R) :
    (tridiagonal t).submatrix Fin.castSucc Fin.castSucc =
      tridiagonal (fun j : Fin (m + 2) => t j.castSucc) := by
  ext i j
  simp only [Matrix.submatrix_apply, tridiagonal, ← Fin.castSucc_succ, Fin.castSucc_inj]

theorem tridiagonal_init_twice {m : ℕ} (t : Fin (m + 4) → R) :
    (tridiagonal t).submatrix (fun i : Fin m => i.castSucc.castSucc)
        (fun j : Fin m => j.castSucc.castSucc) =
      tridiagonal (fun j : Fin (m + 2) => t j.castSucc.castSucc) := by
  calc
    _ = ((tridiagonal t).submatrix Fin.castSucc Fin.castSucc).submatrix
        Fin.castSucc Fin.castSucc := rfl
    _ = _ := by rw [tridiagonal_init, tridiagonal_init]

theorem tridiagonal_last_castSucc_castSucc {m : ℕ} (t : Fin (m + 4) → R)
    (j : Fin m) :
    tridiagonal t (Fin.last (m + 1)) j.castSucc.castSucc = 0 := by
  apply tridiagonal_off_band
  · intro h
    have hv := congrArg Fin.val h
    simp only [Fin.val_last, Fin.val_castSucc] at hv
    omega
  · simp only [Fin.val_last, Fin.val_castSucc]
    omega
  · simp only [Fin.val_last, Fin.val_castSucc]
    omega

theorem tridiagonal_castSucc_castSucc_last {m : ℕ} (t : Fin (m + 4) → R)
    (i : Fin m) :
    tridiagonal t i.castSucc.castSucc (Fin.last (m + 1)) = 0 := by
  apply tridiagonal_off_band
  · intro h
    have hv := congrArg Fin.val h
    simp only [Fin.val_last, Fin.val_castSucc] at hv
    omega
  · simp only [Fin.val_last, Fin.val_castSucc]
    omega
  · simp only [Fin.val_last, Fin.val_castSucc]
    omega

private theorem sign_double (k : ℕ) : (-1 : R) ^ (k + k) = 1 := by
  rw [show k + k = 2 * k by omega, pow_mul]
  norm_num

private theorem sign_last_penultimate (k : ℕ) : (-1 : R) ^ (k + 1 + k) = -1 := by
  rw [show k + 1 + k = (k + k) + 1 by omega, pow_succ, sign_double, one_mul]

/-- The penultimate-column cofactor in the trailing Laplace expansion has
only one nonzero entry in its last column. -/
theorem tridiagonal_minor_penultimate_det {m : ℕ} (t : Fin (m + 4) → R) :
    ((tridiagonal t).submatrix Fin.castSucc (Fin.last m).castSucc.succAbove).det =
      -t (Fin.last (m + 1)).castSucc.castSucc *
        (tridiagonal (fun j : Fin (m + 2) => t j.castSucc.castSucc)).det := by
  let N : Matrix (Fin (m + 1)) (Fin (m + 1)) R :=
    (tridiagonal t).submatrix Fin.castSucc (Fin.last m).castSucc.succAbove
  change N.det = _
  have hlast : N (Fin.last m) (Fin.last m) =
      -t (Fin.last (m + 1)).castSucc.castSucc := by
    change tridiagonal t (Fin.last m).castSucc
      ((Fin.last m).castSucc.succAbove (Fin.last m)) = _
    rw [Fin.succAbove_castSucc_self, Fin.succ_last]
    exact tridiagonal_above t (Fin.last m).castSucc (Fin.last (m + 1)) (by simp)
  have hzero : ∀ i : Fin m, N i.castSucc (Fin.last m) = 0 := by
    intro i
    change tridiagonal t i.castSucc.castSucc
      ((Fin.last m).castSucc.succAbove (Fin.last m)) = 0
    rw [Fin.succAbove_castSucc_self, Fin.succ_last]
    exact tridiagonal_castSucc_castSucc_last t i
  have hinit : N.submatrix Fin.castSucc Fin.castSucc =
      tridiagonal (fun j : Fin (m + 2) => t j.castSucc.castSucc) := by
    ext i j
    change tridiagonal t i.castSucc.castSucc
      ((Fin.last m).castSucc.succAbove j.castSucc) = _
    rw [Fin.succAbove_castSucc_of_lt _ _ (Fin.castSucc_lt_last j)]
    exact congrFun (congrFun (tridiagonal_init_twice t) i) j
  rw [Matrix.det_succ_column N (Fin.last m), Fin.sum_univ_castSucc]
  simp only [Fin.val_castSucc, Fin.val_last, hzero, mul_zero, zero_mul,
    Finset.sum_const_zero, zero_add, sign_double, one_mul, Fin.succAbove_last]
  rw [hlast, hinit]

/-- The trailing continuant identity for the actual displayed matrix. -/
theorem tridiagonal_det_recurrence_right {m : ℕ} (t : Fin (m + 4) → R) :
    (tridiagonal t).det =
      (t (Fin.last (m + 1)).castSucc.castSucc +
        t (Fin.last (m + 1)).succ.castSucc + t (Fin.last (m + 1)).succ.succ) *
        (tridiagonal (fun j : Fin (m + 3) => t j.castSucc)).det -
      (t (Fin.last (m + 1)).castSucc.castSucc)^2 *
        (tridiagonal (fun j : Fin (m + 2) => t j.castSucc.castSucc)).det := by
  have hdiag := tridiagonal_diag t (Fin.last (m + 1))
  have hprev : tridiagonal t (Fin.last (m + 1)) (Fin.last m).castSucc =
      -t (Fin.last (m + 1)).castSucc.castSucc :=
    tridiagonal_below t (Fin.last (m + 1)) (Fin.last m).castSucc (by simp)
  rw [Matrix.det_succ_row (tridiagonal t) (Fin.last (m + 1)),
    Fin.sum_univ_castSucc, Fin.sum_univ_castSucc]
  simp only [Fin.val_castSucc, Fin.val_last, tridiagonal_last_castSucc_castSucc,
    mul_zero, zero_mul, Finset.sum_const_zero, zero_add, sign_double,
    sign_last_penultimate, one_mul, Fin.succAbove_last]
  rw [hdiag, hprev, tridiagonal_init, tridiagonal_minor_penultimate_det]
  ring

/-- The determinant of a prefix, over a fixed ambient coefficient ring. -/
def prefixDet (t : ℕ → R) (m : ℕ) : R :=
  (tridiagonal (fun j : Fin (m + 2) => t j.val)).det

@[simp] theorem prefixDet_zero (t : ℕ → R) : prefixDet t 0 = 1 := by
  simp [prefixDet]

theorem prefixDet_one (t : ℕ → R) : prefixDet t 1 = t 0 + t 1 + t 2 := by
  unfold prefixDet
  rw [Matrix.det_fin_one]
  simpa using tridiagonal_diag (fun j : Fin 3 => t j.val) 0

theorem prefixDet_recurrence (t : ℕ → R) (m : ℕ) :
    prefixDet t (m + 2) =
      (t (m + 1) + t (m + 2) + t (m + 3)) * prefixDet t (m + 1) -
        (t (m + 1))^2 * prefixDet t m := by
  unfold prefixDet
  simpa only [Fin.val_castSucc, Fin.val_last, Fin.val_succ] using
    tridiagonal_det_recurrence_right (fun j : Fin (m + 4) => t j.val)

theorem positivePair_fst_recurrence (t : ℕ → R) (m : ℕ) :
    (positivePair t (m + 2)).1 =
      (t (m + 1) + t (m + 2) + t (m + 3)) * (positivePair t (m + 1)).1 -
        (t (m + 1))^2 * (positivePair t m).1 := by
  simp only [positivePair]
  ring

/-- The positive recurrence agrees with the literal determinant at every
size. In particular, the recurrence does not redefine the paper's object. -/
theorem positivePair_fst_eq_prefixDet (t : ℕ → R) (m : ℕ) :
    (positivePair t m).1 = prefixDet t m := by
  induction m using Nat.twoStepInduction with
  | zero => simp
  | one =>
      rw [prefixDet_one]
      simp only [positivePair, mul_one]
      ring
  | more m ih₀ ih₁ =>
      rw [positivePair_fst_recurrence, prefixDet_recurrence, ih₀, ih₁]

/-- The fixed-variable polynomial used in Proposition A.2 is exactly the
first coordinate of the subtraction-free recurrence. -/
theorem positivePair_polynomial (R : Type*) [CommRing R] (m : ℕ) :
    (positivePair (variableSequence R m) m).1 = polynomial R m := by
  simpa only [prefixDet, variableSequence_fin, polynomial] using
    positivePair_fst_eq_prefixDet (variableSequence R m) m

end Ring

end GraphicalZonotopes.PathDeterminant
