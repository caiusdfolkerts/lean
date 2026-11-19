module

public import Mathlib.LinearAlgebra.Matrix.ConjTranspose
public import Mathlib.Basic.Complex.BigOperators
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.SplitIfs

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
