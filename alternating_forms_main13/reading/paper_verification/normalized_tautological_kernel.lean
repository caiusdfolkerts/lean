module

public import Mathlib.LinearAlgebra.Matrix.SchurComplement
public import Mathlib.LinearAlgebra.Matrix.Notation
public import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

/-!
# The tautological kernel on a normalized matrix chart

A vector belongs to the span of the normalized rows precisely when every
augmented maximal minor vanishes. The proof works over every commutative ring,
including nonreduced rings. The pivot projection is an explicit inverse to the
row-coordinate map, so the resulting kernel is genuinely free of rank `s`.
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators Matrix

namespace PaperVerification.NormalizedTautologicalKernel

variable {R : Type*} [CommRing R] {s n : ℕ}

def augmented (A : Matrix (Fin s) (Fin n) R) (v : Fin n → R) :
    Matrix (Fin (s+1)) (Fin n) R := Fin.cons v A

/-- Every coordinate of the exterior product of a vector with the row wedge.
Repeated column words are retained; their determinants vanish automatically. -/
def incidence (A : Matrix (Fin s) (Fin n) R) (v : Fin n → R)
    (J : Fin (s+1) → Fin n) : R :=
  Matrix.det ((augmented A v).submatrix id J)

private def oneTailEquiv (s : ℕ) : Fin 1 ⊕ Fin s ≃ Fin (s+1) :=
  (finSumFinEquiv : Fin 1 ⊕ Fin s ≃ Fin (1+s)).trans (finCongr (by omega))

@[simp] private lemma oneTailEquiv_zero (s : ℕ) :
    oneTailEquiv s (Sum.inl 0)=0 := by
  apply Fin.ext
  simp [oneTailEquiv]

@[simp] private lemma oneTailEquiv_succ (s : ℕ) (i : Fin s) :
    oneTailEquiv s (Sum.inr i)=i.succ := by
  apply Fin.ext
  simp [oneTailEquiv]

/-- The augmented minor on one arbitrary column and all pivot columns is
exactly the error in the corresponding row-span equation. -/
theorem incidence_pivot_columns
    (A : Matrix (Fin s) (Fin n) R) (p : Fin s → Fin n)
    (hp : A.submatrix id p=1) (v : Fin n → R) (j : Fin n) :
    incidence A v (Fin.cons j p) = v j - ∑ i, v (p i)*A i j := by
  classical
  let M := (augmented A v).submatrix id (Fin.cons j p)
  let B : Matrix (Fin 1) (Fin s) R := fun _ i => v (p i)
  let C : Matrix (Fin s) (Fin 1) R := fun i _ => A i j
  let D : Matrix (Fin 1) (Fin 1) R := fun _ _ => v j
  have hp' (a b : Fin s) : A a (p b)=(1 : Matrix (Fin s) (Fin s) R) a b :=
    congrFun (congrFun hp a) b
  have hb : M.submatrix (oneTailEquiv s) (oneTailEquiv s)=
      Matrix.fromBlocks D B C 1 := by
    ext a b
    cases a with
    | inl a =>
      have ha : a=0 := Subsingleton.elim _ _
      subst a
      cases b with
      | inl b =>
        have hb : b=0 := Subsingleton.elim _ _
        subst b
        simp [M,D,augmented,Matrix.submatrix]
      | inr b => simp [M,B,augmented,Matrix.submatrix]
    | inr a =>
      cases b with
      | inl b =>
        have hb : b=0 := Subsingleton.elim _ _
        subst b
        simp [M,C,augmented,Matrix.submatrix]
      | inr b => simp [M,augmented,Matrix.submatrix,hp']
  change Matrix.det M = _
  rw [← Matrix.det_submatrix_equiv_self (oneTailEquiv s) M,hb,
    Matrix.det_fromBlocks_one₂₂]
  simp [D,B,C,Matrix.det_unique,Matrix.sub_apply,Matrix.mul_apply]

/-- A linear combination of the rows has zero exterior product with them. -/
theorem incidence_rowCombination (A : Matrix (Fin s) (Fin n) R)
    (x : Fin s → R) (J : Fin (s+1) → Fin n) :
    incidence A (x ᵥ* A) J=0 := by
  classical
  let M := (augmented A 0).submatrix id J
  let c : Fin (s+1) → R := Fin.cons 0 x
  have h := Matrix.det_updateRow_sum M (0 : Fin (s+1)) c
  have he : M.updateRow 0 (∑ i, c i • M i)=
      (augmented A (x ᵥ* A)).submatrix id J := by
    ext i j
    refine Fin.cases ?_ (fun i => ?_) i
    · simp [M,c,augmented,Matrix.updateRow,Function.update,
        Matrix.submatrix,Fin.sum_univ_succ,Matrix.vecMul,dotProduct,Finset.sum_apply]
    · simp [M,c,augmented,Matrix.updateRow,Function.update,Matrix.submatrix,Fin.succ_ne_zero]
  rw [he] at h
  simpa only [c,Fin.cons_zero,zero_smul,incidence] using h

/-- The complete kernel is the original row span, with its explicit pivot
coordinates. No field-valued-point or radical argument is involved. -/
theorem incidence_zero_iff_rowCombination
    (A : Matrix (Fin s) (Fin n) R) (p : Fin s → Fin n)
    (hp : A.submatrix id p=1) (v : Fin n → R) :
    (∀ J, incidence A v J=0) ↔ v=(fun i => v (p i)) ᵥ* A := by
  constructor
  · intro h
    funext j
    have hj := h (Fin.cons j p)
    rw [incidence_pivot_columns A p hp] at hj
    exact sub_eq_zero.mp hj
  · intro h J
    rw [h]
    exact incidence_rowCombination A _ J

/-- Projection to the pivot columns recovers every row-coordinate vector. -/
theorem rowCombination_pivot
    (A : Matrix (Fin s) (Fin n) R) (p : Fin s → Fin n)
    (hp : A.submatrix id p=1) (x : Fin s → R) (i : Fin s) :
    (x ᵥ* A) (p i)=x i := by
  have h : x ᵥ* (A.submatrix id p)=x := by rw [hp,Matrix.vecMul_one]
  exact congrFun h i

end PaperVerification.NormalizedTautologicalKernel
