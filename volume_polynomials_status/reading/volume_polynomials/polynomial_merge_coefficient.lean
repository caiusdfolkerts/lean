module

public import VolumePolynomials.MixedVolume
public import Mathlib.Algebra.BigOperators.Finsupp.Fin
public import Lean.Elab.Tactic.Omega

@[expose] public section
set_option autoImplicit false
noncomputable section

/-!
# Squarefree coefficients when two variables are identified

Identifying a new variable with one old variable has exactly two preimages
over the squarefree exponent. The resulting coefficient identity supplies
the algebraic additivity step for actual mixed volume.
-/

open MvPolynomial
open scoped BigOperators

namespace VolumePolynomials

theorem coeff_rename_two_preimages {σ τ : Type*}
    (f : σ → τ) (a b : σ →₀ ℕ) (e : τ →₀ ℕ) (hab : a ≠ b)
    (hfiber : ∀ u : σ →₀ ℕ, u.mapDomain f = e ↔ u = a ∨ u = b)
    (p : MvPolynomial σ ℝ) :
    (MvPolynomial.rename f p).coeff e = p.coeff a + p.coeff b := by
  first
  | classical
    induction p using MvPolynomial.induction_on' with
    | monomial u r =>
        simp only [MvPolynomial.rename_monomial, MvPolynomial.coeff_monomial, hfiber]
        by_cases ha : u = a
        · subst u
          simp [hab]
        · by_cases hb : u = b
          · subst u
            simp [ha]
          · simp [ha, hb]
    | add p q hp hq =>
        simp only [map_add, MvPolynomial.coeff_add, hp, hq]
        ring

def mergeIndex {d : ℕ} (i : Fin d) : Fin (d + 1) → Fin d := Fin.cases i id

def oldSquarefreeLift (d : ℕ) : Fin (d + 1) →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm (Fin.cons 0 (fun _ : Fin d => 1))

def newSquarefreeLift {d : ℕ} (i : Fin d) : Fin (d + 1) →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm (Fin.cons 1 (fun j : Fin d => if j = i then 0 else 1))

@[simp] theorem oldSquarefreeLift_zero (d : ℕ) : oldSquarefreeLift d 0 = 0 := by
  first
  | simp [oldSquarefreeLift]

@[simp] theorem oldSquarefreeLift_succ {d : ℕ} (j : Fin d) :
    oldSquarefreeLift d j.succ = 1 := by simp [oldSquarefreeLift]

@[simp] theorem newSquarefreeLift_zero {d : ℕ} (i : Fin d) : newSquarefreeLift i 0 = 1 := by
  first
  | simp [newSquarefreeLift]

@[simp] theorem newSquarefreeLift_succ {d : ℕ} (i j : Fin d) :
    newSquarefreeLift i j.succ = if j = i then 0 else 1 := by simp [newSquarefreeLift]

theorem mapDomain_mergeIndex_apply {d : ℕ} (i j : Fin d) (u : Fin (d + 1) →₀ ℕ) :
    u.mapDomain (mergeIndex i) j = (if i = j then u 0 else 0) + u j.succ := by
  first
  | classical
    rw [Finsupp.mapDomain_apply, Finsupp.sum_fintype _ _ (fun _ => by simp),
      Fin.sum_univ_succ]
    simp [mergeIndex, Finsupp.single_apply, eq_comm]

theorem mergeIndex_squarefree_fiber {d : ℕ} (i : Fin d) (u : Fin (d + 1) →₀ ℕ) :
    u.mapDomain (mergeIndex i) = squarefreeExponent d ↔
      u = oldSquarefreeLift d ∨ u = newSquarefreeLift i := by
  first
  | constructor
    · intro h
      have hsum : u 0 + u i.succ = 1 := by
        first
        | have hi := congrArg (fun v : Fin d →₀ ℕ => v i) h
          rw [mapDomain_mergeIndex_apply, if_pos rfl, squarefreeExponent_apply] at hi
          exact hi
      have hothers (j : Fin d) (hj : j ≠ i) : u j.succ = 1 := by
        first
        | simpa only [mapDomain_mergeIndex_apply, if_neg (Ne.symm hj), zero_add,
            squarefreeExponent_apply] using congrArg (fun v : Fin d →₀ ℕ => v j) h
      have hcases : u 0 = 0 ∨ u 0 = 1 := by omega
      rcases hcases with hzero | hone
      · left
        ext j
        refine Fin.cases ?_ (fun j => ?_) j
        · simpa only [oldSquarefreeLift_zero] using hzero
        · rw [oldSquarefreeLift_succ]
          by_cases hj : j = i
          · subst j
            omega
          · exact hothers j hj
      · right
        ext j
        refine Fin.cases ?_ (fun j => ?_) j
        · simpa only [newSquarefreeLift_zero] using hone
        · rw [newSquarefreeLift_succ]
          by_cases hj : j = i
          · subst j
            rw [if_pos rfl]
            omega
          · rw [if_neg hj]
            exact hothers j hj
    · rintro (rfl | rfl)
      · ext j
        rw [mapDomain_mergeIndex_apply]
        simp
      · ext j
        rw [mapDomain_mergeIndex_apply]
        by_cases hij : i = j
        · subst j
          simp
        · simp [hij, Ne.symm hij]

theorem coeff_mergeIndex_squarefree {d : ℕ} (i : Fin d)
    (p : MvPolynomial (Fin (d + 1)) ℝ) :
    (MvPolynomial.rename (mergeIndex i) p).coeff (squarefreeExponent d) =
      p.coeff (oldSquarefreeLift d) + p.coeff (newSquarefreeLift i) := by
  first
  | apply coeff_rename_two_preimages _ _ _ _ _ (mergeIndex_squarefree_fiber i) p
    intro h
    have hz := congrArg (fun v : Fin (d + 1) →₀ ℕ => v 0) h
    have hzero : (0 : ℕ) = 1 := by
      first
      | simpa only [oldSquarefreeLift_zero, newSquarefreeLift_zero] using hz
    omega

theorem oldSquarefreeLift_eq_mapDomain (d : ℕ) :
    oldSquarefreeLift d = (squarefreeExponent d).mapDomain Fin.succ := by
  first
  | ext j
    refine Fin.cases ?_ (fun j => ?_) j
    · rw [oldSquarefreeLift_zero,
        Finsupp.mapDomain_of_notMem_range _ _ (by
          rintro ⟨i, hi⟩
          exact Fin.succ_ne_zero i hi)]
    · rw [oldSquarefreeLift_succ,
        Finsupp.mapDomain_apply_of_injective (Fin.succ_injective d), squarefreeExponent_apply]

def replaceIndex {d : ℕ} (i : Fin d) (j : Fin d) : Fin (d + 1) :=
  Equiv.swap 0 i.succ j.succ

theorem replaceIndex_injective {d : ℕ} (i : Fin d) : Function.Injective (replaceIndex i) :=
  (Equiv.swap 0 i.succ).injective.comp (Fin.succ_injective d)

@[simp] theorem replaceIndex_self {d : ℕ} (i : Fin d) : replaceIndex i i = 0 := by
  first
  | simp [replaceIndex]

theorem replaceIndex_of_ne {d : ℕ} {i j : Fin d} (hji : j ≠ i) :
    replaceIndex i j = j.succ := by
  first
  | simp [replaceIndex, Equiv.swap_apply_def, hji, Ne.symm hji, Fin.succ_inj]

theorem newSquarefreeLift_eq_mapDomain {d : ℕ} (i : Fin d) :
    newSquarefreeLift i = (squarefreeExponent d).mapDomain (replaceIndex i) := by
  first
  | ext j
    refine Fin.cases ?_ (fun j => ?_) j
    · rw [newSquarefreeLift_zero, ← replaceIndex_self i,
        Finsupp.mapDomain_apply_of_injective (replaceIndex_injective i),
        squarefreeExponent_apply]
    · rw [newSquarefreeLift_succ]
      by_cases hji : j = i
      · subst j
        rw [if_pos rfl]
        symm
        apply Finsupp.mapDomain_of_notMem_range
        rintro ⟨j, hj⟩
        have h := congrArg (Equiv.swap 0 i.succ) hj
        simp only [replaceIndex, Equiv.swap_apply_self, Equiv.swap_apply_right] at h
        exact Fin.succ_ne_zero j h
      · rw [if_neg hji, ← replaceIndex_of_ne hji,
          Finsupp.mapDomain_apply_of_injective (replaceIndex_injective i),
          squarefreeExponent_apply]

end VolumePolynomials
