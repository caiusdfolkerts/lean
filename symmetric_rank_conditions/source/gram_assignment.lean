module
public import Mathlib.RingTheory.MvPolynomial.MonomialOrder
public import Mathlib.Data.Finset.Sort
public import Mathlib.Order.Prod.Lex.Basic

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 1000000

/-!
# Canonical column assignments for generic Gram matrices

The auxiliary generic matrix has independent variables indexed by column and
then row.  Its lexicographic order places smaller column and row indices first.
An increasing row list has one unique maximal injective column assignment:
assign its successive rows to columns `0, …, t - 1`.
-/

noncomputable section
namespace FourPapers.Symmetric.Gram
open Finset Finsupp MvPolynomial
open scoped MonomialOrder

abbrev Variable (n : ℕ) := Fin n ×ₗ Fin n
abbrev Polynomial (n : ℕ) (R : Type*) [CommRing R] := MvPolynomial (Variable n) R

def order (n : ℕ) : MonomialOrder (Variable n) := MonomialOrder.lex

def firstColumns {t n : ℕ} (h : t ≤ n) (i : Fin t) : Fin n :=
  ⟨i.val, lt_of_lt_of_le i.isLt h⟩

@[simp] theorem firstColumns_val {t n : ℕ} (h : t ≤ n) (i : Fin t) :
    (firstColumns h i).val = i.val := rfl

theorem firstColumns_injective {t n : ℕ} (h : t ≤ n) :
    Function.Injective (firstColumns h) := by
  intro i j hij
  exact Fin.ext (congrArg (fun x : Fin n => x.val) hij)

def assignmentExponent {n t : ℕ} (a : Fin t → Fin n) (f : Fin t → Fin n) :
    Variable n →₀ ℕ := ∑ i, single (toLex (f i, a i)) 1

def diagonalExponent {n t : ℕ} (h : t ≤ n) (a : Fin t ↪o Fin n) :
    Variable n →₀ ℕ := assignmentExponent a (firstColumns h)

private theorem pair_mono {n : ℕ} {c d r s : Fin n} (hc : c ≤ d) (hr : r ≤ s) :
    (toLex (c, r) : Variable n) ≤ toLex (d, s) :=
  Prod.Lex.toLex_le_toLex'.mpr ⟨hc, fun _ => hr⟩

/-- A strictly noncanonical injective assignment is lexicographically smaller.
No characteristic, coefficient, or determinant claim enters this finite argument. -/
theorem assignmentExponent_lt_diagonal {n t : ℕ} (h : t ≤ n)
    (a : Fin t ↪o Fin n) (f : Fin t → Fin n) (hf : Function.Injective f)
    (hne : f ≠ firstColumns h) :
    assignmentExponent a f ≺[order n] diagonalExponent h a := by
  classical
  let S : Finset (Fin t) := univ.filter (fun i => f i ≠ firstColumns h i)
  have hS : S.Nonempty := by
    by_contra hempty
    apply hne
    funext j
    by_contra hj
    exact hempty ⟨j, mem_filter.mpr ⟨mem_univ _, hj⟩⟩
  let i := S.min' hS
  have hi : f i ≠ firstColumns h i := (mem_filter.mp (S.min'_mem hS)).2
  have hprev : ∀ j : Fin t, j < i → f j = firstColumns h j := by
    intro j hj
    by_contra hfj
    have hm : j ∈ S := mem_filter.mpr ⟨mem_univ _, hfj⟩
    exact (not_lt_of_ge (S.min'_le _ hm)) hj
  have hcols : ∀ j : Fin t, i ≤ j → firstColumns h i ≤ f j := by
    intro j hij
    by_contra hnot
    have hlt : (f j).val < i.val := by
      simpa only [Fin.lt_def, firstColumns_val] using lt_of_not_ge hnot
    let k : Fin t := ⟨(f j).val, hlt.trans i.isLt⟩
    have hki : k < i := hlt
    have hfk : f k = f j := (hprev k hki).trans (Fin.ext rfl)
    have hkj := hf hfk
    exact (not_lt_of_ge hij) (hkj ▸ hki)
  change Finsupp.Lex (· < ·) (· < ·) (assignmentExponent a f) (diagonalExponent h a)
  rw [Finsupp.lex_def]
  refine ⟨toLex (firstColumns h i, a i), ?_, ?_⟩
  · intro q hq
    simp only [assignmentExponent, diagonalExponent, Finsupp.finsetSum_apply]
    apply Finset.sum_congr rfl
    intro j _
    by_cases hji : j < i
    · rw [hprev j hji]
    · have hij : i ≤ j := le_of_not_gt hji
      have hp := pair_mono (hcols j hij) (a.monotone hij)
      have hcan := pair_mono (show firstColumns h i ≤ firstColumns h j from hij)
        (a.monotone hij)
      have hn : toLex (f j, a j) ≠ q := (hq.trans_le hp).ne'
      have hn' : toLex (firstColumns h j, a j) ≠ q := (hq.trans_le hcan).ne'
      simp only [single_apply, hn, hn', ite_false]
  · have hz : assignmentExponent a f (toLex (firstColumns h i, a i)) = 0 := by
      simp only [assignmentExponent, Finsupp.finsetSum_apply]
      apply Finset.sum_eq_zero
      intro j _
      have hp : toLex (f j, a j) ≠ (toLex (firstColumns h i, a i) : Variable n) := by
        intro he
        have hj : j = i := a.injective (congrArg (fun p : Variable n => p.2) he)
        subst j
        exact hi (congrArg (fun p : Variable n => p.1) he)
      simp only [single_apply, hp, ite_false]
    have ho : diagonalExponent h a (toLex (firstColumns h i, a i)) = 1 := by
      simp only [diagonalExponent, assignmentExponent, Finsupp.finsetSum_apply]
      rw [Finset.sum_eq_single i]
      · simp
      · intro j _ hji
        have hp : toLex (firstColumns h j, a j) ≠
            (toLex (firstColumns h i, a i) : Variable n) := by
          intro he
          exact hji (a.injective (congrArg (fun p : Variable n => p.2) he))
        simp only [single_apply, hp, ite_false]
      · simp
    rw [hz, ho]
    exact Nat.zero_lt_one

theorem assignmentExponent_le_diagonal {n t : ℕ} (h : t ≤ n)
    (a : Fin t ↪o Fin n) (f : Fin t → Fin n) (hf : Function.Injective f) :
    assignmentExponent a f ≼[order n] diagonalExponent h a := by
  by_cases he : f = firstColumns h
  · subst f
    exact le_rfl
  · exact (assignmentExponent_lt_diagonal h a f hf he).le

end FourPapers.Symmetric.Gram
