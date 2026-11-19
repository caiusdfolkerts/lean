module

public import PaperVerification.IsotropicAttractingPivots

/-!
# The full scheme-theoretic ideal on an attracting cell

Both original alternating forms, on every ordered pair of universal rows,
generate exactly the ideal indexed by the increasing low pivot pairs.  The
argument works over every commutative coefficient ring: diagonal pairings
vanish by pairwise cancellation, not by division by two.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

namespace PaperVerification.IsotropicAttractingCoordinates

open MvPolynomial
open scoped BigOperators

variable {R : Type*} [CommRing R] {n s : ℕ}

@[simp] theorem formMatrix_self (c : ℕ) (a : Fin n) :
    formMatrix (R := R) c a a = 0 := by
  simp [formMatrix]

theorem formMatrix_swap (c : ℕ) (a b : Fin n) :
    formMatrix (R := R) c b a = -formMatrix c a b := by
  unfold formMatrix
  by_cases hab : a.val + b.val = c
  · have hba : b.val + a.val = c := by omega
    rw [ite_eq_left hab, ite_eq_left hba]
    rcases lt_trichotomy a b with h | h | h
    · simp [h, not_lt_of_gt h]
    · simp [h]
    · simp [h, not_lt_of_gt h]
  · have hba : b.val + a.val ≠ c := by omega
    simp [hab, hba]

/-- Swapping the two universal rows negates the original pairing. -/
theorem equation_swap (p : Fin s ↪ Fin n) (c : ℕ) (i j : Fin s) :
    equation (R := R) p c j i = -equation p c i j := by
  classical
  unfold equation
  calc
    _ = ∑ a : Fin n, ∑ b : Fin n,
        C (formMatrix (R := R) c b a) * row p j b * row p i a :=
      Finset.sum_comm
    _ = ∑ a : Fin n, ∑ b : Fin n,
        -(C (formMatrix (R := R) c a b) * row p i a * row p j b) := by
      apply Finset.sum_congr rfl
      intro a _
      apply Finset.sum_congr rfl
      intro b _
      rw [formMatrix_swap, map_neg]
      ring
    _ = _ := by simp

/-- Diagonal pairings vanish over arbitrary commutative rings, including
characteristic two; no cancellation of the scalar two is used. -/
@[simp] theorem equation_self (p : Fin s ↪ Fin n) (c : ℕ) (i : Fin s) :
    equation (R := R) p c i i = 0 := by
  classical
  unfold equation
  rw [← Finset.sum_product']
  apply Finset.sum_ninvolution Prod.swap
  · intro q
    dsimp only [Prod.swap]
    rw [formMatrix_swap, map_neg]
    ring
  · intro q hq he
    have h : q.2 = q.1 := congrArg Prod.fst he
    apply hq
    simp [h]
  · intro q
    simp
  · intro q
    rfl

variable {k : ℕ} {p : Fin s ↪ Fin (2*k+1)}

/-- The complete list of nonzero positive-weight row-pair equations. -/
def lowEquation : LowPair p ⊕ LowPair p → MvPolynomial (Coordinate p) R :=
  Sum.elim (fun q => equation p (2*k+1) q.val.1 q.val.2)
    (fun q => equation p (2*k) q.val.1 q.val.2)

def lowIdeal : Ideal (MvPolynomial (Coordinate p) R) :=
  Ideal.span (Set.range (lowEquation (R := R) (p := p)))

theorem lowIdeal_le_isotropyIdeal :
    lowIdeal (R := R) (p := p) ≤ isotropyIdeal p (2*k+1) (2*k) := by
  apply Ideal.span_le.mpr
  rintro _ ⟨q, rfl⟩
  apply Ideal.subset_span
  cases q with
  | inl q => exact ⟨(true, q.val.1, q.val.2), rfl⟩
  | inr q => exact ⟨(false, q.val.1, q.val.2), rfl⟩

theorem ordered_equation_mem_lowIdeal (hp : IndependentPivots p)
    (c : ℕ) (hc : c = 2*k+1 ∨ c = 2*k) (i j : Fin s)
    (hij : p i < p j) :
    equation (R := R) p c i j ∈ lowIdeal (p := p) := by
  by_cases hlow : (p i).val + (p j).val < 2*k
  · let q : LowPair p := ⟨(i,j), hij, hlow⟩
    apply Ideal.subset_span
    rcases hc with rfl | rfl
    · exact ⟨Sum.inl q, rfl⟩
    · exact ⟨Sum.inr q, rfl⟩
  · have hne : i ≠ j := by
      intro h
      simp [h] at hij
    have hind := hp i j hne
    have hneg : c < (p i).val + (p j).val := by
      rcases hc with rfl | rfl <;> omega
    rw [equation_eq_zero_of_negative_weight p c i j hneg]
    exact Ideal.zero_mem _

theorem equation_mem_lowIdeal (hp : IndependentPivots p)
    (c : ℕ) (hc : c = 2*k+1 ∨ c = 2*k) (i j : Fin s) :
    equation (R := R) p c i j ∈ lowIdeal (p := p) := by
  rcases lt_trichotomy (p i) (p j) with hij | hij | hij
  · exact ordered_equation_mem_lowIdeal hp c hc i j hij
  · have he := p.injective hij
    subst j
    rw [equation_self]
    exact Ideal.zero_mem _
  · rw [equation_swap p c j i]
    exact neg_mem (ordered_equation_mem_lowIdeal hp c hc j i hij)

/-- Equality with the full original ideal. This retains all nilpotent and
scheme-theoretic information; it is not a set-theoretic comparison. -/
theorem isotropyIdeal_eq_lowIdeal (hp : IndependentPivots p) :
    isotropyIdeal (R := R) p (2*k+1) (2*k) = lowIdeal (p := p) := by
  apply le_antisymm
  · apply Ideal.span_le.mpr
    rintro _ ⟨q, rfl⟩
    apply equation_mem_lowIdeal hp
    cases q.1 <;> simp
  · exact lowIdeal_le_isotropyIdeal

end PaperVerification.IsotropicAttractingCoordinates
