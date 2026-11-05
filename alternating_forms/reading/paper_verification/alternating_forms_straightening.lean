module

public import PaperVerification.AlternatingFormsBoolean
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Data.Finset.Basic
public import Mathlib.Data.Subtype

/-!
# The local division identity for commuting square-zero pair variables

The Boolean matrix inverse is translated here into an identity in any
commutative algebra containing square-zero elements.  This is the algebraic
identity used for the paired variables in Lemma 3.1 of the paper.
-/

@[expose] public section

set_option autoImplicit false

namespace PaperVerification.AlternatingForms

open scoped BigOperators

section Incidences

variable {ι : Type*} [DecidableEq ι] [Fintype ι]

/-- Inserting an absent vertex and erasing a present vertex describe the
same incidence between consecutive ranks of the Boolean lattice. -/
def insertionIncidenceEquiv (n : ℕ) :
    (Σ T : FixedSubsets ι n, {a : ι // a ∉ T.1}) ≃
      (Σ U : FixedSubsets ι (n + 1), U.1) where
  toFun x := ⟨⟨insert x.2.1 x.1.1,
      by rw [Finset.card_insert_of_notMem x.2.2, x.1.2]⟩,
    ⟨x.2.1, Finset.mem_insert_self _ _⟩⟩
  invFun x := ⟨eraseSubset x.1 x.2, ⟨x.2.1, Finset.notMem_erase _ _⟩⟩
  left_inv x := by
    rcases x with ⟨⟨T, hT⟩, ⟨a, ha⟩⟩
    apply Sigma.ext
    · apply Subtype.ext
      exact Finset.erase_insert ha
    · refine (Subtype.heq_iff_coe_eq
        (p := fun b : ι => b ∉ (insert a T).erase a)
        (q := fun b : ι => b ∉ T) ?_).mpr ?_
      · intro b
        rw [Finset.erase_insert ha]
      · rfl
  right_inv x := by
    rcases x with ⟨⟨U, hU⟩, ⟨a, ha⟩⟩
    apply Sigma.ext
    · apply Subtype.ext
      exact Finset.insert_erase ha
    · refine (Subtype.heq_iff_coe_eq
        (p := fun b : ι => b ∈ insert a (U.erase a))
        (q := fun b : ι => b ∈ U) ?_).mpr ?_
      · intro b
        rw [Finset.insert_erase ha]
      · rfl

end Incidences

section SquareZeroAlgebra

variable {K A ι : Type*} [Field K] [CommRing A] [Algebra K A]
  [DecidableEq ι] [Fintype ι]

/-- Evaluate a vector on the rank-`n` Boolean lattice at squarefree products. -/
noncomputable def squarefreeEvaluation (y : ι → A) (n : ℕ) :
    (FixedSubsets ι n → K) →ₗ[K] A where
  toFun v := ∑ T : FixedSubsets ι n, v T • ∏ i ∈ T.1, y i
  map_add' v w := by simp [add_smul, Finset.sum_add_distrib]
  map_smul' c v := by simp [mul_smul, Finset.smul_sum]

theorem mul_squarefree_product (y : ι → A) (hy : ∀ i, y i * y i = 0)
    (T : Finset ι) (a : ι) :
    y a * (∏ i ∈ T, y i) = if a ∈ T then 0 else ∏ i ∈ insert a T, y i := by
  by_cases ha : a ∈ T
  · rw [if_pos ha, ← Finset.mul_prod_erase T y ha, ← mul_assoc, hy, zero_mul]
  · rw [if_neg ha, Finset.prod_insert ha]

/-- Multiplication by the sum of the square-zero variables is exactly the
Boolean upward inclusion operator under squarefree evaluation. -/
theorem squarefreeEvaluation_inclusion (y : ι → A) (hy : ∀ i, y i * y i = 0)
    (n : ℕ) (v : FixedSubsets ι n → K) :
    (∑ i, y i) * squarefreeEvaluation y n v =
      squarefreeEvaluation y (n + 1) (inclusionOperator n v) := by
  classical
  have hinner (T : FixedSubsets ι n) :
      (∑ a : ι, v T • (y a * ∏ i ∈ T.1, y i)) =
        ∑ a : {a : ι // a ∉ T.1}, v T • ∏ i ∈ insert a.1 T.1, y i := by
    letI : Fintype {a : ι // a ∈ T.1} := Subtype.fintype (fun a => a ∈ T.1)
    have hz : (∑ a : {a : ι // a ∈ T.1}, v T • (y a.1 * ∏ i ∈ T.1, y i)) = 0 := by
      apply Finset.sum_eq_zero
      intro a _
      rw [mul_squarefree_product y hy, if_pos a.2, smul_zero]
    calc
      _ = (∑ a : {a : ι // a ∈ T.1}, v T • (y a.1 * ∏ i ∈ T.1, y i)) +
          (∑ a : {a : ι // a ∉ T.1}, v T • (y a.1 * ∏ i ∈ T.1, y i)) :=
        (Fintype.sum_subtype_add_sum_subtype (fun a => a ∈ T.1)
          (fun a => v T • (y a * ∏ i ∈ T.1, y i))).symm
      _ = _ := by
        rw [hz, zero_add]
        apply Finset.sum_congr rfl
        intro a _
        rw [mul_squarefree_product y hy, if_neg a.2]
  have hinc :
      (∑ T : FixedSubsets ι n,
        ∑ a : {a : ι // a ∉ T.1}, v T • ∏ i ∈ insert a.1 T.1, y i) =
      ∑ U : FixedSubsets ι (n + 1),
        ∑ a : U.1, v (eraseSubset U a) • ∏ i ∈ U.1, y i := by
    rw [← Fintype.sum_sigma', ← Fintype.sum_sigma']
    apply Fintype.sum_equiv (insertionIncidenceEquiv n)
    rintro ⟨T, a⟩
    have herase : eraseSubset ((insertionIncidenceEquiv n) ⟨T, a⟩).1
        ((insertionIncidenceEquiv n) ⟨T, a⟩).2 = T := by
      apply Subtype.ext
      change (insert a.val T.val).erase a.val = T.val
      exact Finset.erase_insert a.property
    change v T • (∏ i ∈ insert a.val T.val, y i) =
      v (eraseSubset ((insertionIncidenceEquiv n) ⟨T, a⟩).1
        ((insertionIncidenceEquiv n) ⟨T, a⟩).2) • (∏ i ∈ insert a.val T.val, y i)
    rw [herase]
  change (∑ i, y i) * (∑ T : FixedSubsets ι n, v T • ∏ i ∈ T.1, y i) = _
  rw [Finset.mul_sum]
  simp_rw [mul_smul_comm, Finset.sum_mul, Finset.smul_sum, hinner]
  rw [hinc]
  simp only [squarefreeEvaluation, inclusionOperator, LinearMap.coe_mk,
    AddHom.coe_mk, Finset.sum_smul]

/-- The explicit inverse formula from Lemma 3.1, interpreted as an identity
of algebra elements.  It holds for every characteristic-zero field and
every commutative algebra of square-zero pair variables. -/
theorem local_pair_division [CharZero K]
    (y : ι → A) (hy : ∀ i, y i * y i = 0)
    (n : ℕ) (hι : Fintype.card ι = 2 * n + 1)
    (P : FixedSubsets ι (n + 1)) :
    (∑ i, y i) *
        (∑ T : FixedSubsets ι n,
          inverseCoefficient (K := K) n (T.1 ∩ P.1).card • ∏ i ∈ T.1, y i) =
      ∏ i ∈ P.1, y i := by
  have h := squarefreeEvaluation_inclusion y hy n
    (inclusionInverse n (Pi.single P (1 : K)))
  rw [inclusionOperator_inclusionInverse n hι] at h
  simpa [squarefreeEvaluation, inclusionInverse, Pi.single_apply] using h

end SquareZeroAlgebra

end PaperVerification.AlternatingForms
