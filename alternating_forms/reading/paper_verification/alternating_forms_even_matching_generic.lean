module

public import PaperVerification.AlternatingFormsEvenExteriorBoolean
public import PaperVerification.AlternatingFormsEvenAvailableRenaming
public import PaperVerification.AlternatingFormsBooleanGenericHilbert
public import Mathlib.LinearAlgebra.ExteriorPower.Basis
public import Mathlib.Algebra.MvPolynomial.Funext

/-!
# One simultaneous generic certificate for every matching-form degree

Every restriction to unoccupied pairs is obtained by an injective variable
renaming.  The product of the finite collection of Boolean certificates is
therefore nonzero in the original parameters.  Its nonvanishing controls
every degree at once.  Degrees above the dimension are handled by the
ordinary exterior-power dimension theorem, not by an extra hypothesis.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace PaperVerification.AlternatingForms.EvenSingletons

open scoped BigOperators Classical

variable {K ι : Type*} [Field K] [CharZero K] [LinearOrder ι] [Fintype ι]

def blockGenericPolynomial {s : ℕ} (J : DegreeBlock ι s) :
    MvPolynomial (Bool × Fin (Fintype.card (Available J.val.1))) K :=
  Classical.choose (BooleanGenericHilbert.generic_boolean_degree (K := K)
    (Fintype.card (Available J.val.1)) J.val.2.val)

theorem blockGenericPolynomial_ne_zero {s : ℕ} (J : DegreeBlock ι s) :
    blockGenericPolynomial (K := K) J ≠ 0 :=
  (Classical.choose_spec (BooleanGenericHilbert.generic_boolean_degree (K := K)
    (Fintype.card (Available J.val.1)) J.val.2.val)).1

theorem blockGenericPolynomial_spec {s : ℕ} (J : DegreeBlock ι s) (a c : ι → K)
    (h : BooleanQuotient.pairParameterEvaluation a c
      (blockParameterPullback J.val.1 (blockGenericPolynomial J)) ≠ 0) :
    Module.finrank K (BooleanQuotient.piece
      (fun i : Available J.val.1 => a i.val) (fun i : Available J.val.1 => c i.val)
      J.val.2.val) = Fintype.card (BlockGoodSubsets J) := by
  rw [finrank_availablePiece]
  rw [blockParameterPullback_evaluate] at h
  apply (Classical.choose_spec (BooleanGenericHilbert.generic_boolean_degree (K := K)
    (Fintype.card (Available J.val.1)) J.val.2.val)).2
  exact h

def degreeGenericPolynomial (s : ℕ) : MvPolynomial (Bool × ι) K :=
  ∏ J : DegreeBlock ι s, blockParameterPullback J.val.1 (blockGenericPolynomial J)

theorem degreeGenericPolynomial_ne_zero (s : ℕ) : degreeGenericPolynomial (K := K) (ι := ι) s ≠ 0 := by
  apply Finset.prod_ne_zero_iff.mpr
  intro J hJ
  exact blockParameterPullback_ne_zero J.val.1 (blockGenericPolynomial_ne_zero J)

def blockWalkCount (ι : Type*) [LinearOrder ι] [Fintype ι] (s : ℕ) : ℕ :=
  ∑ J : DegreeBlock ι s, Fintype.card (BlockGoodSubsets J)

theorem blockWalkCount_eq_zero {s : ℕ} (hs : Fintype.card ι < s) :
    blockWalkCount ι s = 0 := by
  apply Finset.sum_eq_zero
  intro J hJ
  exact card_blockGoodSubsets_zero hs J

variable {M : Type*} [AddCommGroup M] [Module K M] [FiniteDimensional K M]

theorem degreeGenericPolynomial_spec (b : Module.Basis (ι ⊕ ι) K M)
    (a c : ι → K) (s : ℕ)
    (h : BooleanQuotient.pairParameterEvaluation a c (degreeGenericPolynomial s) ≠ 0) :
    Module.finrank K (ExteriorQuotientDegree (matchingForm b a) (matchingForm b c) s) =
      blockWalkCount ι s := by
  rw [finrank_exteriorQuotient_eq_sum_booleanPieces]
  apply Finset.sum_congr rfl
  intro J hJ
  apply blockGenericPolynomial_spec
  have hp : ∏ L : DegreeBlock ι s, BooleanQuotient.pairParameterEvaluation a c
      (blockParameterPullback L.val.1 (blockGenericPolynomial L)) ≠ 0 := by
    simpa only [degreeGenericPolynomial, map_prod] using h
  exact Finset.prod_ne_zero_iff.mp hp J (Finset.mem_univ J)

def matchingGenericPolynomial : MvPolynomial (Bool × ι) K :=
  ∏ s : Fin (2 * Fintype.card ι + 1), degreeGenericPolynomial s.val

theorem matchingGenericPolynomial_ne_zero :
    matchingGenericPolynomial (K := K) (ι := ι) ≠ 0 := by
  apply Finset.prod_ne_zero_iff.mpr
  intro s hs
  exact degreeGenericPolynomial_ne_zero s.val

/-- The complete actual matching quotient Hilbert function, in every natural
degree, on one principal open in the original coefficient vectors. -/
theorem matchingGenericPolynomial_spec (b : Module.Basis (ι ⊕ ι) K M)
    (a c : ι → K)
    (h : BooleanQuotient.pairParameterEvaluation a c
      (matchingGenericPolynomial (K := K) (ι := ι)) ≠ 0) (s : ℕ) :
    Module.finrank K (ExteriorQuotientDegree (matchingForm b a) (matchingForm b c) s) =
      blockWalkCount ι s := by
  by_cases hs : s ≤ 2 * Fintype.card ι
  · apply degreeGenericPolynomial_spec
    have hp : ∏ t : Fin (2 * Fintype.card ι + 1),
        BooleanQuotient.pairParameterEvaluation a c (degreeGenericPolynomial t.val) ≠ 0 := by
      simpa only [matchingGenericPolynomial, map_prod] using h
    exact Finset.prod_ne_zero_iff.mp hp ⟨s, Nat.lt_succ_of_le hs⟩ (Finset.mem_univ _)
  · rw [blockWalkCount_eq_zero (by omega : Fintype.card ι < s)]
    have hdim : Module.finrank K M = 2 * Fintype.card ι := by
      rw [Module.finrank_eq_card_basis b, Fintype.card_sum]
      omega
    have hz := Submodule.finrank_quotient_add_finrank
      (exteriorDegreeRelations (matchingForm b a) (matchingForm b c) s)
    rw [exteriorPower.finrank_eq, Nat.choose_eq_zero_of_lt (by omega : Module.finrank K M < s)] at hz
    change Module.finrank K (ExteriorQuotientDegree (matchingForm b a) (matchingForm b c) s) + _ = 0 at hz
    omega

theorem generic_matching_hilbert (b : Module.Basis (ι ⊕ ι) K M) :
    ∃ p : MvPolynomial (Bool × ι) K, p ≠ 0 ∧
      ∀ a c : ι → K, BooleanQuotient.pairParameterEvaluation a c p ≠ 0 →
        ∀ s : ℕ, Module.finrank K
          (ExteriorQuotientDegree (matchingForm b a) (matchingForm b c) s) =
            blockWalkCount ι s :=
  ⟨matchingGenericPolynomial, matchingGenericPolynomial_ne_zero,
    fun a c h s => matchingGenericPolynomial_spec b a c h s⟩

theorem generic_matching_vanishing (b : Module.Basis (ι ⊕ ι) K M)
    (a c : ι → K)
    (h : BooleanQuotient.pairParameterEvaluation a c
      (matchingGenericPolynomial (K := K) (ι := ι)) ≠ 0)
    (s : ℕ) (hs : Fintype.card ι < s) :
    Module.finrank K (ExteriorQuotientDegree (matchingForm b a) (matchingForm b c) s) = 0 := by
  rw [matchingGenericPolynomial_spec b a c h s, blockWalkCount_eq_zero hs]

end PaperVerification.AlternatingForms.EvenSingletons
