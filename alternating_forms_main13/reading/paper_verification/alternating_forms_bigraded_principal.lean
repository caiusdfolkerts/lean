module

public import PaperVerification.AlternatingFormsBigradedPieces
public import PaperVerification.AlternatingFormsGoodWalkWeights
public import PaperVerification.AlternatingFormsTransferSeries
public import Mathlib.Algebra.BigOperators.NatAntidiagonal

/-!
# Proposition 5.1 in its full printed parameter range

The left side uses the actual images of the original bidegree exterior-word
spans in the actual quotient by the two canonical odd quadrics.  The right
side is the coefficient of the genuine formal reciprocal of the printed
recurrence polynomial.  The proof uses the actual homogeneous good basis,
the complete weight-preserving bounded-walk equivalence, and the all-size
matrix resolvent identity.  No dimension, generic-rank, or counting premise
is introduced.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical

namespace PaperVerification.AlternatingForms

open Bidegree GoodPaths BigradedTransfer

/-- The pure combinatorial and algebraic good indices have identical data
and identical inequalities; this equivalence changes no selected position. -/
def goodPathExteriorIndexEquiv (k s : ℕ) : GoodOddIndex k s ≃ GoodPathIndex k s :=
  Equiv.refl _

@[simp] theorem goodPathExteriorIndexEquiv_degree {k s : ℕ} (I : GoodOddIndex k s) :
    indexADegree (goodPathExteriorIndexEquiv k s I).val.val=goodADegree I := rfl

def goodDegreeIndex {k s : ℕ} (I : GoodOddIndex k s) : Fin (s+1) :=
  ⟨goodADegree I,Nat.lt_succ_of_le (indexADegree_le I.val.val)⟩

theorem goodDegreeIndex_fiber_card (k s : ℕ) (p : Fin (s+1)) :
    Nat.card {I : GoodOddIndex k s // goodDegreeIndex I=p}=
      Nat.card {I : GoodOddIndex k s // goodADegree I=p.val} := by
  apply Nat.card_congr
  exact Equiv.subtypeEquivRight (fun I => by
    change (⟨goodADegree I,_⟩ : Fin (s+1))=p ↔ goodADegree I=p.val
    exact Fin.ext_iff)

/-- Counting actual finite fibers is equivalent to summing their elements. -/
theorem sum_fiber_card_weight {I D R : Type*} [Fintype I] [Fintype D]
    [CommRing R] (δ : I → D) (f : D → R) :
    (∑ d,(Nat.card {i : I // δ i=d} : R)*f d)=∑ i,f (δ i) := by
  simpa only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,Nat.card_eq_fintype_card]
    using (Fintype.sum_fiberwise' δ f)

section ActualHilbertFunction

variable {K R : Type*} [Field K] [CharZero K] [CommRing R]

/-- The exact finite total-degree slice of the genuine quotient bigrading. -/
def bigradedHilbertSlice (k s : ℕ) (u v : R) : R :=
  ∑ p : Fin (s+1),(Module.finrank K (quotientASubdegree (K := K) k s p.val) : R)*
    u^p.val*v^(s-p.val)

theorem bigradedHilbertSlice_good_sum (k s : ℕ) (u v : R) :
    bigradedHilbertSlice (K := K) k s u v=
      ∑ I : GoodPathIndex k s,u^indexADegree I.val.val*v^(s-indexADegree I.val.val) := by
  calc
    _ = ∑ p : Fin (s+1),(Nat.card {I : GoodOddIndex k s // goodDegreeIndex I=p} : R)*
        (u^p.val*v^(s-p.val)) := by
      unfold bigradedHilbertSlice
      apply Finset.sum_congr rfl
      intro p hp
      rw [finrank_quotientASubdegree,←goodDegreeIndex_fiber_card]
      exact mul_assoc _ _ _
    _ = ∑ I : GoodOddIndex k s,u^(goodDegreeIndex I).val*v^(s-(goodDegreeIndex I).val) :=
      sum_fiber_card_weight goodDegreeIndex (fun p : Fin (s+1) => u^p.val*v^(s-p.val))
    _ = _ := Equiv.sum_comp (goodPathExteriorIndexEquiv k s)
      (fun I : GoodPathIndex k s => u^indexADegree I.val.val*v^(s-indexADegree I.val.val))

/-- The entire all-size coefficient identity, with the actual quotient pieces. -/
theorem bigradedHilbertSlice_coefficient (k s : ℕ) (hs : s≤k+1) (u v : R) :
    bigradedHilbertSlice (K := K) k s u v=
      PowerSeries.coeff s (inverseDenominator u v (k+2-s)) := by
  rw [bigradedHilbertSlice_good_sum,good_index_weight_sum k s hs]
  have hN : s+(k+1-s)=k+1 := by omega
  have hm : k+1-s+1=k+2-s := by omega
  simpa only [hN,hm] using transfer_power_entry (k+1-s) s u v

/-- Numbered Proposition 5.1, with the printed sum over all `p+q=s`.
`actualBigradedPiece` is defined from the original exterior words, and the
finite-antidiagonal identity proves equivalence to the finite slice above. -/
theorem paper_proposition_5_1 (k s : ℕ) (hs : s≤k+1) (u v : R) :
    (∑ pq∈Finset.antidiagonal s,
      (Module.finrank K (actualBigradedPiece (K := K) k pq.1 pq.2) : R)*
        u^pq.1*v^pq.2)=
      PowerSeries.coeff s (inverseDenominator u v (k+2-s)) := by
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk,
    ←Fin.sum_univ_eq_sum_range]
  calc
    _ = bigradedHilbertSlice (K := K) k s u v := by
      unfold bigradedHilbertSlice
      apply Finset.sum_congr rfl
      intro p hp
      have he : p.val+(s-p.val)=s := by have := p.isLt; omega
      have hdim := congrArg
        (fun d : ℕ => Module.finrank K (quotientASubdegree (K := K) k d p.val)) he
      exact congrArg (fun d : ℕ => (d : R)*u^p.val*v^(s-p.val)) hdim
    _ = _ := bigradedHilbertSlice_coefficient k s hs u v

end ActualHilbertFunction
end PaperVerification.AlternatingForms
