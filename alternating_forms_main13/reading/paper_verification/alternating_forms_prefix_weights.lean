module

public import PaperVerification.AlternatingFormsExteriorCoordinates
public import PaperVerification.AlternatingFormsPrefixSupport
public import PaperVerification.WeightedInitialFiber

/-!
# Actual weights of the canonical prefix replacement states

The single positive vertex-weight vector is used for both odd-pencil
matchings.  A later matching pair lowers the weight strictly, for every
pair state occurring in the singleton-preserving inverse.  The Plücker
coordinate weight is proved to equal the exterior word weight.
-/

@[expose] public section
set_option autoImplicit false

noncomputable section

namespace PaperVerification.AlternatingForms

open scoped BigOperators
open MvPolynomial

variable {K : Type*} [Field K] {k s n : ℕ}

/-- The positive integral vertex weights as natural numbers, retaining their
exact integer values. -/
def oddNatVertexWeight (k : ℕ) (i : Fin (2*k+1)) : ℕ :=
  (oddPathVertexWeight k i).toNat

@[simp] theorem oddNatVertexWeight_cast (k : ℕ) (i : Fin (2*k+1)) :
    (oddNatVertexWeight k i : ℤ)=oddPathVertexWeight k i :=
  Int.toNat_of_nonneg (oddPathVertexWeight_positive k i).le

theorem canonicalPairWeight_replacement_strict (C : ℤ)
    (P T : Finset (Fin k)) (h : ℕ) (j : Fin k)
    (hP : ∀ i ∈ P,i.val<h) (hj : h≤j.val) (hc : P.card=T.card+1) :
    (∑ i ∈ T,(2*C-(2:ℤ)^(i.val+1)))+(2*C-(2:ℤ)^(j.val+1)) <
      ∑ i ∈ P,(2*C-(2:ℤ)^(i.val+1)) := by
  have hPi : P.image Fin.val ⊆ Finset.range h := by
    rintro _ ha
    obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp ha
    exact Finset.mem_range.mpr (hP i hi)
  have hz := replacement_pair_cost_strict (P.image Fin.val) (T.image Fin.val) h j.val hPi hj
  rw [Finset.sum_image (fun _ _ _ _ hij => Fin.val_injective hij),
    Finset.sum_image (fun _ _ _ _ hij => Fin.val_injective hij)] at hz
  have hz' : (∑ i ∈ P,(2:ℤ)^(i.val+1)) <
      (∑ i ∈ T,(2:ℤ)^(i.val+1))+(2:ℤ)^(j.val+1) := by exact_mod_cast hz
  simp only [Finset.sum_sub_distrib,Finset.sum_const,nsmul_eq_mul,hc,Nat.cast_add,Nat.cast_one]
  nlinarith

/-- Every actual first-matching replacement has smaller vertex weight.
The fixed singleton and suffix weights can be added to both sides unchanged. -/
theorem oddFirst_replacement_weight_strict (P T : Finset (Fin k)) (h : ℕ) (j : Fin k)
    (hP : ∀ i ∈ P,i.val<h) (hj : h≤j.val) (hc : P.card=T.card+1) :
    (∑ i ∈ T,(oddPathVertexWeight k (oddPathFirstLeft i)+
      oddPathVertexWeight k (oddPathMiddle i)))+
      (oddPathVertexWeight k (oddPathFirstLeft j)+oddPathVertexWeight k (oddPathMiddle j)) <
      ∑ i ∈ P,(oddPathVertexWeight k (oddPathFirstLeft i)+
        oddPathVertexWeight k (oddPathMiddle i)) := by
  simp only [oddPathFirst_pair_weight]
  exact canonicalPairWeight_replacement_strict
    (positiveWeightShift (oddPathVertexCost k)) P T h j hP hj hc

theorem oddSecond_pair_weight_reflected (i : Fin k) :
    oddPathVertexWeight k (oddPathMiddle i.rev)+
      oddPathVertexWeight k (oddPathSecondRight i.rev) =
        2*positiveWeightShift (oddPathVertexCost k)-(2:ℤ)^(i.val+1) := by
  have h := oddPathSecond_pair_cost_reflected i
  simp only [oddPathVertexWeight]
  omega

/-- The right-prefix replacement uses that very same weight vector, after
reflection, rather than an independently chosen monomial order. -/
theorem oddSecond_replacement_weight_strict (P T : Finset (Fin k)) (h : ℕ) (j : Fin k)
    (hP : ∀ i ∈ P,i.val<h) (hj : h≤j.val) (hc : P.card=T.card+1) :
    (∑ i ∈ T,(oddPathVertexWeight k (oddPathMiddle i.rev)+
      oddPathVertexWeight k (oddPathSecondRight i.rev)))+
      (oddPathVertexWeight k (oddPathMiddle j.rev)+
        oddPathVertexWeight k (oddPathSecondRight j.rev)) <
      ∑ i ∈ P,(oddPathVertexWeight k (oddPathMiddle i.rev)+
        oddPathVertexWeight k (oddPathSecondRight i.rev)) := by
  simp only [oddSecond_pair_weight_reflected]
  exact canonicalPairWeight_replacement_strict
    (positiveWeightShift (oddPathVertexCost k)) P T h j hP hj hc

/-- The weight of a Plücker variable is the sum of its actual vertex weights. -/
def pluckerVertexWeight (w : Fin n → ℕ) (I : PluckerIndex s n) : ℕ :=
  ∑ i,w (I.val i)

theorem orderedPluckerCoordinate_isWeightedHomogeneous (w : Fin n → ℕ)
    (I : Fin s → Fin n) :
    (orderedPluckerCoordinate (K := K) I).IsWeightedHomogeneous
      (pluckerVertexWeight w) (∑ i,w (I i)) := by
  classical
  unfold orderedPluckerCoordinate
  split_ifs with hI
  · have hweight : pluckerVertexWeight w (sortedPluckerIndex I hI)=∑ i,w (I i) := by
      exact Equiv.sum_comp (Tuple.sort I) (fun i => w (I i))
    have hx := isWeightedHomogeneous_X (R := K) (pluckerVertexWeight w)
      (sortedPluckerIndex I hI)
    rw [hweight] at hx
    exact (weightedHomogeneousSubmodule K (pluckerVertexWeight w) _).smul_mem _ hx
  · exact isWeightedHomogeneous_zero K _ _

/-- The coordinate map retains each ordered exterior word's weight, even
when a repeated vertex makes both sides zero. -/
theorem exteriorPluckerCoordinates_word_isWeightedHomogeneous (w : Fin n → ℕ)
    (I : Fin s → Fin n) :
    (exteriorPluckerCoordinates (K := K) s n
      (exteriorPower.ιMulti K s (fun i => Pi.basisFun K (Fin n) (I i)))).IsWeightedHomogeneous (pluckerVertexWeight w) (∑ i,w (I i)) := by
  rw [exteriorPluckerCoordinates_word]
  exact orderedPluckerCoordinate_isWeightedHomogeneous w I

end PaperVerification.AlternatingForms
