module

public import PaperVerification.AlternatingFormsHibiDegeneration
public import PaperVerification.AlternatingFormsHibiWeights
public import PaperVerification.WeightedMonicNormalForm

/-!
# Diagonal control of the actual Richardson normal form

Coefficients are defined by the proved basis of the actual interval
Plücker quotient. Mapping its full finite expansion into the band matrix
ring proves the diagonal bound. At the greatest diagonal weight the
product of two minors has precisely its meet/join chain, with coefficient
one. No straightening coefficient or triangularity condition is assumed.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace PaperVerification.AlternatingForms.Hibi

open MvPolynomial
open scoped BigOperators
open WeightedSagbi WeightedInitialFiber

variable {K : Type*} [Field K] [CharZero K] {s n : ℕ}
  (α β : Fin s → Fin n)

/-- The actual sorted two-column chain. -/
def pairChain (I J : IntervalIndex α β) : Σ r,BandChain α β r :=
  ⟨2,chainOfList α β [meet α β I J,join α β I J] (by
    refine List.pairwise_cons.mpr ⟨?_, by simp⟩
    intro x hx
    have hx' : x = join α β I J := by simpa only [List.mem_singleton] using hx
    subst x
    exact (meet_le_left α β I J).trans (left_le_join α β I J))⟩

theorem standardPolynomial_pairChain (I J : IntervalIndex α β) :
    standardPolynomial (K := K) α β (pairChain α β I J).2=
      X (meet α β I J)*X (join α β I J) := by
  rw [pairChain,standardPolynomial_chainOfList]
  simp only [word_cons,word_nil,mul_one]

theorem pairChain_diagonal (I J : IntervalIndex α β) :
    chainDiagonalExponent (pairChain α β I J).2.val=
      diagonalExponent α β I+diagonalExponent α β J := by
  change (∑ j : Fin 2,
    minorTermExponent (([meet α β I J,join α β I J].get j).val.val) 1)=_
  rw [Fin.sum_univ_two]
  exact pair_exponents α β I J

theorem pairChain_diagonalWeight (I J : IntervalIndex α β) :
    standardDiagonalWeight α β (pairChain α β I J)=
      diagonalWeight α β I+diagonalWeight α β J := by
  rw [←chainDiagonalExponent_weight,pairChain_diagonal,map_add]
  rfl

theorem pairChain_sum_weight (w : IntervalIndex α β → ℕ)
    (I J : IntervalIndex α β) :
    (∑ j,w (intervalIndexOfChain α β (pairChain α β I J).2 j))=
      w (meet α β I J)+w (join α β I J) := by
  simp only [pairChain,Fin.sum_univ_two,intervalIndexOfChain,chainOfList]
  rfl

variable (hα : Monotone α) (hβ : Monotone β) (hs : 0<s)

def intervalCoefficients (p : MvPolynomial (PluckerIndex s n) K) :
    (Σ r,BandChain α β r) →₀ K :=
  (intervalStandardBasis (K := K) α β hα hβ hs).repr (Ideal.Quotient.mk _ p)

theorem intervalCoefficients_band_expansion (p : MvPolynomial (PluckerIndex s n) K) :
    (intervalCoefficients (K := K) α β hα hβ hs p).sum
      (fun C c => c • bandStandardProduct (K := K) α β C.2)=bandPluckerMap (K := K) α β p := by
  have h := congrArg (intervalBandMap (K := K) α β hα hβ)
    ((intervalStandardBasis (K := K) α β hα hβ hs).linearCombination_repr
      (Ideal.Quotient.mk _ p))
  have hm : intervalBandMap (K := K) α β hα hβ (Ideal.Quotient.mk _ p) =
      bandPluckerMap (K := K) α β p := rfl
  rw [hm] at h
  simpa only [Finsupp.linearCombination_apply,Finsupp.sum,map_sum,map_smul,
    intervalStandardBasis,Module.Basis.mk_apply,intervalAllStandardProduct,
    intervalBandMap_standardProduct,intervalCoefficients] using h

theorem intervalCoefficients_diagonal_le
    (p : MvPolynomial (PluckerIndex s n) K) (d : ℕ)
    (hp : WeightBound diagonalEntryWeight d (bandPluckerMap (K := K) α β p))
    (C : Σ r,BandChain α β r) (hc : intervalCoefficients (K := K) α β hα hβ hs p C≠0) :
    standardDiagonalWeight α β C≤d := by
  apply expansion_degree_le diagonalEntryWeight
    (fun C : Σ r,BandChain α β r => bandStandardProduct (K := K) α β C.2)
    (fun C => chainDiagonalExponent C.2.val) (standardDiagonalWeight α β)
    (allChainDiagonalExponent_injective α β hs)
    (fun C => by rw [diagonalEntryWeight_cast]; exact bandStandardProduct_weightMonic α β C.2)
    (chainDiagonalExponent_weight α β)
    (intervalCoefficients (K := K) α β hα hβ hs p) d ?_ C hc
  rwa [intervalCoefficients_band_expansion]

theorem band_pair_weightMonic (I J : IntervalIndex α β) :
    IsWeightMonic (fun i => (diagonalEntryWeight i : ℤ))
      (bandPluckerMap (K := K) α β (X I.val*X J.val : MvPolynomial (PluckerIndex s n) K))
      (diagonalExponent α β I+diagonalExponent α β J) := by
  simp only [bandPluckerMap,map_mul,aeval_X]
  exact (bandMinor_diagonal_weightMonic α β I).mul
    (bandMinor_diagonal_weightMonic α β J)

theorem interval_pair_diagonal_le (I J : IntervalIndex α β)
    (C : Σ r,BandChain α β r)
    (hc : intervalCoefficients (K := K) α β hα hβ hs (X I.val*X J.val) C≠0) :
    standardDiagonalWeight α β C≤diagonalWeight α β I+diagonalWeight α β J := by
  apply intervalCoefficients_diagonal_le (K := K) α β hα hβ hs _ _ ?_ C hc
  simpa only [map_add,diagonalWeight,inducedWeight] using
    weightBound_of_weightMonic diagonalEntryWeight _ _ (band_pair_weightMonic (K := K) α β I J)

/-- The unique possible greatest-diagonal-weight term is the actual
meet/join chain, in the full basis over all chain lengths. -/
theorem interval_pair_top_chain (I J : IntervalIndex α β)
    (C : Σ r,BandChain α β r)
    (hc : intervalCoefficients (K := K) α β hα hβ hs (X I.val*X J.val) C≠0)
    (hd : standardDiagonalWeight α β C=diagonalWeight α β I+diagonalWeight α β J) :
    C=pairChain α β I J := by
  apply allChainDiagonalExponent_injective α β hs
  change chainDiagonalExponent C.2.val = chainDiagonalExponent (pairChain α β I J).2.val
  rw [pairChain_diagonal]
  apply expansion_monic_top_exponent diagonalEntryWeight
    (fun C : Σ r,BandChain α β r => bandStandardProduct (K := K) α β C.2)
    (fun C => chainDiagonalExponent C.2.val) (standardDiagonalWeight α β)
    (allChainDiagonalExponent_injective α β hs)
    (fun C => by rw [diagonalEntryWeight_cast]; exact bandStandardProduct_weightMonic α β C.2)
    (chainDiagonalExponent_weight α β)
    (intervalCoefficients (K := K) α β hα hβ hs (X I.val*X J.val)) _ _
    (band_pair_weightMonic (K := K) α β I J)
    (intervalCoefficients_band_expansion (K := K) α β hα hβ hs _) C hc
  simpa only [map_add,diagonalWeight,inducedWeight] using hd

theorem interval_pair_top_coefficient (I J : IntervalIndex α β) :
    intervalCoefficients (K := K) α β hα hβ hs (X I.val*X J.val) (pairChain α β I J)=1 := by
  apply expansion_monic_top_coefficient diagonalEntryWeight
    (fun C : Σ r,BandChain α β r => bandStandardProduct (K := K) α β C.2)
    (fun C => chainDiagonalExponent C.2.val) (standardDiagonalWeight α β)
    (allChainDiagonalExponent_injective α β hs)
    (fun C => by rw [diagonalEntryWeight_cast]; exact bandStandardProduct_weightMonic α β C.2)
    (chainDiagonalExponent_weight α β)
    (intervalCoefficients (K := K) α β hα hβ hs (X I.val*X J.val)) _ _
    (band_pair_weightMonic (K := K) α β I J)
    (intervalCoefficients_band_expansion (K := K) α β hα hβ hs _) (pairChain α β I J)
  exact pairChain_diagonal α β I J

end PaperVerification.AlternatingForms.Hibi
