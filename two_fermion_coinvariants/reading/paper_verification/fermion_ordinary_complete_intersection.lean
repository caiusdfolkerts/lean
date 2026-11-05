module

public import PaperVerification.FermionOrdinaryParameters
public import PaperVerification.FermionCompleteIntersectionPairing

/-!
# The Frobenius pairing of the actual ordinary moment quotient

Support, regularity and finiteness are proved in the leaf module
`FermionOrdinaryParameters`; the Koszul socle comparison supplies the perfect
multiplication pairing here.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace PaperVerification.Fermion

open scoped BigOperators
open MvPolynomial

variable {K : Type*} [Field K] {n : ℕ}

/-- The ordinary quotient in Section 4 has a perfect multiplication pairing,
derived from its actual moment generators and subset-sum hypotheses. -/
theorem powerMoment_quotient_frobenius
    (r : Fin n → ℕ) (β : Fin n → K) (s : ℕ)
    (hr : ∀ i, 0 < r i) (hs : 0 < s)
    (hβ : ∀ U : Finset (Fin n), U.Nonempty → IsUnit (∑ i ∈ U, β i)) :
    ∃ ε : (MvPolynomial (Fin n) K ⧸ powerMomentIdeal r β s) →ₗ[K] K,
      (multiplicationPairing ε).IsPerfPair := by
  letI := powerMoment_quotient_finite r β s hβ
  letI : Module.Finite K (MvPolynomial (Fin n) K ⧸
      Ideal.span (Set.range fun k : Fin n ↦ powerMoment r β s k)) :=
    powerMoment_quotient_finite r β s hβ
  apply exists_frobenius_of_regular_sequence polynomialOrigin MvPolynomial.X
    (fun k : Fin n ↦ powerMoment r β s k) span_variables_eq_origin
    (powerMoments_isWeaklyRegular r β s hr hs hβ)
  rw [← originIdeal_eq_polynomialOrigin_ker]
  exact powerMoment_radical_eq_origin r β s hr hs hβ

end PaperVerification.Fermion
