module
public import two_fermion

@[expose] public section
noncomputable section
set_option autoImplicit false
open scoped BigOperators

namespace PalomarFermion
open PaperVerification.Fermion
variable {R : Type*} [CommRing R] {n : ℕ}

/-- The paired quotient's finite free rank, from the proved full rank theorem. -/
theorem pairedFreeRank (d : PairedData (K := R) (n := n)) :
    Nonempty (PairedQuotient d.beta d.phi d.a d.b ≃ₗ[R]
      (Fin (2^n * (∏ i, d.r i) * d.s.ascFactorial n) → R)) :=
  (PaperVerification.Fermion.theorem_1_1_free_rank d).1

/-- The strict quotient's finite free rank, from the proved full rank theorem. -/
theorem strictFreeRank (d : StrictData (K := R) (n := n)) :
    Nonempty (StrictQuotient d.beta d.phi ≃ₗ[R]
      (Fin (2^(n-1) * (∏ i, d.r i) * n.factorial) → R)) :=
  (PaperVerification.Fermion.theorem_1_2_free_rank d).1

end PalomarFermion
