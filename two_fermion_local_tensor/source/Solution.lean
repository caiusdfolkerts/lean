module
public import two_fermion
@[expose] public section
noncomputable section
namespace PaperVerification.Fermion
open scoped Classical BigOperators
theorem localTensorDecomposition {F : Type} [Field F] [CharZero F] [IsAlgClosed F] {n : ℕ}
    (d : SeparatedPairedData F n) :
    ∀ rho : d.O.SupportPoint,∃ e :
        d.LocalSuper rho ≃ₐ[F] (d.localClusterFamily rho).tensor.Carrier,
      ∀ g x,e x∈(d.localClusterFamily rho).tensorBigrading.part g ↔
        x∈d.localSuperBigradedPart rho g := (theorem_7_2 d).2.1
end PaperVerification.Fermion
