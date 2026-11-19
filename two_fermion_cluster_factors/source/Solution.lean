module
public import two_fermion
@[expose] public section
noncomputable section
namespace PaperVerification.Fermion
open scoped Classical BigOperators
theorem localFactorPresentation {F : Type} [Field F] [CharZero F] [IsAlgClosed F] {n : ℕ}
    (d : SeparatedPairedData F n) :
    ∀ (rho : d.O.SupportPoint) (c : Fin (Fintype.card (d.O.PointCluster rho))),
      ∃ e : ((d.localClusterFamily rho).factor c).Carrier ≃ₐ[F]
        PairedQuotient (d.localFactorPairedData rho c).beta
          (d.localFactorPairedData rho c).phi
          (d.localFactorPairedData rho c).a
          (d.localFactorPairedData rho c).b,
        ∀ g x,e x∈d.localFactorPairedBigradedPart rho c g ↔
          x∈((d.localClusterFamily rho).factorBigrading c).part g := (theorem_7_2 d).2.2.2.2
end PaperVerification.Fermion
