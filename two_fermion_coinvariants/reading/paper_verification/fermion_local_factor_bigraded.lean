module

public import PaperVerification.FermionLocalPairedFactors
public import PaperVerification.FermionSingleClusterBigraded

/-!
# Faithful exterior-bigraded identification of every paired cluster factor

-/

@[expose] public section
set_option autoImplicit false
noncomputable section
open scoped Classical

namespace PaperVerification.Fermion
namespace SeparatedPairedData

variable {F : Type} [Field F] [CharZero F] [IsAlgClosed F] {n : ℕ}
  (d : SeparatedPairedData F n) (rho : d.O.SupportPoint)
  (c : Fin (Fintype.card (d.O.PointCluster rho)))

local instance FermionLocalFactorBigraded_factorOddOrder :
    LinearOrder (d.LocalFactorIndex rho c⊕d.LocalFactorIndex rho c) := finiteIndexLinearOrder _
local instance FermionLocalFactorBigraded_originalOddOrder :
    LinearOrder (Fin (Fintype.card (d.LocalFactorIndex rho c))⊕
      Fin (Fintype.card (d.LocalFactorIndex rho c))) := finiteIndexLinearOrder _

def localFactorPairedBigradedPart (g : ℕ×ℕ) :
    Submodule F (PairedQuotient (d.localFactorPairedData rho c).beta
      (d.localFactorPairedData rho c).phi
      (d.localFactorPairedData rho c).a
      (d.localFactorPairedData rho c).b) :=
  let p := d.localFactorPairedData rho c
  pairedPowerBigradedPart p.beta p.allowed_weights.2 p.r p.positive_r p.s p.positive_s
    p.u p.v p.degree_split g

set_option maxHeartbeats 1000000 in
/-- The factor bridge is exterior-bigraded for independently defined
original exterior-word image components on both sides. -/
theorem localFactorBigradedEquivPaired :
    ∃ e : ((d.localClusterFamily rho).factor c).Carrier ≃ₐ[F]
      PairedQuotient (d.localFactorPairedData rho c).beta
        (d.localFactorPairedData rho c).phi
        (d.localFactorPairedData rho c).a
        (d.localFactorPairedData rho c).b,
      ∀ g x,e x∈d.localFactorPairedBigradedPart rho c g ↔
        x∈((d.localClusterFamily rho).factorBigrading c).part g := by
  let p := d.localFactorPairedData rho c
  let eIndex := singleClusterFinParameterEquiv
    ((d.localClusterFamily rho).beta c) ((d.localClusterFamily rho).r c)
    ((d.localClusterFamily rho).s c) ((d.localClusterFamily rho).u c)
    ((d.localClusterFamily rho).v c)
  obtain ⟨ePower,hPower⟩ := pairedPowerBigradedEquivExists p.beta p.allowed_weights.2
    p.r p.positive_r p.s p.positive_s p.u p.v p.degree_split
  refine ⟨eIndex.algEquiv.trans ePower.symm,?_⟩
  intro g x
  have hp := hPower g (ePower.symm (eIndex.algEquiv x))
  rw [AlgEquiv.apply_symm_apply ePower (eIndex.algEquiv x)] at hp
  exact hp.symm.trans (eIndex.algEquiv_bigraded_iff g x)

end SeparatedPairedData
end PaperVerification.Fermion

