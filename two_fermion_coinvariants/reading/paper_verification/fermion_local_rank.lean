module

public import PaperVerification.FermionTheoremSevenTwo
public import PaperVerification.FermionPairedRank
public import Mathlib.LinearAlgebra.Dimension.Constructions

/-!
# Exact dimensions of the actual local factors

The signed tensor product has the ordinary tensor product as its underlying
vector space. The factor bases are the original paired bases with all
hypotheses discharged by the root data. The final formula counts every
original coordinate once through the actual cluster partition.
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical BigOperators TensorProduct

namespace PaperVerification.Fermion

namespace NGradedAlgebra

variable {F : Type*} [Field F]

theorem tensor_finrank (A B : NGradedAlgebra F) :
    Module.finrank F (tensor F A B).Carrier=
      Module.finrank F A.Carrier*Module.finrank F B.Carrier := by
  change Module.finrank F (A.part ᵍ⊗[F] B.part) =
    Module.finrank F A.Carrier * Module.finrank F B.Carrier
  rw [←(GradedTensorProduct.of F A.part B.part).finrank_eq]
  exact Module.finrank_tensorProduct

theorem tensorFin_finrank {m : ℕ} (A : Fin m → NGradedAlgebra F) :
    Module.finrank F (tensorFin A).Carrier=∏ i,Module.finrank F (A i).Carrier := by
  induction m with
  | zero =>
      change Module.finrank F F = ∏ i : Fin 0, Module.finrank F (A i).Carrier
      simpa only [Fin.prod_univ_zero] using (Module.finrank_self F)
  | succ m ih =>
      rw [tensorFin,tensor_finrank,ih,Fin.prod_univ_succ]

theorem tensorFin_finite {m : ℕ} (A : Fin m → NGradedAlgebra F)
    (hA : ∀ i,Module.Finite F (A i).Carrier) :
    Module.Finite F (tensorFin A).Carrier := by
  induction m with
  | zero => exact inferInstanceAs (Module.Finite F F)
  | succ m ih =>
      letI := hA 0
      letI := ih (fun i : Fin m ↦ A i.succ) (fun i ↦ hA i.succ)
      exact Module.Finite.equiv (GradedTensorProduct.of F (A 0).part
        (tensorFin (fun i : Fin m ↦ A i.succ)).part)

end NGradedAlgebra

namespace SeparatedPairedData

variable {F : Type} [Field F] [CharZero F] [IsAlgClosed F] {n : ℕ}
  (d : SeparatedPairedData F n) (rho : d.O.SupportPoint)

local instance : Fintype d.O.SupportPoint := Fintype.ofFinite _

theorem localFactor_finite (c : Fin (Fintype.card (d.O.PointCluster rho))) :
    Module.Finite F ((d.localClusterFamily rho).factor c).Carrier := by
  let p := d.localFactorPairedData rho c
  letI := Module.Finite.of_basis (pairedPaperBasis p)
  exact Module.Finite.equiv (d.localFactorEquivPaired rho c).symm.toLinearEquiv

theorem localTensor_finite :
    Module.Finite F (d.localClusterFamily rho).tensor.Carrier :=
  NGradedAlgebra.tensorFin_finite _ (d.localFactor_finite rho)

theorem localSuper_finite : Module.Finite F (d.LocalSuper rho) := by
  letI := d.localTensor_finite rho
  exact Module.Finite.equiv (d.localSuperTensorEquiv rho).symm.toLinearEquiv

theorem localFactor_finrank (c : Fin (Fintype.card (d.O.PointCluster rho))) :
    Module.finrank F ((d.localClusterFamily rho).factor c).Carrier=
      2^Fintype.card (d.LocalFactorIndex rho c)*
        (∏ j : Fin (Fintype.card (d.LocalFactorIndex rho c)),
          d.O.ramificationOrder rho (d.localFactorIndex rho c j))*
        ((d.localClusterFamily rho).s c).ascFactorial
          (Fintype.card (d.LocalFactorIndex rho c)) := by
  rw [(d.localFactorEquivPaired rho c).toLinearEquiv.finrank_eq,paired_finrank]
  rfl

theorem localFactor_card_sum :
    (∑ c : Fin (Fintype.card (d.O.PointCluster rho)),
      Fintype.card (d.LocalFactorIndex rho c))=n := by
  rw [←Fintype.card_sigma,←Fintype.card_congr (d.localClusterIndexEquiv rho),
    Fintype.card_fin]

theorem localFactor_ramification_product :
    (∏ c : Fin (Fintype.card (d.O.PointCluster rho)),
      ∏ j : Fin (Fintype.card (d.LocalFactorIndex rho c)),
        d.O.ramificationOrder rho (d.localFactorIndex rho c j))=
      ∏ i,d.O.ramificationOrder rho i := by
  have h c : (∏ j : Fin (Fintype.card (d.LocalFactorIndex rho c)),
      d.O.ramificationOrder rho (d.localFactorIndex rho c j))=
      ∏ i : (d.localClusterFamily rho).Index c,d.O.ramificationOrder rho i.1 :=
    (Fintype.equivFin (d.LocalFactorIndex rho c)).symm.prod_comp
      (fun i ↦ d.O.ramificationOrder rho i.1)
  simp_rw [h]
  rw [← Fintype.prod_sigma' (fun c (i : (d.localClusterFamily rho).Index c) ↦
    d.O.ramificationOrder rho i.val)]
  have he := (d.localClusterIndexEquiv rho).prod_comp
    (fun i ↦ d.O.ramificationOrder rho i.2.1)
  simpa only [d.localClusterIndexEquiv_value] using he.symm

/-- The exact local-rank formula printed after Theorem 7.2, on the actual
localized superalgebra and with the full ramification orders. -/
theorem localSuper_finrank :
    Module.finrank F (d.LocalSuper rho)=
      2^n*(∏ i,d.O.ramificationOrder rho i)*
        ∏ c : Fin (Fintype.card (d.O.PointCluster rho)),
          ((d.localClusterFamily rho).s c).ascFactorial
            (Fintype.card (d.LocalFactorIndex rho c)) := by
  rw [(d.localSuperTensorEquiv rho).toLinearEquiv.finrank_eq]
  change Module.finrank F (NGradedAlgebra.tensorFin (d.localClusterFamily rho).factor).Carrier=_
  rw [NGradedAlgebra.tensorFin_finrank]
  simp_rw [d.localFactor_finrank]
  rw [Finset.prod_mul_distrib,Finset.prod_mul_distrib,
    Finset.prod_pow_eq_pow_sum,d.localFactor_card_sum,
    d.localFactor_ramification_product]

/-- Every support point contributes its actual local dimension; no reduced
fiber or set of selected roots is substituted in this product formula. -/
theorem globalSuper_finrank_sum :
    Module.finrank F d.SuperQuotient=
      ∑ rho : d.O.SupportPoint,
        2^n*(∏ i,d.O.ramificationOrder rho i)*
          ∏ c : Fin (Fintype.card (d.O.PointCluster rho)),
            ((d.localClusterFamily rho).s c).ascFactorial
              (Fintype.card (d.LocalFactorIndex rho c)) := by
  letI : ∀ rho : d.O.SupportPoint,Module.Finite F (d.LocalSuper rho) := d.localSuper_finite
  letI : ∀ rho : d.O.SupportPoint,Module.Free F (d.LocalSuper rho) :=
    fun rho ↦ Module.Free.of_divisionRing F (d.LocalSuper rho)
  rw [d.superProductOverSupport.toLinearEquiv.finrank_eq,Module.finrank_pi_fintype]
  exact Finset.sum_congr rfl (fun rho _ ↦ d.localSuper_finrank rho)

end SeparatedPairedData
end PaperVerification.Fermion
