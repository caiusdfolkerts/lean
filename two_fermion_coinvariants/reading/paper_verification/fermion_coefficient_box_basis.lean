module

public import PaperVerification.FermionAdmissibleExteriorBlocks

/-! The actual coefficient-colon monomial basis, separated from optional
rational representation theory without changing its definitions or proofs.
 -/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical BigOperators TensorProduct

namespace PaperVerification.Fermion.TypeA

variable {F : Type*} [Field F] [CharZero F] {n : ℕ}

/-- The actual monomial basis of each actual coefficient colon quotient. -/
def coefficientBoxBasis (hn : 0<n) (m : MultiplicityVector n) :
    Module.Basis (StrictWordPolynomialIndex (fun _ : Fin n ↦ 1) (canonicalWord m)) F
      (CoefficientQuotient (F := F) m) :=
  (strictMultiplicityColonBasis (data (F := F) hn) (canonicalWord m)).map
    ((Ideal.quotientEquivAlgOfEq F (by
      rw [ordinaryIdeal_eq,canonicalWord_multiplicity]
      rfl)).toLinearEquiv)

@[simp] theorem coefficientBoxBasis_apply (hn : 0<n) (m : MultiplicityVector n)
    (a : StrictWordPolynomialIndex (fun _ : Fin n ↦ 1) (canonicalWord m)) :
    coefficientBoxBasis (F := F) hn m a=
      Ideal.Quotient.mk (coefficientIdeal (F := F) m) (MvPolynomial.monomial a.val.val 1) := by
  let d := data (F := F) hn
  let T := canonicalWord m
  let e₁ := Ideal.quotientEquivAlgOfEq F (creatorColon_eq_multiplicityColon d T)
  have hI : principalColon (coupledOrdinaryIdeal d.pairedExtension)
      (multiplicityFactor d.phi (wordMultiplicityVector T))=coefficientIdeal (F := F) m := by
    dsimp only [d,T]
    rw [ordinaryIdeal_eq,canonicalWord_multiplicity]
    rfl
  let e₂ := Ideal.quotientEquivAlgOfEq F hI
  change e₂ (e₁ (strictCreatorColonBasis d T a))=_
  have h := congrArg (fun x ↦ e₂ (e₁ x))
    (strictCreatorColonBasis_apply (F := F) d T a)
  simpa only [e₁,e₂,Ideal.quotientEquivAlgOfEq_mk] using h

end PaperVerification.Fermion.TypeA
