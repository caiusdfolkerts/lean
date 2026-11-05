module

public import PaperVerification.FermionDescendingGradedAction
public import PaperVerification.FermionMultiplicityAssociatedGraded
public import PaperVerification.FermionColorReesFibers
public import PaperVerification.FermionNaturalColorBlocks

/-!
# Equivariance of the actual multiplicity associated graded

The source action is induced from the original simultaneous color action on
F_d/F_(d+1).  The target action is the separately constructed action on the
literal initial quotient. Their equality follows on the complete actual
basis from the full normal-form formula. Composing with natural exterior
multiplication gives the equivariant tensor-block comparison in Theorem8.1.

No group action or multiplication is defined by transporting the desired
conclusion through a vector-space isomorphism. 
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical BigOperators DirectSum

namespace PaperVerification.Fermion.TypeA


open MvPolynomial Exterior

variable {F : Type*} [Field F] [CharZero F] {n : ℕ}

local instance FermionColorAssociatedGraded_localInst_1 : LinearOrder (OddIndex n) :=
  LinearOrder.lift' modeRank modeRank_injective

/-- The action on the actual direct sum F_d/F_(d+1), induced before comparison. -/
def gradedColorAction (hn : 0<n) :
    Matrix.GeneralLinearGroup (Fin 2) F →*
      (StrictMultiplicityAssociatedGraded (data (F := F) hn) ≃ₐ[F]
        StrictMultiplicityAssociatedGraded (data (F := F) hn)) :=
  DescendingAlgebra.associatedAction (strictMultiplicityDescendingFiltration (data (F := F) hn))
    (ColorAction.quotientAction (fun i : Fin n ↦ (X i : PolynomialRing F n)))
    (fun g r x ↦ color_preserves_basisTail hn g r x)

/-- The comparison with the initial quotient intertwines the actual actions. -/
theorem multiplicityAssociatedGraded_color_equivariant (hn : 0<n)
    (g : Matrix.GeneralLinearGroup (Fin 2) F)
    (x : StrictMultiplicityAssociatedGraded (data (F := F) hn)) :
    strictMultiplicityAssociatedGradedEquiv (data (F := F) hn) (gradedColorAction (F := F) hn g x)=
      diagonalInitialAction (F := F) hn g (strictMultiplicityAssociatedGradedEquiv (data (F := F) hn) x) := by
  let d := data (F := F) hn
  let E := strictMultiplicityAssociatedGradedEquiv d
  let G := gradedColorAction (F := F) hn g
  let H := diagonalInitialAction (F := F) hn g
  let B := DescendingBasis.gradedBasis (K := F) (A := StrictQuotient d.beta d.phi)
    (strictCoupledBasis d)
    (strictBasisMultiplicityWeight d) (strictBasisMultiplicityWeight_multiplicative d)
  have hb (i : StrictPowerIndex d.r) : E (G (B i))=H (E (B i)) := by
    have hEi := strictMultiplicityAssociatedGradedEquiv_basis d i
    have hHi := diagonalInitialAction_basis (F := F) hn g i
    change E (B i)=strictMultiplicityInitialBasis d i at hEi
    change H (strictMultiplicityInitialBasis d i)=_ at hHi
    conv_rhs => rw [hEi,hHi]
    change E
      (DescendingAlgebra.associatedEquiv (strictMultiplicityDescendingFiltration d)
        (ColorAction.quotientEquiv (R := F) g (fun k ↦ X k))
        (fun r y ↦ color_preserves_basisTail (F := F) hn g r y)
        (DescendingBasis.gradedBasis (K := F) (A := StrictQuotient d.beta d.phi)
          (strictCoupledBasis d)
          (strictBasisMultiplicityWeight d) (strictBasisMultiplicityWeight_multiplicative d) i))=_
    rw [DescendingBasis.gradedBasis_apply,DescendingAlgebra.associatedEquiv_of_mk,
      strictMultiplicityAssociatedGradedEquiv_of_mk]
    rfl
  have he : E.toLinearMap.comp G.toLinearMap=H.toLinearMap.comp E.toLinearMap := by
    apply B.ext
    intro i
    exact hb i
  have hx := LinearMap.congr_fun he x
  exact hx

/-- The natural direct-sum comparison of the actual associated graded. -/
def naturalAssociatedGradedEquiv (hn : 0<n) :
    StrictMultiplicityAssociatedGraded (data (F := F) hn) ≃ₗ[F]
      ⨁ m : {m : MultiplicityVector n // Admissible m},
        ExteriorCoefficientBlock (F := F) m.val :=
  (strictMultiplicityAssociatedGradedEquiv (data (F := F) hn)).toLinearEquiv.trans
    (naturalInitialAdmissibleEquiv (F := F) hn)

/-- The target has its ordinary exterior representation, including every
admissible block and the diagonal restriction of independent color changes. -/
theorem naturalAssociatedGradedEquiv_intertwines (hn : 0<n)
    (g : Matrix.GeneralLinearGroup (Fin 2) F)
    (x : StrictMultiplicityAssociatedGraded (data (F := F) hn)) :
    naturalAssociatedGradedEquiv (F := F) hn (gradedColorAction (F := F) hn g x)=
      naturalAdmissibleRepresentation (F := F) (fun _ ↦ g) (naturalAssociatedGradedEquiv (F := F) hn x) := by
  simp only [naturalAssociatedGradedEquiv,LinearEquiv.trans_apply,
    AlgEquiv.toLinearEquiv_apply]
  rw [multiplicityAssociatedGraded_color_equivariant]
  have hx := naturalInitialAdmissibleEquiv_intertwines (F := F) hn (fun _ ↦ g)
    (strictMultiplicityAssociatedGradedEquiv (data (F := F) hn) x)
  exact hx

end PaperVerification.Fermion.TypeA
