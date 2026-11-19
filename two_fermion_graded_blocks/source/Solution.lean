module
public import two_fermion
@[expose] public section
noncomputable section
namespace PaperVerification.Fermion.TypeA
set_option backward.isDefEq.respectTransparency false
open scoped Classical BigOperators TensorProduct DirectSum
  PaperVerification.Fermion.WeightRees
open MvPolynomial Exterior
variable {F : Type*} [Field F] [CharZero F] {n : ℕ}
attribute [local instance] theoremEightOneOrder
-- PALOMAR_CONTEXT_ORIGIN 55724
set_option maxHeartbeats 2000000 in
set_option maxRecDepth 8192 in
theorem palomarColorGradedBlocks (hn : 0<n) :
    let d := data (F := F) hn
    ∃ E : StrictMultiplicityAssociatedGraded d ≃ₐ[F] StrictMultiplicityInitialQuotient d,
      (∀ i : StrictPowerIndex d.r,
        ∃ hi : strictCoupledBasis d i ∈ (strictMultiplicityDescendingFiltration d).piece (strictBasisMultiplicityWeight d i),
          E (DirectSum.of (DescendingAlgebra.GradedPiece (strictMultiplicityDescendingFiltration d))
            (strictBasisMultiplicityWeight d i) (Submodule.Quotient.mk
              (⟨strictCoupledBasis d i,hi⟩ : (strictMultiplicityDescendingFiltration d).piece (strictBasisMultiplicityWeight d i)))) =
            strictInitialProjection d (monomial i.2.val.val (1 : F) • superPolynomialBasis (K := F) i.1)) ∧
      ∃ B : StrictMultiplicityAssociatedGraded d ≃ₗ[F]
          ⨁ m : {m : MultiplicityVector n // Admissible m}, ExteriorCoefficientBlock (F := F) m.val,
        (∀ (m : MultiplicityVector n) (p : PolynomialRing F n) (x : ColorPaths.ExteriorColorTensor F m)
          (j : {m : MultiplicityVector n // Admissible m}),
          B (E.symm (strictInitialProjection d (p ⊗ₜ[F] NaturalColor.assemble (fun i ↦ (m i).val) x))) j =
            (Pi.single (M := fun l ↦ ExteriorCoefficientBlock (F := F) l) m
              (Ideal.Quotient.mk (coefficientIdeal m) p ⊗ₜ[F] x)) j.val) ∧
        ∃ A : Matrix.GeneralLinearGroup (Fin 2) F →*
            (StrictMultiplicityAssociatedGraded d ≃ₐ[F] StrictMultiplicityAssociatedGraded d),
          (∀ (g : Matrix.GeneralLinearGroup (Fin 2) F) (r : ℕ) (x : (strictMultiplicityDescendingFiltration d).piece r),
            ∃ h : ColorAction.quotientEquiv g (fun i ↦ X i) x.val ∈ (strictMultiplicityDescendingFiltration d).piece r,
              A g (DirectSum.of (DescendingAlgebra.GradedPiece (strictMultiplicityDescendingFiltration d))
                r (Submodule.Quotient.mk x)) = DirectSum.of (DescendingAlgebra.GradedPiece (strictMultiplicityDescendingFiltration d))
                  r (Submodule.Quotient.mk (⟨ColorAction.quotientEquiv g (fun i ↦ X i) x.val,h⟩ :
                    (strictMultiplicityDescendingFiltration d).piece r))) ∧
          ∀ (g : Matrix.GeneralLinearGroup (Fin 2) F) x,
            B (A g x) = naturalAdmissibleRepresentation (fun _ ↦ g) (B x) := by
  let d := data (F := F) hn
  refine ⟨strictMultiplicityAssociatedGradedEquiv d, ?_, naturalAssociatedGradedEquiv hn, ?_, gradedColorAction hn, ?_, naturalAssociatedGradedEquiv_intertwines hn⟩
  · intro i
    refine ⟨DescendingBasis.basis_mem_tail (strictCoupledBasis d) (strictBasisMultiplicityWeight d)
      (strictBasisMultiplicityWeight_multiplicative d) i, ?_⟩
    rw [← DescendingBasis.gradedBasis_apply, strictMultiplicityAssociatedGradedEquiv_basis,
      strictMultiplicityInitialBasis_apply]
    rfl
  · intro m p x j
    change (naturalInitialFunctionEquiv hn (strictMultiplicityAssociatedGradedEquiv d
      ((strictMultiplicityAssociatedGradedEquiv d).symm _))) j.val = _
    rw [AlgEquiv.apply_symm_apply, ← naturalInitialFunctionEquiv_symm_tmul hn m p x,
      LinearEquiv.apply_symm_apply]
  · intro g r x
    have he := color_preserves_basisTail (F := F) hn g
    exact ⟨(he r x.val).mpr x.property, DescendingAlgebra.associatedEquiv_of_mk
      (strictMultiplicityDescendingFiltration d) (ColorAction.quotientEquiv g (fun i ↦ X i)) he r x⟩
end PaperVerification.Fermion.TypeA
