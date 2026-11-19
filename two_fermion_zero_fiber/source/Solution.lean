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
set_option maxRecDepth 8192 in
theorem palomarColorZeroFiber (hn : 0<n) :
    letI : Algebra (Polynomial F) F := (Polynomial.evalRingHom (0 : F)).toAlgebra
    let d := data (F := F) hn
    ∃ E : (F ⊗[Polynomial F] StrictMultiplicityRees d) ≃ₐ[F] StrictMultiplicityAssociatedGraded d,
      (∀ i : StrictPowerIndex d.r, ∃ hi : strictCoupledBasis d i ∈
          (strictMultiplicityDescendingFiltration d).piece (strictBasisMultiplicityWeight d i),
        E (1 ⊗ₜ[Polynomial F] strictMultiplicityReesBasis d i) =
        DirectSum.of (DescendingAlgebra.GradedPiece (strictMultiplicityDescendingFiltration d))
          (strictBasisMultiplicityWeight d i)
          (Submodule.Quotient.mk (⟨strictCoupledBasis d i, hi⟩ : (strictMultiplicityDescendingFiltration d).piece (strictBasisMultiplicityWeight d i)))) ∧
      ∃ A : Matrix.GeneralLinearGroup (Fin 2) F →*
          (StrictMultiplicityAssociatedGraded d ≃ₐ[F] StrictMultiplicityAssociatedGraded d),
        (∀ (g : Matrix.GeneralLinearGroup (Fin 2) F) (r : ℕ)
          (x : (strictMultiplicityDescendingFiltration d).piece r),
          ∃ h : ColorAction.quotientEquiv g (fun i ↦ X i) x.val ∈ (strictMultiplicityDescendingFiltration d).piece r,
            A g (DirectSum.of (DescendingAlgebra.GradedPiece (strictMultiplicityDescendingFiltration d))
              r (Submodule.Quotient.mk x)) = DirectSum.of (DescendingAlgebra.GradedPiece (strictMultiplicityDescendingFiltration d))
                r (Submodule.Quotient.mk ⟨ColorAction.quotientEquiv g (fun i ↦ X i) x.val,h⟩)) ∧
      ∀ (g : Matrix.GeneralLinearGroup (Fin 2) F) z,
        E (Algebra.TensorProduct.congr (AlgEquiv.refl : F ≃ₐ[F] F) (reesColorAction hn g) z) =
          A g (E z) := by
  letI : Algebra (Polynomial F) F := (Polynomial.evalRingHom (0 : F)).toAlgebra
  let d := data (F := F) hn
  refine ⟨zeroFiberAssociatedEquiv hn, ?_, gradedColorAction hn, ?_, zeroFiberAssociatedEquiv_intertwines hn⟩
  · intro i
    refine ⟨DescendingBasis.basis_mem_tail (strictCoupledBasis d) (strictBasisMultiplicityWeight d)
      (strictBasisMultiplicityWeight_multiplicative d) i, ?_⟩
    rw [← DescendingBasis.gradedBasis_apply]
    apply (strictMultiplicityAssociatedGradedEquiv d).injective
    rw [strictMultiplicityAssociatedGradedEquiv_basis]
    change strictMultiplicityAssociatedGradedEquiv d ((strictMultiplicityAssociatedGradedEquiv d).symm
      (strictMultiplicityFiberZero d (1 ⊗ₜ[Polynomial F] strictMultiplicityReesBasis d i))) = _
    rw [AlgEquiv.apply_symm_apply]
    unfold strictMultiplicityFiberZero strictMultiplicityReesBasis
    apply WeightRees.fiberAlgEquiv_basis
  · intro g r x
    have he := color_preserves_basisTail (F := F) hn g
    exact ⟨(he r x.val).mpr x.property, DescendingAlgebra.associatedEquiv_of_mk
      (strictMultiplicityDescendingFiltration d) (ColorAction.quotientEquiv g (fun i ↦ X i)) he r x⟩
end PaperVerification.Fermion.TypeA
