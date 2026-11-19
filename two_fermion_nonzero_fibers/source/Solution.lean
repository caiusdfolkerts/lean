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
theorem palomarColorNonzero_fibers (hn : 0<n) :
    (letI : Algebra (Polynomial F) F := (Polynomial.evalRingHom (1 : F)).toAlgebra
    Nonempty (F ⊗[Polynomial F] StrictMultiplicityRees (data (F := F) hn) ≃ₐ[F]
      StrictQuotient (fun _ : Fin n ↦ (1 : F)) (fun i ↦ X i)) ∧
    ∀ (g : Matrix.GeneralLinearGroup (Fin 2) F)
      (z : F ⊗[Polynomial F] StrictMultiplicityRees (data (F := F) hn)),
      strictMultiplicityFiberOne (data (F := F) hn)
        (Algebra.TensorProduct.congr (AlgEquiv.refl : F ≃ₐ[F] F) (reesColorAction hn g) z)=
        ColorAction.quotientEquiv g (fun i ↦ X i) (strictMultiplicityFiberOne (data (F := F) hn) z)) ∧
    (∀ (c : F) (hc : c≠0),
    letI : Algebra (Polynomial F) F := (Polynomial.evalRingHom c).toAlgebra
    Nonempty (F ⊗[Polynomial F] StrictMultiplicityRees (data (F := F) hn) ≃ₐ[F]
      StrictQuotient (fun _ : Fin n ↦ (1 : F)) (fun i ↦ X i)) ∧
    ∀ (g : Matrix.GeneralLinearGroup (Fin 2) F)
      (z : F ⊗[Polynomial F] StrictMultiplicityRees (data (F := F) hn)),
      nonzeroFiberEquiv hn c hc
        (Algebra.TensorProduct.congr (AlgEquiv.refl : F ≃ₐ[F] F) (reesColorAction hn g) z)=
        ColorAction.quotientEquiv g (fun i ↦ X i) (nonzeroFiberEquiv hn c hc z)) := by
  exact ⟨(PaperVerification.Fermion.theorem_8_1 (F := F) hn).unit_fiber, (PaperVerification.Fermion.theorem_8_1 (F := F) hn).nonzero_fibers⟩
end PaperVerification.Fermion.TypeA
