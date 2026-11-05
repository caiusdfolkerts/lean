module

public import PaperVerification.FermionColorReesFibers
public import PaperVerification.FermionWeightReesUnitFibers

/-!
# All nonzero fibers of the equivariant type A degeneration

The parameter ranges over every nonzero field element. The equivalence and its
equivariance use the original moment quotient and its actual color action.
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped TensorProduct

namespace PaperVerification.Fermion.TypeA

open MvPolynomial
variable {F : Type*} [Field F] [CharZero F] {n : ℕ}

set_option maxHeartbeats 1000000 in
def nonzeroFiberEquiv (hn : 0<n) (c : F) (hc : c≠0) :
    letI : Algebra (Polynomial F) F := (Polynomial.evalRingHom c).toAlgebra
    F ⊗[Polynomial F] StrictMultiplicityRees (data (F := F) hn) ≃ₐ[F]
      StrictQuotient (fun _ : Fin n ↦ (1 : F)) (fun i ↦ X i) := by
  let e := WeightRees.fiberUnit (K := F) (A := StrictQuotient (fun _ : Fin n ↦ (1 : F)) (fun i ↦ X i))
      (strictCoupledBasis (data hn))
      (strictBasisMultiplicityWeight (data hn))
      (strictBasisMultiplicityWeight_multiplicative (data hn)) (Units.mk0 c hc)
  exact e

set_option maxHeartbeats 1000000 in
theorem nonzeroFiberEquiv_intertwines (hn : 0<n) (c : F) (hc : c≠0) :
    letI : Algebra (Polynomial F) F := (Polynomial.evalRingHom c).toAlgebra
    ∀ (g : Matrix.GeneralLinearGroup (Fin 2) F)
      (z : F ⊗[Polynomial F] StrictMultiplicityRees (data (F := F) hn)),
      nonzeroFiberEquiv hn c hc
        (Algebra.TensorProduct.congr (AlgEquiv.refl : F ≃ₐ[F] F) (reesColorAction hn g) z)=
        ColorAction.quotientEquiv g (fun i ↦ X i) (nonzeroFiberEquiv hn c hc z) := by
  letI : Algebra (Polynomial F) F := (Polynomial.evalRingHom c).toAlgebra
  intro g z
  let d := data (F := F) hn
  let b := strictCoupledBasis d
  let w := strictBasisMultiplicityWeight d
  have hweight := strictBasisMultiplicityWeight_multiplicative d
  let e := ColorAction.quotientEquiv g (fun i : Fin n ↦ (X i : PolynomialRing F n))
  have he := color_preserves_basisTail hn g
  have equivariance := @WeightRees.fiberUnit_equivariant F
    (StrictQuotient d.beta d.phi) (StrictPowerIndex d.r)
    inferInstance inferInstance inferInstance inferInstance
    b w hweight e he (Units.mk0 c hc)
  exact equivariance z

end PaperVerification.Fermion.TypeA
