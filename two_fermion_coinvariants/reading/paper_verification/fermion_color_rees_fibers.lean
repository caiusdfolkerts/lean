module

public import PaperVerification.FermionColorRees
public import PaperVerification.FermionIndependentColorAction
public import PaperVerification.FermionWeightReesActionFibers

/-!
# Equivariance of both actual type-A fibers

At one the action is the original simultaneous color action on the strict
quotient. At zero it is the diagonal restriction of the independently
constructed GL(2)^n action on the actual initial quotient. The comparison
uses actual homogeneous representatives and their proved initial normal
forms; neither action is defined by transport through the fiber isomorphism.

-/

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped Classical BigOperators TensorProduct PaperVerification.Fermion.WeightRees

namespace PaperVerification.Fermion.TypeA

open MvPolynomial Exterior

variable {F : Type*} [Field F] [CharZero F] {n : ℕ}

local instance FermionColorReesFibers_localInst_1 : LinearOrder (OddIndex n) :=
  LinearOrder.lift' modeRank modeRank_injective

def diagonalInitialAction (hn : 0<n) (g : Matrix.GeneralLinearGroup (Fin 2) F) :
    StrictMultiplicityInitialQuotient (data (F := F) hn) ≃ₐ[F]
      StrictMultiplicityInitialQuotient (data (F := F) hn) :=
  ColorAction.initialQuotientEquiv (fun _ ↦ g) (data hn)

theorem diagonalInitialAction_basis (hn : 0<n)
    (g : Matrix.GeneralLinearGroup (Fin 2) F) (i : StrictPowerIndex (data (F := F) hn).r) :
    diagonalInitialAction hn g (strictMultiplicityInitialBasis (data hn) i)=
      ∑ j : StrictPowerIndex (data (F := F) hn).r,
        if strictBasisMultiplicityWeight (data hn) j=strictBasisMultiplicityWeight (data hn) i then
          (strictCoupledBasis (data hn)).repr
            (ColorAction.quotientEquiv g (fun k ↦ X k) (strictCoupledBasis (data hn) i)) j •
              strictMultiplicityInitialBasis (data hn) j else 0 := by
  let d := data (F := F) hn
  let h := strictMultiplicityPresentation d
  have hx : BasisFiltered.Homogeneous (superPolynomialBasis (K := F)) multiplicityWordWeight
      (strictBasisMultiplicityWeight d i) (ColorAction.ambient g.val (h.representative i)) :=
    ColorAction.ambient_smul_basis_homogeneous g.val _ _
  have H := strictInitial_normalForm d _ _ hx
  have hq : (strictIdeal d.beta d.phi).ringCon.mkₐ F
      (ColorAction.ambient g.val (h.representative i))=
      ColorAction.quotientEquiv g (fun k ↦ X k) (strictCoupledBasis d i) := by
    have hb : strictCoupledBasis d i=
        (strictIdeal d.beta d.phi).ringCon.mkₐ F (h.representative i) := h.basis_apply i
    rw [hb]
    exact (ColorAction.quotientEquiv_mk g (fun k ↦ X k) (h.representative i)).symm
  rw [hq] at H
  rw [strictMultiplicityInitialBasis_apply]
  change ColorAction.initialQuotientEquiv (fun _ ↦ g) d
    ((strictMultiplicityInitialIdeal d).ringCon.mkₐ F (h.representative i))=_
  rw [ColorAction.initialQuotientEquiv_mk,ColorAction.indexAmbient_constant]
  exact H

theorem color_preserves_basisTail (hn : 0<n)
    (g : Matrix.GeneralLinearGroup (Fin 2) F) (r : ℕ)
    (x : StrictQuotient (fun _ : Fin n ↦ (1 : F)) (fun i ↦ X i)) :
    ColorAction.quotientEquiv g (fun i ↦ X i) x ∈
        BlockInitial.lowerSubmodule (strictCoupledBasis (data hn))
          (strictBasisMultiplicityWeight (data hn)) r ↔
      x ∈ BlockInitial.lowerSubmodule (strictCoupledBasis (data hn))
        (strictBasisMultiplicityWeight (data hn)) r := by
  rw [←colorFiltration_eq_basisTail hn r]
  exact ColorAction.quotientEquiv_filtration_iff g _ r x

section Zero

local instance zeroEvaluation : Algebra (Polynomial F) F :=
  (Polynomial.evalRingHom (0 : F)).toAlgebra

set_option maxHeartbeats 1000000 in
/-- The zero-fiber algebra isomorphism intertwines the actual family action
and the diagonal subgroup of the independently constructed GL(2)^n action. -/
theorem fiberZero_color_equivariant (hn : 0<n)
    (g : Matrix.GeneralLinearGroup (Fin 2) F)
    (z : F ⊗[Polynomial F] StrictMultiplicityRees (data (F := F) hn)) :
    strictMultiplicityFiberZero (data hn)
      (Algebra.TensorProduct.congr (AlgEquiv.refl : F ≃ₐ[F] F) (reesColorAction hn g) z)=
        diagonalInitialAction hn g (strictMultiplicityFiberZero (data hn) z) := by
  let b := strictCoupledBasis (data (F := F) hn)
  let w := strictBasisMultiplicityWeight (data (F := F) hn)
  have hweight := strictBasisMultiplicityWeight_multiplicative (data (F := F) hn)
  let e : StrictQuotient (data (F := F) hn).beta (data (F := F) hn).phi ≃ₐ[F]
      StrictQuotient (data (F := F) hn).beta (data (F := F) hn).phi :=
    ColorAction.quotientEquiv g (fun i : Fin n ↦ (X i : PolynomialRing F n))
  have he := color_preserves_basisTail hn g
  let b₀ := strictMultiplicityInitialBasis (data (F := F) hn)
  let e₀ := diagonalInitialAction hn g
  let makeProof := @WeightRees.fiberLinearEquiv_equivariant
    F (StrictQuotient (data (F := F) hn).beta (data (F := F) hn).phi)
    (StrictPowerIndex (data (F := F) hn).r)
    inferInstance inferInstance inferInstance inferInstance b w hweight e he
    (StrictMultiplicityInitialQuotient (data (F := F) hn))
    inferInstance inferInstance (0 : F) b₀ e₀
  have h := makeProof (by
    intro i
    dsimp only [b,w,b₀,e,e₀]
    rw [diagonalInitialAction_basis]
    apply Finset.sum_congr rfl
    intro j hj
    rw [WeightRees.actionPolynomial_eval_zero (K := F)
      (A := StrictQuotient (fun _ : Fin n ↦ (1 : F)) (fun i ↦ X i))
      _ _ _ (color_preserves_basisTail hn g)]
    split_ifs
    · rfl
    · exact (zero_smul F (strictMultiplicityInitialBasis (data (F := F) hn) j)).symm)
  exact h z

end Zero

section One

local instance oneEvaluation : Algebra (Polynomial F) F :=
  (Polynomial.evalRingHom (1 : F)).toAlgebra

set_option maxHeartbeats 1000000 in
/-- The unit-fiber isomorphism intertwines the actual family action and the
original color action on the literal strict moment quotient. -/
theorem fiberOne_color_equivariant (hn : 0<n)
    (g : Matrix.GeneralLinearGroup (Fin 2) F)
    (z : F ⊗[Polynomial F] StrictMultiplicityRees (data (F := F) hn)) :
    strictMultiplicityFiberOne (data hn)
      (Algebra.TensorProduct.congr (AlgEquiv.refl : F ≃ₐ[F] F) (reesColorAction hn g) z)=
        ColorAction.quotientEquiv g (fun i ↦ X i) (strictMultiplicityFiberOne (data hn) z) := by
  let b := strictCoupledBasis (data (F := F) hn)
  let w := strictBasisMultiplicityWeight (data (F := F) hn)
  have hweight := strictBasisMultiplicityWeight_multiplicative (data (F := F) hn)
  let e := ColorAction.quotientEquiv g (fun i : Fin n ↦ (X i : PolynomialRing F n))
  have he := color_preserves_basisTail hn g
  have h := @WeightRees.fiberOne_equivariant
    F (StrictQuotient (data (F := F) hn).beta (data (F := F) hn).phi)
    (StrictPowerIndex (data (F := F) hn).r)
    inferInstance inferInstance inferInstance inferInstance b w hweight e he
  exact h z

end One
end PaperVerification.Fermion.TypeA
