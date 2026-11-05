module

public import PaperVerification.FermionPairedQuotientBaseChange
public import Mathlib.Algebra.Algebra.Equiv
public import Mathlib.RingTheory.TensorProduct.Basic

/-!
# Algebra scalar extension of the actual paired quotient

The previously constructed module comparison preserves the actual product
and unit.  This upgrades the fiber identification to an algebra isomorphism,
as required for the degeneration statement.

-/

@[expose] public section
set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace PaperVerification.Fermion

open Exterior
open scoped TensorProduct

variable (R S : Type*) [CommRing R] [CommRing S] [Algebra R S] {n : ℕ}

local instance FermionPairedAlgebraBaseChange_localInst_1 : LinearOrder (Fin n ⊕ Fin n) :=
  LinearOrder.lift' modeRank modeRank_injective

/-- The usual algebra-tensor-product ring structure, with the canonical
quotient scalar action made explicit for instance synthesis. -/
instance superQuotientTensorRing (I : TwoSidedIdeal (SuperRing R n)) :
    Ring (S ⊗[R] I.ringCon.Quotient) := by
  exact Algebra.TensorProduct.instRing (R := R) (A := S) (B := I.ringCon.Quotient)

/-- The usual left scalar algebra on the same tensor product. -/
instance superQuotientTensorAlgebra (I : TwoSidedIdeal (SuperRing R n)) :
    Algebra S (S ⊗[R] I.ringCon.Quotient) := by
  exact Algebra.TensorProduct.leftAlgebra (R := R) (S := S) (A := S) (B := I.ringCon.Quotient)

theorem pairedQuotientBaseChangeEquiv_map_one (d : PairedData (K := R) (n := n)) :
    pairedQuotientBaseChangeEquiv R S d 1 = 1 := by
  let q := (pairedIdeal d.beta d.phi d.a d.b).ringCon.mkₐ R
  let q' := (pairedIdeal (d.map (algebraMap R S)).beta (d.map (algebraMap R S)).phi
    (d.map (algebraMap R S)).a (d.map (algebraMap R S)).b).ringCon.mkₐ S
  have hq : q 1 = 1 := q.toRingHom.toMonoidHom.toOneHom.map_one'
  have hq' : q' 1 = 1 := q'.toRingHom.toMonoidHom.toOneHom.map_one'
  have hc : superCoefficientMap R S (1 : SuperRing R n) = 1 :=
    (superCoefficientMap R S).toRingHom.toMonoidHom.toOneHom.map_one'
  change pairedQuotientBaseChangeEquiv R S d ((1 : S) ⊗ₜ[R] (1 : PairedQuotient d.beta d.phi d.a d.b)) = 1
  rw [show (1 : PairedQuotient d.beta d.phi d.a d.b)=q 1 from hq.symm]
  rw [pairedQuotientBaseChangeEquiv_tmul_class,hc]
  change (1 : S) • q' 1 = 1
  rw [hq',one_smul]

theorem pairedQuotientBaseChangeEquiv_map_mul (d : PairedData (K := R) (n := n))
    (x y : S ⊗[R] PairedQuotient d.beta d.phi d.a d.b) :
    pairedQuotientBaseChangeEquiv R S d (x*y) =
      pairedQuotientBaseChangeEquiv R S d x * pairedQuotientBaseChangeEquiv R S d y := by
  let q := (pairedIdeal d.beta d.phi d.a d.b).ringCon.mkₐ R
  induction x using TensorProduct.induction_on with
  | zero => simp only [zero_mul,map_zero]
  | add x x' hx hx' => simp only [add_mul,map_add,hx,hx']
  | tmul s x =>
      obtain ⟨a,rfl⟩ := (pairedIdeal d.beta d.phi d.a d.b).ringCon.mkₐ_surjective (α := R) x
      induction y using TensorProduct.induction_on with
      | zero => simp only [mul_zero,map_zero]
      | add y y' hy hy' => simp only [mul_add,map_add,hy,hy']
      | tmul t y =>
          obtain ⟨b,rfl⟩ := (pairedIdeal d.beta d.phi d.a d.b).ringCon.mkₐ_surjective (α := R) y
          rw [Algebra.TensorProduct.tmul_mul_tmul,← map_mul q]
          dsimp only [q]
          simp only [pairedQuotientBaseChangeEquiv_tmul_class]
          simp only [map_mul,smul_mul_smul_comm]

def pairedQuotientBaseChangeAlgEquiv (d : PairedData (K := R) (n := n)) :
    S ⊗[R] PairedQuotient d.beta d.phi d.a d.b ≃ₐ[S]
      PairedQuotient (d.map (algebraMap R S)).beta (d.map (algebraMap R S)).phi
        (d.map (algebraMap R S)).a (d.map (algebraMap R S)).b :=
  AlgEquiv.ofLinearEquiv (pairedQuotientBaseChangeEquiv R S d)
    (pairedQuotientBaseChangeEquiv_map_one R S d)
    (pairedQuotientBaseChangeEquiv_map_mul R S d)

@[simp] theorem pairedQuotientBaseChangeAlgEquiv_class
    (d : PairedData (K := R) (n := n)) (z : PairedPowerIndex d.r d.u d.v d.s) :
    pairedQuotientBaseChangeAlgEquiv R S d ((1 : S) ⊗ₜ[R] pairedCoupledClasses d z) =
      pairedCoupledClasses (d.map (algebraMap R S)) z :=
  pairedQuotientBaseChangeEquiv_class R S d z

end PaperVerification.Fermion
