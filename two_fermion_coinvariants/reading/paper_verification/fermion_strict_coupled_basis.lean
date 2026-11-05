module

public import PaperVerification.FermionStrictCoupledIndependence
public import PaperVerification.FermionStrictIndexRecursion
public import PaperVerification.FermionStrictSplitting
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
# The complete coupled strict basis over its original field

The actual creator tests prove independence.  Independently, the actual
paired-extension split computes the whole quotient dimension, and the
strict-to-paired-tail index equivalence counts every proposed monomial.
Equality supplies spanning, with all coupled coefficients retained.

-/

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace PaperVerification.Fermion

open Exterior

variable {F : Type*} [Field F] {n : ℕ}

local instance FermionStrictCoupledBasis_localInst_1 : LinearOrder (Fin n ⊕ Fin n) :=
  LinearOrder.lift' modeRank modeRank_injective

def strictCoupledBasis (d : StrictData (K := F) (n := n)) :
    Module.Basis (StrictPowerIndex d.r) F (StrictQuotient d.beta d.phi) := by
  letI := strictCoupled_quotient_finite d
  exact basisOfLinearIndependentOfCardEqFinrank' (strictCoupledClasses d)
    (strictCoupledClasses_linearIndependent d)
    ((card_strictPowerIndex d.r d.positive_n).trans (strictCoupled_finrank d).symm)

@[simp] theorem strictCoupledBasis_apply (d : StrictData (K := F) (n := n))
    (z : StrictPowerIndex d.r) : strictCoupledBasis d z=strictCoupledClasses d z := by
  letI := strictCoupled_quotient_finite d
  exact congrFun (coe_basisOfLinearIndependentOfCardEqFinrank' _ _ _) z

end PaperVerification.Fermion
