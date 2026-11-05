module

public import PaperVerification.FermionDefinitions
public import Mathlib.LinearAlgebra.TensorProduct.Basis
public import Mathlib.LinearAlgebra.ExteriorAlgebra.Basis
public import Mathlib.RingTheory.MvPolynomial.Basic

/-!
# The literal polynomial and exterior monomial basis

These declarations are moved verbatim from FermionSuperHighestForms. They
belong to the original ambient algebra and require no filtered quotient or
moment-basis theorem.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace PaperVerification.Fermion

open MvPolynomial
open scoped BigOperators TensorProduct

variable {K : Type*} [CommRing K] {n : ℕ} [LinearOrder (OddIndex n)]

abbrev SuperMonomialIndex (n : ℕ) := (Fin n →₀ ℕ) × Finset (OddIndex n)

def superMonomialBasis : Module.Basis (SuperMonomialIndex n) K (SuperRing K n) :=
  (basisMonomials (Fin n) K).tensorProduct (Pi.basisFun K (OddIndex n)).ExteriorAlgebra

@[simp] theorem superMonomialBasis_apply (z : SuperMonomialIndex n) :
    superMonomialBasis (K := K) z =
      monomial z.1 1 ⊗ₜ[K] (Pi.basisFun K (OddIndex n)).ExteriorAlgebra z.2 := by
  simp only [superMonomialBasis,Module.Basis.tensorProduct_apply',coe_basisMonomials]

end PaperVerification.Fermion
