module

public import PaperVerification.AlternatingFormsOddExteriorBasis
public import PaperVerification.AlternatingFormsOddTransport

/-!
# The good exterior basis in arbitrary coordinates

This endpoint removes the choice of the standard coordinate vector space.
It covers every module with a basis of the requested size, every odd
dimension, and every exterior degree, and displays the original basis words.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace PaperVerification.AlternatingForms

variable {K M : Type*} [Field K] [CharZero K]
  [AddCommGroup M] [Module K M] {k : ℕ}

def oddExteriorBasisAt (b : Module.Basis (Fin (2*k+1)) K M) (s : ℕ) :
    Module.Basis (GoodOddIndex k s) K
      (ExteriorQuotientDegree (oddPathFirstQuadratic (K := K) b) (oddPathSecondQuadratic (K := K) b) s) :=
  (oddExteriorBasis k s).map (oddExteriorBasisChangeEquiv b s)

@[simp] theorem oddExteriorBasisAt_apply
    (b : Module.Basis (Fin (2*k+1)) K M) (s : ℕ) (I : GoodOddIndex k s) :
    oddExteriorBasisAt b s I = Submodule.Quotient.mk
      (exteriorPower.ιMulti K s (fun i => b (I.val.val i))) := by
  rw [oddExteriorBasisAt, Module.Basis.map_apply, oddExteriorBasis_apply,
    oddExteriorBasisChangeEquiv_mk, exteriorPluckerBasis_apply,
    exteriorPower.map_apply_ιMulti]
  congr 1
  apply congrArg (exteriorPower.ιMulti K s)
  funext i
  exact standardBasisEquiv_basisFun b (I.val.val i)

/-- The exterior-basis clause of Theorem 1.3 with its full basis-dependent
vector-space interpretation, including all boundary and vanishing degrees. -/
theorem paper_theorem_1_3_exterior_basis_with_basis
    (b : Module.Basis (Fin (2*k+1)) K M) (s : ℕ) :
    ∃ B : Module.Basis (GoodOddIndex k s) K
      (ExteriorQuotientDegree (oddPathFirstQuadratic (K := K) b) (oddPathSecondQuadratic (K := K) b) s),
      ∀ I, B I = Submodule.Quotient.mk
        (exteriorPower.ιMulti K s (fun i => b (I.val.val i))) :=
  ⟨oddExteriorBasisAt b s, oddExteriorBasisAt_apply b s⟩

end PaperVerification.AlternatingForms
