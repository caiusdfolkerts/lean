module

public import PaperVerification.FermionColorFiltration
public import PaperVerification.FermionTypeAMultiplicity
public import PaperVerification.FermionStrictWeightReesFibers
public import PaperVerification.FermionWeightReesEquivariant

/-!
# The actual GL(2)-equivariant flat family for strict type A

The action is defined on the same Laurent subalgebra whose finite freeness
and two fibers were constructed independently. Its preservation follows
from the literal exterior-word filtration. No equivariance hypothesis is
added to the type-A data.

-/

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped PaperVerification.Fermion.WeightRees

namespace PaperVerification.Fermion.TypeA

open MvPolynomial

variable {F : Type*} [Field F] [CharZero F] {n : ℕ}

theorem colorFiltration_eq_basisTail (hn : 0<n) (r : ℕ) :
    ColorAction.quotientFiltration (fun i : Fin n ↦ (X i : PolynomialRing F n)) r =
      BlockInitial.lowerSubmodule (strictCoupledBasis (data (F := F) hn))
        (strictBasisMultiplicityWeight (data hn)) r :=
  strictMultiplicityFiltration_eq_basisTail (data hn) r

set_option maxHeartbeats 1000000 in
def reesColorAction (hn : 0<n) :
    Matrix.GeneralLinearGroup (Fin 2) F →*
      (StrictMultiplicityRees (data (F := F) hn) ≃ₐ[Polynomial F]
        StrictMultiplicityRees (data (F := F) hn)) := by
  let f := WeightRees.filtrationAction (K := F) (A := StrictQuotient (fun _ : Fin n ↦ (1 : F)) (fun i ↦ X i))
      (strictCoupledBasis (data hn))
      (strictBasisMultiplicityWeight (data hn))
      (strictBasisMultiplicityWeight_multiplicative (data hn))
      (ColorAction.quotientAction (fun i : Fin n ↦ (X i : PolynomialRing F n)))
      (fun g r x ↦ by
        rw [←colorFiltration_eq_basisTail hn r]
        exact ColorAction.quotientEquiv_filtration_iff g _ r x)
  exact f

/-- The family action is exactly the original color action on every actual
Laurent coefficient, with every integer exponent retained. -/
theorem reesColorAction_coeff (hn : 0<n)
    (g : Matrix.GeneralLinearGroup (Fin 2) F)
    (z : StrictMultiplicityRees (data (F := F) hn)) (r : ℤ) :
    (reesColorAction hn g z).val.coeff r =
      ColorAction.quotientEquiv g (fun i : Fin n ↦ (X i : PolynomialRing F n))
        (z.val.coeff r) := by
  have h := WeightRees.parameterLaurentEquiv_coeff (K := F)
    (A := StrictQuotient (fun _ : Fin n ↦ (1 : F)) (fun i ↦ X i))
    (ColorAction.quotientEquiv g (fun i : Fin n ↦ (X i : PolynomialRing F n))) z.val r
  exact h

/-- Flatness and the color action concern the very same algebra over F[t]. -/
theorem colorRees_finite_free_flat (hn : 0<n) :
    Module.Finite (Polynomial F) (StrictMultiplicityRees (data (F := F) hn)) ∧
    Module.Free (Polynomial F) (StrictMultiplicityRees (data (F := F) hn)) ∧
    Module.Flat (Polynomial F) (StrictMultiplicityRees (data (F := F) hn)) := by
  have h := strictMultiplicityRees_finite_free (data (F := F) hn)
  exact ⟨h.1,h.2,strictMultiplicityRees_flat (data hn)⟩

end PaperVerification.Fermion.TypeA
