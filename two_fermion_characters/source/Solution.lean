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
theorem palomarColorCoefficients (hn : 0<n) :
    (∀ z : SuperRing F n,z∈initialIdeal hn ↔
    ∀ T,(superPolynomialBasis (K := F)).repr z T∈coefficientIdeal (wordMultiplicityVector T)) ∧
    (∀ m : MultiplicityVector n,¬Admissible m →
    coefficientIdeal (F := F) m=⊤) ∧
    (∀ (m : MultiplicityVector n),Admissible m → ∀ k : ℕ,
    (Module.finrank F (coefficientPolynomialPiece (F := F) m k) : F)=
      (ColorPaths.multiplicityBoxPolynomial (Polynomial.X : Polynomial F) m).coeff k) := by
  exact ⟨(PaperVerification.Fermion.theorem_8_1 (F := F) hn).initial_coefficients, (PaperVerification.Fermion.theorem_8_1 (F := F) hn).inadmissible_blocks, (PaperVerification.Fermion.theorem_8_1 (F := F) hn).coefficient_hilbert⟩
end PaperVerification.Fermion.TypeA
