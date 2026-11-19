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
theorem palomarColorFamily (hn : 0<n) :
    (∀ r : ℕ,
    (strictMultiplicityDescendingFiltration (data (F := F) hn)).piece r=
      strictMultiplicityFiltration (data (F := F) hn) r) ∧
    (∀ z : LaurentPolynomial
      (StrictQuotient (fun _ : Fin n ↦ (1 : F)) (fun i ↦ X i)),
    z∈StrictMultiplicityRees (data (F := F) hn) ↔
      ∀ e,z.coeff e∈strictMultiplicityFiltration (data (F := F) hn) (-e).toNat) ∧
    (Module.Finite (Polynomial F) (StrictMultiplicityRees (data (F := F) hn)) ∧
    Module.Free (Polynomial F) (StrictMultiplicityRees (data (F := F) hn)) ∧
    Module.Flat (Polynomial F) (StrictMultiplicityRees (data (F := F) hn))) ∧
    (∀ (g : Matrix.GeneralLinearGroup (Fin 2) F)
      (z : StrictMultiplicityRees (data (F := F) hn)) (r : ℤ),
    (reesColorAction hn g z).val.coeff r=
      ColorAction.quotientEquiv g (fun i ↦ X i)
        (z.val.coeff r)) := by
  exact ⟨(PaperVerification.Fermion.theorem_8_1 (F := F) hn).actual_filtration, (PaperVerification.Fermion.theorem_8_1 (F := F) hn).actual_rees, (PaperVerification.Fermion.theorem_8_1 (F := F) hn).finite_free_flat, (PaperVerification.Fermion.theorem_8_1 (F := F) hn).family_color_coefficients⟩
end PaperVerification.Fermion.TypeA
