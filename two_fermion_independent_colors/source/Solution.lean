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
theorem palomarColorIndependent (hn : 0<n) :
    (∀ (g : Fin n → Matrix.GeneralLinearGroup (Fin 2) F) (z : SuperRing F n),
      ColorAction.initialQuotientAction (data (F := F) hn) g (strictInitialProjection (data (F := F) hn) z)=
        strictInitialProjection (data (F := F) hn) (ColorAction.indexAmbient (fun i ↦ (g i).val) z)) ∧
    (∀ (g : Fin n → Matrix.GeneralLinearGroup (Fin 2) F)
      (x : StrictMultiplicityInitialQuotient (data (F := F) hn)),
      naturalInitialAdmissibleEquiv hn (ColorAction.initialQuotientAction (data (F := F) hn) g x)=
        naturalAdmissibleRepresentation g (naturalInitialAdmissibleEquiv hn x)) := by
  exact ⟨(PaperVerification.Fermion.theorem_8_1 (F := F) hn).independent_color_representatives, (PaperVerification.Fermion.theorem_8_1 (F := F) hn).independent_color_equivariance⟩
end PaperVerification.Fermion.TypeA
