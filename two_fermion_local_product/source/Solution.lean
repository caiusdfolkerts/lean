module
public import two_fermion
@[expose] public section
noncomputable section
namespace PaperVerification.Fermion
theorem localProductOverSupport {F : Type} [Field F] [CharZero F] [IsAlgClosed F] {n : ℕ}
    (d : SeparatedPairedData F n) :
    Finite d.O.SupportPoint ∧ (∀ rho : d.O.SupportPoint, Nontrivial (d.LocalSuper rho)) ∧
      Nonempty (d.SuperQuotient ≃ₐ[F] ∀ rho : d.O.SupportPoint, d.LocalSuper rho) := by
  exact ⟨(theorem_7_2 d).1, (theorem_7_2 d).2.2.2.1, ⟨d.superProductOverSupport⟩⟩
end PaperVerification.Fermion
