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
theorem palomarColorProducts (hn : 0<n) :
    let pure := fun (m : MultiplicityVector n) (p : PolynomialRing F n)
          (x : ColorPaths.ExteriorColorTensor F m) ↦
        (strictMultiplicityAssociatedGradedEquiv (data (F := F) hn)).symm
          (strictInitialProjection (data (F := F) hn)
            (p ⊗ₜ[F] NaturalColor.assemble (fun i ↦ (m i).val) x))
    (Submodule.span F (Set.range (fun z :
    Σ m : MultiplicityVector n,PolynomialRing F n × ColorPaths.ExteriorColorTensor F m ↦
      pure z.1 z.2.1 z.2.2))=⊤) ∧
    (∀ (m l : MultiplicityVector n) (p q : PolynomialRing F n)
      (x : ColorPaths.ExteriorColorTensor F m) (y : ColorPaths.ExteriorColorTensor F l),
    pure m p x*pure l q y=
      (strictMultiplicityAssociatedGradedEquiv (data (F := F) hn)).symm
        (strictInitialProjection (data (F := F) hn)
          ((p*q) ⊗ₜ[F] (NaturalColor.assemble (fun i ↦ (m i).val) x*
            NaturalColor.assemble (fun i ↦ (l i).val) y)))) := by
  dsimp only
  have h (m : MultiplicityVector n) (p : PolynomialRing F n) (x : ColorPaths.ExteriorColorTensor F m) :
      (strictMultiplicityAssociatedGradedEquiv (data (F := F) hn)).symm
        (strictInitialProjection (data (F := F) hn)
          (p ⊗ₜ[F] NaturalColor.assemble (fun i ↦ (m i).val) x)) = gradedPureTensor hn m p x := by
    rw [← gradedPureTensor_original hn m p x, AlgEquiv.symm_apply_apply]
  simpa only [h] using And.intro (PaperVerification.Fermion.theorem_8_1 (F := F) hn).products_span
    (PaperVerification.Fermion.theorem_8_1 (F := F) hn).original_products
end PaperVerification.Fermion.TypeA
