module

public import PaperVerification.AlternatingFormsCubicInjectivity
public import PaperVerification.AlternatingFormsQuadraticDualTensorHilbert
import Lean.Elab.Tactic.Omega

/-!
# The complete generic quadratic-dual clause of Proposition 5.3

This endpoint retains every dimension `n ≥ 6` and a nonempty principal
open subset of the full original coefficient space.  The source is the
ordinary annihilator-defined quadratic dual.  Its isomorphism with the
actual ordinary two-step enveloping algebra, both Lie-degree dimensions,
triple-bracket vanishing, and its full original-generator Hilbert series
are conclusions of the theorem.

The separate assertion that the exterior quotient is Koszul exactly for
`n ≤ 4` is not asserted by this endpoint.  This source remains a proof
candidate until compiled with its complete dependency closure.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section
open scoped Classical PowerSeries

namespace PaperVerification.AlternatingForms

variable (K : Type) [Field K] [CharZero K]

theorem paper_proposition_5_3_dual_clause (n : ℕ) (hn : 6≤n) :
    ∃ (ι : Type) (fin : Fintype ι),
      letI := fin
      ∃ b₂ : Module.Basis ι K (⋀[K]^2 (Fin n → K)),
        ∃ Q : MvPolynomial (ι ⊕ ι) K, Q≠0 ∧
          (∃ y : (ι ⊕ ι) → K, MvPolynomial.eval y Q≠0) ∧
          ∀ y : (ι ⊕ ι) → K, MvPolynomial.eval y Q≠0 →
            let f := (orbitFormsFromCoordinates b₂ y).1
            let g := (orbitFormsFromCoordinates b₂ y).2
            let D := TwoStepDual.bracketData f g
            Nonempty (QuadraticDual.TensorQuadraticDual f g ≃ₐ[K]
              UniversalEnvelopingAlgebra K (TwoStepCentralLie.LieSpace D)) ∧
            Module.finrank K (TwoStepCentralLie.degreeOne D)=n ∧
            Module.finrank K (TwoStepCentralLie.degreeTwo D)=2 ∧
            Disjoint (TwoStepCentralLie.degreeOne D) (TwoStepCentralLie.degreeTwo D) ∧
            TwoStepCentralLie.degreeOne D ⊔ TwoStepCentralLie.degreeTwo D=⊤ ∧
            TwoStepCentralLie.degreeTwo D=Submodule.span K
              (Set.range (fun p : Fin n × Fin n =>
                ⁅TwoStepCentralLie.generator D (Pi.basisFun K (Fin n) p.1),
                  TwoStepCentralLie.generator D (Pi.basisFun K (Fin n) p.2)⁆)) ∧
            (∀ x y z : TwoStepCentralLie.LieSpace D, ⁅⁅x,y⁆,z⁆=0) ∧
            QuadraticDual.tensorHilbertSeries f g*
              ((1-PowerSeries.X)^n*(1-PowerSeries.X^2)^2)=1 := by
  letI : NeZero n := ⟨by omega⟩
  have hdim : Module.finrank K (Fin n → K)=n := by simp
  obtain ⟨ι,fin,h⟩ := generic_cubic_wedge_injective (K := K) (M := Fin n → K) n hn hdim
  letI := fin
  obtain ⟨b₂,Q,hQ,hnonempty,h⟩ := h
  refine ⟨ι,fin,b₂,Q,hQ,hnonempty,?_⟩
  intro y hy
  let f := (orbitFormsFromCoordinates b₂ y).1
  let g := (orbitFormsFromCoordinates b₂ y).2
  let D := TwoStepDual.bracketData f g
  refine ⟨⟨QuadraticDual.tensorQuadraticDualEnvelopingEquiv f g (h y hy)⟩,
    ?_,?_,?_,?_,?_,?_,?_⟩
  · exact (TwoStepCentralLie.finrank_degreeOne D).trans hdim
  · simpa using TwoStepCentralLie.finrank_degreeTwo D
  · exact TwoStepCentralLie.degree_subspaces_disjoint D
  · exact TwoStepCentralLie.degree_subspaces_span D
  · exact QuadraticCommutatorQuotient.degreeTwo_eq_span_generator_brackets D
      (TwoStepDual.bracketMap_surjective f g (h y hy))
  · exact TwoStepCentralLie.bracket_bracket_eq_zero D
  · simpa only [Fintype.card_fin] using
      QuadraticDual.tensorHilbertSeries_mul_denominator_eq_one f g (h y hy)

end PaperVerification.AlternatingForms
