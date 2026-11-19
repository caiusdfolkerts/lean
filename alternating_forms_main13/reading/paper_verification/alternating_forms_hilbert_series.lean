module

public import PaperVerification.AlternatingFormsGenericHilbertCoordinates
public import PaperVerification.FiniteHilbertSeries

/-!
# Theorem 1.1 as an equality of formal Hilbert series

The coefficients in `exteriorPairHilbertSeries` are the dimensions of the
actual homogeneous pieces of the quotient by the two exterior forms.  The
coefficient theorem and the displayed finite series are rigorously equivalent.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

namespace PaperVerification.AlternatingForms

open MvPolynomial
open scoped BigOperators Classical PowerSeries

variable {K M : Type*} [Field K] [AddCommGroup M] [Module K M]

def exteriorPairHilbertSeries (f g : ⋀[K]^2 M) : ℕ⟦X⟧ :=
  PowerSeries.mk fun s => Module.finrank K (ExteriorQuotientDegree f g s)

def paperExteriorHilbertSeries (n : ℕ) : ℕ⟦X⟧ :=
  FiniteHilbertSeries.expression (StripWalks.paperWalkCount n) ((n+1)/2)

theorem exteriorPairHilbertSeries_eq_iff (f g : ⋀[K]^2 M) (n : ℕ) :
    exteriorPairHilbertSeries f g = paperExteriorHilbertSeries n ↔
      Module.finrank K (ExteriorQuotientDegree f g 0) = 1 ∧
      (∀ s, 1 ≤ s → s ≤ (n+1)/2 →
        Module.finrank K (ExteriorQuotientDegree f g s) = StripWalks.paperWalkCount n s) ∧
      (∀ s, (n+1)/2 < s → Module.finrank K (ExteriorQuotientDegree f g s) = 0) :=
  FiniteHilbertSeries.mk_eq_expression_iff _ _ _

/-- The exact power-series formula of Theorem 1.1 on a nonempty principal
open in the complete coefficient space of pairs of exterior two-forms. -/
theorem paper_theorem_1_1_hilbertSeries [CharZero K] [FiniteDimensional K M]
    (n : ℕ) (hdim : Module.finrank K M = n) :
    ∃ (ι : Type) (fin : Fintype ι),
      letI := fin
      ∃ b₂ : Module.Basis ι K (⋀[K]^2 M),
        ∃ Q : MvPolynomial (ι ⊕ ι) K, Q ≠ 0 ∧
          (∃ y : (ι ⊕ ι) → K, eval y Q ≠ 0) ∧
          ∀ y : (ι ⊕ ι) → K, eval y Q ≠ 0 →
            exteriorPairHilbertSeries
              (orbitFormsFromCoordinates b₂ y).1 (orbitFormsFromCoordinates b₂ y).2 =
                paperExteriorHilbertSeries n := by
  obtain ⟨ι, fin, h⟩ := paper_theorem_1_1 (K := K) (M := M) n hdim
  letI := fin
  obtain ⟨b₂, Q, hQ, hnonempty, h⟩ := h
  refine ⟨ι, fin, b₂, Q, hQ, hnonempty, ?_⟩
  intro y hy
  obtain ⟨h0, hlo, hhi⟩ := h y hy
  exact (exteriorPairHilbertSeries_eq_iff _ _ n).mpr
    ⟨h0, fun s hs hd => (hlo s hs hd).1, hhi⟩

end PaperVerification.AlternatingForms
