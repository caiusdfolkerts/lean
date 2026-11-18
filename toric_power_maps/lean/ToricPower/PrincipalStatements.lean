module

public import ToricPower.SchemeCore
public import ToricPower.CoherentDerived

/-! # Exact principal target in the bounded derived category of coherent sheaves

This file records the statement to be proved.  It deliberately contains no
theorem asserting the principal claim.  In particular, a definition of the
claim is not counted as a verification of the paper.

The ambient category is the literal bounded derived category of the abelian
category of coherent sheaves.  No comparison with the bounded-coherent
part of the derived category of all module sheaves is assumed.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TauCeti.Toric

namespace ToricPower

universe u

variable {N : Type u} {V : Type*} [AddCommGroup N] [AddCommGroup V]
  [Module ℝ V] {i : N →+ V}

/-- The actual bounded derived category of coherent sheaves on the toric
scheme.  Noetherianity follows from the finite fan and its integral lattice. -/
abbrev ToricDbCoh (Φ : Fan i) :=
  letI := toricScheme_isNoetherian Φ
  DbCoh Φ.algebraicRealization

/-- The paper's ordinary positive-power direct image as a coherent sheaf
placed in degree zero in the literal bounded derived category. -/
def toricDbPowerObject (Φ : Fan i) (hreg : Φ.IsRegular)
    (hne : Φ.cones.Nonempty) (D : toricCartierDivisor Φ hne)
    (ell : ℕ) (hell : 0 < ell) : ToricDbCoh Φ := by
  letI := toricScheme_isNoetherian Φ
  exact coherentSingle Φ.algebraicRealization
    ⟨toricPowerDivisorSheaf Φ hne D ell,
      toricPowerDivisorSheaf_isFinitePresentation Φ hreg hne D ell hell⟩

/-- Classical generation of the actual bounded coherent derived category
by the actual power-map direct image. -/
def toricPowerGeneratesDbCoh (Φ : Fan i) (hreg : Φ.IsRegular)
    (hne : Φ.cones.Nonempty) (D : toricCartierDivisor Φ hne)
    (ell : ℕ) (hell : 0 < ell) : Prop := by
  letI := toricScheme_isNoetherian Φ
  exact generatesDbCoh (X := Φ.algebraicRealization) (toricDbPowerObject Φ hreg hne D ell hell)

/-- Theorem 1.1, as an exact goal proposition.  Its assumptions are precisely
a nonempty smooth finite fan over the complex numbers and an arbitrary
Cartier divisor.  The right-hand side tests every rational linear subspace,
with no completeness, projectivity, dimension, or exponent restriction.

This declaration has type `Prop`; it is not a proof of that proposition. -/
def principalTheoremDbCohClaim (Φ : Fan i) (hreg : Φ.IsRegular)
    (hne : Φ.cones.Nonempty) (D : toricCartierDivisor Φ hne) : Prop :=
  ((∃ (ell : ℕ) (hell : 0 < ell),
      toricPowerGeneratesDbCoh Φ hreg hne D ell hell) ↔
    linearCohomologyCriterion Φ hne D) ∧
  (linearCohomologyCriterion Φ hne D →
    ∃ (L : ℕ) (hL : 0 < L), ∀ (ell : ℕ) (hLell : L ≤ ell),
      toricPowerGeneratesDbCoh Φ hreg hne D ell (lt_of_lt_of_le hL hLell))

end ToricPower
