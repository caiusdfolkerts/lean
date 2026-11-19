module

public import ToricPower.ToricCoherentCartierCover
public import ToricPower.CoherentCohomologyFiniteness
public import ToricPower.ToricCohomologyBound

/-!
# The geometric reduction of coherent cohomology finiteness

The finite Cartier cover and the uniform finite-cover vanishing bound are
proved for the actual smooth toric variety. The final wrapper isolates
only actual complex-linear Cartier finiteness. It does not assert this
input merely from an additive comparison.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory TauCeti.Toric
open TauCeti.AlgebraicGeometry.Scheme.Modules

namespace ToricPower

universe v

variable {N : Type} {V : Type v} [AddCommGroup N] [AddCommGroup V]
  [Module ℝ V] {i : N →+ V}

/-- Actual all-coherent finiteness follows from the precise linear
Cartier finiteness and finite-cover vanishing inputs. -/
theorem toricCoherentCohomology_finite_of_cartier_and_bound
    (fan : Fan i) (nonempty : Nonempty fan.cones) (regular : fan.IsRegular) :
    letI := toricSchemeIntegral fan nonempty
    (∀ (D : TauCeti.AlgebraicGeometry.Scheme.CartierDivisor fan.algebraicRealization)
      (degree : ℕ), FiniteDimensional ℂ (Cohomology D.sheaf degree)) →
    ∀ bound : ℕ,
      (∀ (M : fan.algebraicRealization.Modules) [M.IsFinitePresentation] (degree : ℕ),
        bound < degree → Subsingleton (Cohomology M degree)) →
      ∀ (M : fan.algebraicRealization.Modules) [M.IsFinitePresentation] (degree : ℕ),
        FiniteDimensional ℂ (Cohomology M degree) := by
  letI := toricSchemeIntegral fan nonempty
  letI := toricScheme_isNoetherian fan
  intro cartierFinite bound vanishes M hM degree
  exact coherentCohomology_finite_of_cartier_and_bound ℂ fan.algebraicRealization
    (toricFiniteCartierEpimorphism fan nonempty regular) cartierFinite bound vanishes M degree

/-- The proved toric Čech dimension bound removes the uniform vanishing
premise: actual complex-linear Cartier finiteness suffices for all
coherent sheaves, in every cohomological degree. -/
theorem toricCoherentCohomology_finite_of_cartier
    (fan : Fan i) (nonempty : Nonempty fan.cones) (regular : fan.IsRegular) :
    letI := toricSchemeIntegral fan nonempty
    (∀ (D : TauCeti.AlgebraicGeometry.Scheme.CartierDivisor fan.algebraicRealization)
      (degree : ℕ), FiniteDimensional ℂ (Cohomology D.sheaf degree)) →
      ∀ (M : fan.algebraicRealization.Modules) [M.IsFinitePresentation] (degree : ℕ),
        FiniteDimensional ℂ (Cohomology M degree) := by
  letI := toricSchemeIntegral fan nonempty
  intro cartierFinite
  apply toricCoherentCohomology_finite_of_cartier_and_bound
    fan nonempty regular cartierFinite (Nat.card fan.cones)
  intro M hM degree high
  exact toricQuasicoherentCohomology_subsingleton fan M degree high

end ToricPower

end
