module

public import ToricPower.Cohomology.SchemeCoefficientMaps
public import ToricPower.Cohomology.SheafFunctorExact

/-! The actual connecting morphism for sheaves of modules. -/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1000000

open CategoryTheory Limits TopologicalSpace AlgebraicGeometry Scheme.Modules

namespace TauCeti.AlgebraicGeometry.Scheme.Modules

universe u

variable {X : Scheme.{u}}

variable {S : ShortComplex X.Modules} (hS : S.ShortExact)

include hS

/-- The connecting map `Hⁿ⁰(X, M₃) →+ Hⁿ¹(X, M₁)` of the long exact cohomology sequence of a
short exact sequence `0 ⟶ M₁ ⟶ M₂ ⟶ M₃ ⟶ 0` of sheaves of modules. -/
abbrev cohomologyδ (n₀ n₁ : ℕ) (h : n₀ + 1 = n₁) :
    Cohomology S.X₃ n₀ →+ Cohomology S.X₁ n₁ :=
  ToricPower.SheafCohomology.functorConnectingMap.{u, u, u, u + 1, u} (toSheaf X) (S := S) (shortExact_map_toSheaf hS) n₀ n₁ h


end TauCeti.AlgebraicGeometry.Scheme.Modules

end
