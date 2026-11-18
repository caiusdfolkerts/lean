module
public import ToricPower.Cohomology.SchemeMapExactness
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1000000
open CategoryTheory Limits TopologicalSpace AlgebraicGeometry Scheme.Modules
namespace TauCeti.AlgebraicGeometry.Scheme.Modules
universe u
variable {X : Scheme.{u}} {S : ShortComplex X.Modules} (hS : S.ShortExact)
include hS
/-- The long exact sequence is exact immediately before its connecting map. -/
theorem exact_cohomologyMap_cohomologyδ (n₀ n₁ : ℕ) (h : n₀ + 1 = n₁) :
    Function.Exact (cohomologyMap S.g n₀) (cohomologyδ hS n₀ n₁ h) := by
  simpa only [cohomologyMap, cohomologyMapAddHom, cohomologyFunctor, Cohomology, cohomologyδ] using
    ToricPower.SheafCohomology.exact_functor_map_connecting.{u, u, u, u + 1, u} (toSheaf X) (S := S)
      (shortExact_map_toSheaf hS) n₀ n₁ h

/-- The long exact sequence is exact immediately after its connecting map. -/
theorem exact_cohomologyδ_cohomologyMap (n₀ n₁ : ℕ) (h : n₀ + 1 = n₁) :
    Function.Exact (cohomologyδ hS n₀ n₁ h) (cohomologyMap S.f n₁) := by
  simpa only [cohomologyMap, cohomologyMapAddHom, cohomologyFunctor, Cohomology, cohomologyδ] using
    ToricPower.SheafCohomology.exact_functor_connecting_map.{u, u, u, u + 1, u} (toSheaf X) (S := S)
      (shortExact_map_toSheaf hS) n₀ n₁ h

end TauCeti.AlgebraicGeometry.Scheme.Modules
end
