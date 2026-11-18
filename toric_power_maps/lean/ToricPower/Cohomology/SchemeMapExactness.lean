module
public import ToricPower.Cohomology.SchemeConnectingMap
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
/-- The long exact cohomology sequence is exact at `Hⁿ(X, M₂)`. -/
theorem exact_cohomologyMap_cohomologyMap (n : ℕ) :
    Function.Exact (cohomologyMap S.f n) (cohomologyMap S.g n) := by
  intro x
  have hx := CategoryTheory.Sheaf.H.exact_map_map.{u, u, u}
    (shortExact_map_toSheaf hS) n x
  simpa only [cohomologyMap_eq_sheafH, cohomologyδ, Cohomology, cohomologyFunctor,
    CategoryTheory.Functor.comp_obj, CategoryTheory.Sheaf.functorH,
    ShortComplex.map_X₁, ShortComplex.map_X₂, ShortComplex.map_X₃,
    ShortComplex.map_f, ShortComplex.map_g] using hx


end TauCeti.AlgebraicGeometry.Scheme.Modules
end
