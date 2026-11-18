module

public import ToricPower.ArrangementNormalizedRHom
public import ToricPower.CartierFiniteMeetLinear

/-!
# Scalar linearity of the actual normalized toric adjoint

The proof uses the canonical isomorphism to the full finite Čech derived
model. Thus it retains the actual boundary twist, dimension shift, and
all source-incidence maps, on every unbounded quasicoherent object.
-/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TauCeti.Toric
open ToricPower.IntegralArrangement

namespace ToricPower

variable {N : Type} {V : Type*} [AddCommGroup N] [AddCommGroup V]
  [Module ℝ V] {i : N →+ V} (fan : Fan i)
  (nonempty : Nonempty fan.cones) (regular : fan.IsRegular)
  {n s : ℕ} (basis : Module.Basis (Fin n) ℤ (N →+ ℤ)) (rays : Fin s ≃ fan.Ray)

local instance normalizedLinearityDerivedQCoh : HasDerivedCategory.{1} (QCoh fan.algebraicRealization) :=
  HasDerivedCategory.standard _
local instance normalizedLinearityDerivedIncidence : HasDerivedCategory.{1}
    (IncidenceObject (fanArrangementMatrix fan basis rays) ⥤ ModuleCat.{0} ℂ) :=
  HasDerivedCategory.standard _
local instance normalizedLinearityDerivedChart : HasDerivedCategory.{1}
    ((ToricMeetChartIndex fan)ᵒᵖ ⥤ ModuleCat.{0} ℂ) :=
  HasDerivedCategory.standard _

instance normalizedCartierChartDiagram_linear :
    (normalizedCartierChartDiagram fan nonempty regular basis rays).Linear ℂ := by
  letI := toricSchemeIntegral fan nonempty
  unfold normalizedCartierChartDiagram
  infer_instance

instance normalizedCartierFiniteModel_linear :
    (normalizedCartierFiniteModel fan nonempty regular basis rays).Linear ℂ := by
  unfold normalizedCartierFiniteModel
  letI := (normalizedCartierChartDiagram_exact fan nonempty regular basis rays).1
  letI := (normalizedCartierChartDiagram_exact fan nonempty regular basis rays).2
  infer_instance

instance arrangementNormalizedDerivedHom_linear :
    letI := nonempty
    (arrangementNormalizedDerivedHom fan regular basis rays).Linear ℂ := by
  letI := nonempty
  exact Functor.linear_of_iso ℂ
    (arrangementNormalizedHomFiniteModelIso fan nonempty regular basis rays).symm

end ToricPower
end
