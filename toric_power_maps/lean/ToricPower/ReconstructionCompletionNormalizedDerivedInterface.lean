module

public import ToricPower.ReconstructionCompletionToricFactors

/-! # The normalized realization at the original diagram localization

The original right adjoint and normalized realization used separately named
standard localization instances. This interface retains the original
realization while fixing its source to the right adjoint's chosen derived
category, before the reconstruction comparison is assembled.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TauCeti.Toric
open ToricPower.IntegralArrangement

namespace ToricPower

attribute [local instance 2000] arrangementToricDiagramHasDerivedCategory
attribute [local instance 2000] quasicoherentStandardDerivedCategory

variable {N : Type} {V : Type*} [AddCommGroup N] [AddCommGroup V]
  [Module ℝ V] {i : N →+ V}
  (fan : Fan i) [nonempty : Nonempty fan.cones] (regular : fan.IsRegular)
  {n s : ℕ} (basis : Module.Basis (Fin n) ℤ (N →+ ℤ)) (rays : Fin s ≃ fan.Ray)

local notation "A" => fanArrangementMatrix fan basis rays
local notation "X" => fan.algebraicRealization
local notation "Φ" => arrangementQuasicoherentCellularRealization fan nonempty regular basis rays

local instance reconstructionNormalizedInterfaceBiproducts : HasFiniteBiproducts (QCoh X) :=
  HasFiniteBiproducts.of_hasFiniteProducts

/-- The original normalized realization, in the literal source category
of the original derived Hom functor. -/
def reconstructionNormalizedDerivedInterface :
    DerivedCategory (IncidenceObject A ⥤ ModuleCat.{0} ℂ) ⥤ DerivedQCoh X :=
  arrangementNormalizedDerivedRealization fan regular basis rays

instance reconstructionNormalizedDerivedInterface_commShift :
    (reconstructionNormalizedDerivedInterface fan regular basis rays).CommShift ℤ :=
  arrangementNormalizedDerivedRealization_commShift fan regular basis rays

instance reconstructionNormalizedDerivedInterface_isTriangulated :
    (reconstructionNormalizedDerivedInterface fan regular basis rays).IsTriangulated :=
  arrangementNormalizedDerivedRealization_isTriangulated fan regular basis rays

/-- The typed interface retains exactly the original functor. -/
def reconstructionNormalizedDerivedInterfaceIso :
    reconstructionNormalizedDerivedInterface fan regular basis rays ≅
      arrangementNormalizedDerivedRealization fan regular basis rays :=
  Iso.refl _

/-- The original whole cellular factorization in the same chosen
diagram derived category. -/
def reconstructionNormalizedInterfaceCellularFactors :
    DerivedCategory.Q ⋙ reconstructionNormalizedDerivedInterface fan regular basis rays ≅
      FunctorTotal.functor Φ (n + 1) ⋙ DerivedCategory.Q :=
  reconstructionCellularDerivedFactors fan regular basis rays

end ToricPower

end
