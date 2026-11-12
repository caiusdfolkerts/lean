module

public import ToricPower.ArrangementNormalizedLift
public import ToricPower.WeightedDerivedCoverLift

/-!
# The normalized right adjoint as the actual universal-cover direct image

The coefficient is the original Cartier line with the inverse boundary
twist. The final shift is exactly the lattice rank. Neither the character
family nor the coefficient complex is restricted.
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
  [nonempty : Nonempty fan.cones] (regular : fan.IsRegular)
  {n s : ℕ} (basis : Module.Basis (Fin n) ℤ (N →+ ℤ)) (rays : Fin s ≃ fan.Ray)

local notation "A" => fanArrangementMatrix fan basis rays

local instance normalizedCoverDerivedQCoh :
    HasDerivedCategory.{1} (QCoh fan.algebraicRealization) := HasDerivedCategory.standard _
local instance normalizedCoverDerivedCells :
    HasDerivedCategory.{1} (IncidenceObject A ⥤ ModuleCat.{0} ℂ) :=
  HasDerivedCategory.standard _
local instance normalizedCoverDerivedElements :
    HasDerivedCategory.{1} ((universalWeightFunctor A).Elements ⥤ ModuleCat.{0} ℂ) :=
  HasDerivedCategory.standard _

/-- The unrestricted normalized lift on the genuine category of elements. -/
def arrangementNormalizedCoverComplex (b : fan.Ray → ℤ) :
    CochainComplex ((universalWeightFunctor A).Elements ⥤ ModuleCat.{0} ℂ) ℤ :=
  weightedCoverLiftComplex A ℂ (arrangementNormalizedLiftedCech fan basis rays b)

/-- The direct-image formula for the actual normalized right adjoint. -/
def arrangementNormalizedRHomCoverPushdownIso (b : fan.Ray → ℤ) :
    (arrangementNormalizedDerivedHom fan regular basis rays).obj
        ((DerivedCategory.singleFunctor (QCoh fan.algebraicRealization) 0).obj
          (arrangementCartierCoefficient fan regular b)) ≅
      ((ElementPushdown.functor (universalWeightFunctor A) (D := ModuleCat.{0} ℂ)).mapDerivedCategory.obj
          (DerivedCategory.Q.obj (arrangementNormalizedCoverComplex fan basis rays b)))⟦(n : ℤ)⟧ :=
  arrangementNormalizedRHomWeightedPushdownIso fan regular basis rays b ≪≫
    (shiftFunctor _ (n : ℤ)).mapIso
      (weightedCoverPushdownIso A ℂ (arrangementNormalizedLiftedCech fan basis rays b)).symm

end ToricPower

end
