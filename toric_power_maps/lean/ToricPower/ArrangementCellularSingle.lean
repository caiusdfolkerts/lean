module

public import ToricPower.ArrangementCellularNormalization
public import ToricPower.FiniteFunctorTotalSingleInput

/-!
# Normalized realization on the original single coefficient diagram

The entire unbounded cellular model specializes on a diagram in degree
zero to its literal finite cellular cochain complex, extended by zero.
The normalization comparison keeps the original boundary twist and
dimension shift.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TauCeti.Toric
open ToricPower.IntegralArrangement

namespace ToricPower

variable {N : Type} {V : Type*} [AddCommGroup N] [AddCommGroup V]
  [Module ℝ V] {i : N →+ V} (fan : Fan i) [nonempty : Nonempty fan.cones]
  (regular : fan.IsRegular) {n s : ℕ}
  (basis : Module.Basis (Fin n) ℤ (N →+ ℤ)) (rays : Fin s ≃ fan.Ray)

local notation "Cells" => IncidenceObject (fanArrangementMatrix fan basis rays)
local notation "X" => fan.algebraicRealization
local notation "Φ" => arrangementQuasicoherentCellularRealization fan nonempty regular basis rays

local instance cellularSingleBiproducts : HasFiniteBiproducts (QCoh X) :=
  HasFiniteBiproducts.of_hasFiniteProducts
local instance cellularSingleDerivedTarget : HasDerivedCategory.{1} (QCoh X) :=
  HasDerivedCategory.standard _
local instance cellularSingleDerivedSource : HasDerivedCategory.{1} (Cells ⥤ ModuleCat.{0} ℂ) :=
  HasDerivedCategory.standard _

def arrangementCellularDerivedSingleIso (F : Cells ⥤ ModuleCat.{0} ℂ) :
    (arrangementCellularDerivedFunctor fan regular basis rays).obj
        ((DerivedCategory.singleFunctor (Cells ⥤ ModuleCat.{0} ℂ) 0).obj F) ≅
      DerivedCategory.Q.obj (((Φ).obj F).extend ComplexShape.embeddingUpNat) :=
  (complexFunctorDerivedFactors
      (arrangementCellularTotalFunctor fan nonempty regular basis rays)
      (fun f hf => by
        letI := hf
        exact arrangementCellularTotalFunctor_map_quasiIso fan nonempty regular basis rays f)).app
      ((CochainComplex.singleFunctor (Cells ⥤ ModuleCat.{0} ℂ) 0).obj F) ≪≫
    DerivedCategory.Q.mapIso
      (FunctorTotal.singleInputIso Φ (n+1) F (fun q high =>
        arrangementQuasicoherentCellularRealization_isZero_X_above fan nonempty regular basis rays
          F q (by omega)))

def arrangementNormalizedRealizationSingleIso (F : Cells ⥤ ModuleCat.{0} ℂ) :
    (arrangementNormalizedDerivedRealization fan regular basis rays).obj
        ((DerivedCategory.singleFunctor (Cells ⥤ ModuleCat.{0} ℂ) 0).obj F) ≅
      DerivedCategory.Q.obj (((Φ).obj F).extend ComplexShape.embeddingUpNat) :=
  (arrangementCellularDerivedNormalizedIso fan regular basis rays).symm.app
      ((DerivedCategory.singleFunctor (Cells ⥤ ModuleCat.{0} ℂ) 0).obj F) ≪≫
    arrangementCellularDerivedSingleIso fan regular basis rays F

end ToricPower
end
