module

public import ToricPower.ReconstructionCompletionGeometricCellular
public import ToricPower.ArrangementOriginalAffineHom
public import ToricPower.ArrangementRepresentedQuasicoherentAugmentation
public import ToricPower.DiagonalPulledCellularInclusions
public import ToricPower.QuasicoherentTensorLinear

/-!
# Geometric reconstruction from the original diagonal top quotient

The actual inverse-twist Hom comparison and the literal pulled diagonal
quotient define a natural cellular augmentation on every quasicoherent
coefficient. It is constructed in the ordinary category, before any
claim of derived invertibility.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite
open TauCeti.Toric ToricPower.IntegralArrangement

namespace ToricPower

variable {N : Type} {V : Type*} [AddCommGroup N] [AddCommGroup V]
  [Module ℝ V] {i : N →+ V} (fan : Fan i)
  (nonempty : Nonempty fan.cones) (regular : fan.IsRegular)
  {n s : ℕ} (basis : Module.Basis (Fin n) ℤ (N →+ ℤ)) (rays : Fin s ≃ fan.Ray)

local notation "A" => fanArrangementMatrix fan basis rays
local notation "C" => IncidenceObject A
local notation "X" => fan.algebraicRealization
local notation "I" => quasicoherentInclusion X
local notation "IC" => Functor.mapHomologicalComplex I (ComplexShape.up ℕ)
local notation "Q" => arrangementDualLeftQuasicoherentDiagram fan nonempty regular basis rays
local notation "R" => arrangementDualRightQuasicoherentDiagram fan nonempty regular basis rays
local notation "Qs" => arrangementDualLeftCartierDiagram fan nonempty regular basis rays
local notation "Rs" => arrangementDualRightCartierDiagram fan nonempty regular basis rays
local notation "P₀" => arrangementRightQuasicoherentDiagram fan nonempty regular basis rays
local notation "J" => dualDiagonalLineQuasicoherent fan nonempty regular basis rays
local notation "Φ" => arrangementQuasicoherentCellularRealization fan nonempty regular basis rays
local notation "T" => Cellular.covariantTensorDiagram Q R
local notation "Ts" => Cellular.covariantTensorDiagram Qs Rs

local instance geometricAugmentationQCohBiproducts : HasFiniteBiproducts (QCoh X) :=
  HasFiniteBiproducts.of_hasFiniteProducts
local instance geometricAugmentationSheafBiproducts : HasFiniteBiproducts (X).Modules :=
  HasFiniteBiproducts.of_hasFiniteProducts
local instance geometricAugmentationMonoidalLinear : MonoidalLinear ℂ (QCoh X) where
  whiskerLeft_smul := by
    intro B₁ B₂ B₃ a f
    exact (tensorLeft B₁).map_smul a f
  smul_whiskerRight := by
    intro a B₁ B₂ f B₃
    exact (tensorRight B₃).map_smul a f

/-- The original right-label Hom diagram, expressed as actual maps
from the structure sheaf into the original inverse twist. -/
def reconstructionOriginalUnitHomIso :
    Cellular.homDiagram ℂ P₀ ≅ Cellular.unitTensorSectionFunctor ℂ R :=
  arrangementOriginalCartierHomSectionsIso fan nonempty regular basis rays ≪≫
    Functor.isoWhiskerLeft ((R ⋙ tensoringLeft (QCoh X)).flip)
      ((Functor.whiskeringRight C (QCoh X) (ModuleCat ℂ)).mapIso
        (reconstructionQuasicoherentUnitHomSectionsIso ℂ X).symm)

/-- The genuine tensor labels retain their original underlying sheaves
and every original incidence map. -/
def reconstructionTensorLabelUnderlyingIso : T ⋙ I ≅ Ts :=
  NatIso.ofComponents (fun c => (tensorLeft ((Qs).obj c)).mapIso
      ((arrangementDualRightQuasicoherentInclusionIso fan nonempty regular basis rays).app c))
    (by
      intro c d f
      change ((Qs).map f ⊗ₘ (I).map ((R).map f)) ≫
          (Qs).obj d ◁ (arrangementDualRightQuasicoherentInclusionIso
            fan nonempty regular basis rays).hom.app d =
        (Qs).obj c ◁ (arrangementDualRightQuasicoherentInclusionIso
            fan nonempty regular basis rays).hom.app c ≫
          ((Qs).map f ⊗ₘ (Rs).map f)
      rw [tensorHom_comp_whiskerLeft, whiskerLeft_comp_tensorHom]
      exact congrArg (fun g => (Qs).map f ⊗ₘ g)
        ((arrangementDualRightQuasicoherentInclusionIso
          fan nonempty regular basis rays).hom.naturality f))

/-- The original pulled diagonal quotient, lifted through the full
ordinary quasicoherent inclusion. -/
def reconstructionTensorTopAugmentation :
    arrangementCellularCochainComplex A ℂ T ⟶
      (HomologicalComplex.single (QCoh X) (.up ℕ) n).obj J :=
  (IC).preimage
    ((cellularCoefficientComplexIso A ℂ I T).hom ≫
      (arrangementCellularCochainFunctor A ℂ).map
        (reconstructionTensorLabelUnderlyingIso fan nonempty regular basis rays).hom ≫
      (diagonalPulledCellularComplexIso fan nonempty regular basis rays).inv ≫
        dualDiagonalPulledTopAugmentation fan nonempty regular basis rays ≫
          (HomologicalComplex.singleMapHomologicalComplex I (.up ℕ) n).inv.app J)

/-- The complete geometric natural augmentation on every quasicoherent
coefficient, with no boundedness or finite-presentation assumption. -/
def reconstructionGeometricAugmentation :
    Cellular.homDiagram ℂ P₀ ⋙ Φ ⟶
      tensorLeft J ⋙ HomologicalComplex.single (QCoh X) (.up ℕ) n :=
  Functor.whiskerRight
      (reconstructionOriginalUnitHomIso fan nonempty regular basis rays).hom Φ ≫
    cellularUnitTensorAugmentation A ℂ Q R J
      (reconstructionTensorTopAugmentation fan nonempty regular basis rays)

end ToricPower

end
