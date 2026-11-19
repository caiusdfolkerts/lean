module

public import ToricPower.ReconstructionCompletionGeometricGenerators
public import ToricPower.ReconstructionCompletionAffineCoefficientUnits
public import ToricPower.ReconstructionCompletionDiagonalRetraction

/-! # The original affine evaluation on underlying Cartier factors

The coefficient change is absorbed by the original inverse-twist unit
map. The resulting expression uses the same exterior retraction as the
actual diagonal quotient.
-/

@[expose] public noncomputable section

set_option quotPrecheck false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite
open TauCeti.Toric ToricPower.IntegralArrangement

namespace ToricPower

section Monoidal

universe u v
variable {B : Type u} [Category.{v} B] [MonoidalCategory B]

/-- The genuine middle-factor map is absorbed into the evaluated coefficient. -/
theorem reconstruction_tensorEvaluation_changeLabel
    (Q R R' E J : B) (x : 𝟙_ B ⟶ R ⊗ E) (f : R ⟶ R') (β : Q ⊗ R' ⟶ J) :
    (ρ_ Q).inv ≫ Q ◁ x ≫ (α_ Q R E).inv ≫ (Q ◁ f ≫ β) ▷ E =
      (ρ_ Q).inv ≫ Q ◁ (x ≫ f ▷ E) ≫ (α_ Q R' E).inv ≫ β ▷ E := by
  rw [comp_whiskerRight, ← associator_inv_naturality_middle_assoc,
    ← whiskerLeft_comp_assoc]

end Monoidal

variable {N : Type} {V : Type*} [AddCommGroup N] [AddCommGroup V]
  [Module ℝ V] {i : N →+ V} (fan : Fan i)
  (nonempty : Nonempty fan.cones) (regular : fan.IsRegular)
  {n s : ℕ} (basis : Module.Basis (Fin n) ℤ (N →+ ℤ)) (rays : Fin s ≃ fan.Ray)
  (τ : fan.cones)

local notation "A" => fanArrangementMatrix fan basis rays
local notation "X" => fan.algebraicRealization
local notation "I" => quasicoherentInclusion X
local notation "Q" => arrangementDualLeftCartierDiagram fan nonempty regular basis rays
local notation "Qq" => arrangementDualLeftQuasicoherentDiagram fan nonempty regular basis rays
local notation "R" => arrangementDualRightCartierDiagram fan nonempty regular basis rays
local notation "Rq" => arrangementDualRightQuasicoherentDiagram fan nonempty regular basis rays
local notation "P₀" => arrangementRightQuasicoherentDiagram fan nonempty regular basis rays
local notation "J" => dualDiagonalLineSheaf fan nonempty regular basis rays
local notation "E" => quasicoherentAffineUnitImage (fan.affineToricChartι τ)
local notation "M" => (Cellular.homDiagram ℂ P₀).obj E
local notation "Pull" => Scheme.Modules.pullback (toricDiagonal fan)

local instance : IsAffineHom (fan.affineToricChartι τ) := toricChartInclusion_isAffineHom fan τ
local instance : HasFiniteBiproducts (QCoh X) := HasFiniteBiproducts.of_hasFiniteProducts
local instance : HasFiniteBiproducts (X).Modules := HasFiniteBiproducts.of_hasFiniteProducts

/-- The original sheaf map attached to the original top cell. -/
def reconstructionUnderlyingTopCell (d : NormalizedCell A n) :
    (Q).obj ⟨n,d⟩ ⊗ (R).obj ⟨n,d⟩ ⟶ J :=
  (diagonalPulledInverseCoefficientIso fan nonempty regular basis rays).inv.app ⟨n,d⟩ ≫
    (Pull).map (diagonalInverseCellTopQuotient fan nonempty regular basis rays d)

/-- On every original Hom coefficient, the genuine reconstruction map
is exactly tensor evaluation followed by the genuine top-cell map. -/
@[reassoc]
theorem reconstructionGeometricAugmentation_underlying_generator
    (d : NormalizedCell A n) (h : (M).obj ⟨n,d⟩) :
    (I).map (Cellular.vectorCopowerInclusion ℂ ((Qq).obj ⟨n,d⟩) ((M).obj ⟨n,d⟩) h ≫
      arrangementCellularCochainInclusion A ℂ (Cellular.covariantCopowerDiagram ℂ Qq M) n d ≫
      singleAugmentationComponent
        ((reconstructionGeometricAugmentation fan nonempty regular basis rays).app E)) =
      (ρ_ ((Q).obj ⟨n,d⟩)).inv ≫
        ((Q).obj ⟨n,d⟩) ◁ (reconstructionAffineCoefficientUnit fan nonempty regular basis rays τ ⟨n,d⟩ h) ≫
        (α_ ((Q).obj ⟨n,d⟩) ((R).obj ⟨n,d⟩) (E).obj).inv ≫
        (reconstructionUnderlyingTopCell fan nonempty regular basis rays d) ▷ (E).obj := by
  rw [reconstructionGeometricAugmentation_generator]
  let T := Cellular.covariantTensorDiagram Qq Rq
  let β := arrangementCellularCochainInclusion A ℂ T n d ≫
    singleAugmentationComponent (reconstructionTensorTopAugmentation fan nonempty regular basis rays)
  change (ρ_ ((Q).obj ⟨n,d⟩)).inv ≫
      ((Q).obj ⟨n,d⟩) ◁
        (((reconstructionOriginalUnitHomIso fan nonempty regular basis rays).hom.app E).app ⟨n,d⟩ h).hom ≫
      (α_ ((Q).obj ⟨n,d⟩) (((Rq).obj ⟨n,d⟩).obj) (E).obj).inv ≫
      (I).map β ▷ (E).obj = _
  rw [show (I).map β =
      ((Q).obj ⟨n,d⟩) ◁
        ((arrangementDualRightQuasicoherentInclusionIso fan nonempty regular basis rays).hom.app ⟨n,d⟩) ≫
        reconstructionUnderlyingTopCell fan nonempty regular basis rays d from
    reconstructionTensorTopAugmentation_generator fan nonempty regular basis rays d]
  exact reconstruction_tensorEvaluation_changeLabel _ _ _ _ _ _ _ _

end ToricPower

end
