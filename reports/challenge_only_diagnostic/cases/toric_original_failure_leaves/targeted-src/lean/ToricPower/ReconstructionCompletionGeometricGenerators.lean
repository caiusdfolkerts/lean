module

public import ToricPower.ReconstructionCompletionGeometricAugmentation
public import ToricPower.ReconstructionCompletionGeometricTransport

/-! # Literal generators of the geometric reconstruction map

The ordinary quasicoherent lift retains the specified diagonal top
quotient. Its evaluation on a cellular Hom coefficient is the actual
unit-source map into the inverse twist, followed by that quotient.
-/

@[expose] public noncomputable section

set_option maxHeartbeats 600000
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
local notation "T" => Cellular.covariantTensorDiagram Q R
local notation "Ts" => Cellular.covariantTensorDiagram Qs Rs
local notation "P" => Scheme.Modules.pullback (toricDiagonal fan)
local notation "ε" => reconstructionTensorTopAugmentation fan nonempty regular basis rays

local instance : HasFiniteBiproducts (QCoh X) := HasFiniteBiproducts.of_hasFiniteProducts
local instance : HasFiniteBiproducts (X).Modules := HasFiniteBiproducts.of_hasFiniteProducts
local instance : MonoidalLinear ℂ (QCoh X) where
  whiskerLeft_smul := by
    intro B₁ B₂ B₃ a f
    exact (tensorLeft B₁).map_smul a f
  smul_whiskerRight := by
    intro a B₁ B₂ f B₃
    exact (tensorRight B₃).map_smul a f
local instance (q : ℕ) : Fintype (NormalizedCell A q) := Fintype.ofFinite _

/-- Forgetting the ordinary full-subcategory lift gives exactly the
specified top quotient, with its original source comparison. -/
theorem reconstructionTensorTopAugmentation_underlying :
    (IC).map ε ≫
        (HomologicalComplex.singleMapHomologicalComplex I (.up ℕ) n).hom.app J =
      (cellularCoefficientComplexIso A ℂ I T).hom ≫
        (arrangementCellularCochainFunctor A ℂ).map
          (reconstructionTensorLabelUnderlyingIso fan nonempty regular basis rays).hom ≫
        (diagonalPulledCellularComplexIso fan nonempty regular basis rays).inv ≫
          dualDiagonalPulledTopAugmentation fan nonempty regular basis rays := by
  rw [reconstructionTensorTopAugmentation, Functor.map_preimage]
  simp only [Category.assoc, Iso.inv_hom_id_app, Category.comp_id]
  all_goals rfl

/-- The original diagonal quotient on each original tensor-labelled
cellular generator survives the quasicoherent lift unchanged. -/
@[reassoc]
theorem reconstructionTensorTopAugmentation_generator (d : NormalizedCell A n) :
    (I).map (arrangementCellularCochainInclusion A ℂ T n d ≫
        singleAugmentationComponent ε) =
      (reconstructionTensorLabelUnderlyingIso fan nonempty regular basis rays).hom.app ⟨n,d⟩ ≫
        (diagonalPulledInverseCoefficientIso fan nonempty regular basis rays).inv.app ⟨n,d⟩ ≫
          (P).map (diagonalInverseCellTopQuotient fan nonempty regular basis rays d) := by
  have mapped := congrArg singleAugmentationComponent
    (reconstructionTensorTopAugmentation_underlying fan nonempty regular basis rays)
  rw [singleAugmentationComponent_map, singleAugmentationComponent_comp,
    singleAugmentationComponent_comp, singleAugmentationComponent_comp] at mapped
  have component : singleAugmentationComponent
      (dualDiagonalPulledTopAugmentation fan nonempty regular basis rays) =
      (P).map (dualDiagonalTopQuotient fan nonempty regular basis rays) := by
    simp only [singleAugmentationComponent, dualDiagonalPulledTopAugmentation,
      HomologicalComplex.mkHomToSingle_f, Category.assoc,
      Iso.inv_hom_id, Category.comp_id]
  rw [Functor.map_comp, mapped]
  have inclusion :
      (I).map (arrangementCellularCochainInclusion A ℂ T n d) ≫
        (cellularCoefficientComplexIso A ℂ I T).hom.f n =
      arrangementCellularCochainInclusion A ℂ (T ⋙ I) n d :=
    cellularCoefficientTermIso_inclusion A ℂ I T n d
  rw [reassoc_of% inclusion, cellularCochainMap_inclusion_assoc,
    diagonalPulledCellularComplexIso_inverse_inclusion_assoc,
    component, ← Functor.map_comp]
  rfl

/-- Evaluation uses the complete original Hom coefficient. No choice
of a basis or a finite-dimensional subspace enters this identity. -/
@[reassoc]
theorem reconstructionGeometricAugmentation_generator (E : QCoh X)
    (d : NormalizedCell A n) (h : (P₀).obj (op ⟨n,d⟩) ⟶ E) :
    Cellular.vectorCopowerInclusion ℂ ((Q).obj ⟨n,d⟩)
        (((Cellular.homDiagram ℂ P₀).obj E).obj ⟨n,d⟩) h ≫
      arrangementCellularCochainInclusion A ℂ
        (Cellular.covariantCopowerDiagram ℂ Q ((Cellular.homDiagram ℂ P₀).obj E)) n d ≫
      singleAugmentationComponent
        ((reconstructionGeometricAugmentation fan nonempty regular basis rays).app E) =
      (ρ_ ((Q).obj ⟨n,d⟩)).inv ≫
        ((Q).obj ⟨n,d⟩) ◁
          (((reconstructionOriginalUnitHomIso fan nonempty regular basis rays).hom.app E).app ⟨n,d⟩ h) ≫
        (α_ ((Q).obj ⟨n,d⟩) ((R).obj ⟨n,d⟩) E).inv ≫
          (arrangementCellularCochainInclusion A ℂ T n d ≫
            singleAugmentationComponent ε) ▷ E := by
  exact cellularUnitTensorAugmentationTransport_generator A ℂ Q R J ε
    (Cellular.homDiagram ℂ P₀)
    (reconstructionOriginalUnitHomIso fan nonempty regular basis rays) E d h

end ToricPower

end
