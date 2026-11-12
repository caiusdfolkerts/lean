module

public import ToricPower.ArrangementRepresentedQuasicoherentAugmentation
public import ToricPower.CellularLinearNaturalExtension
public import ToricPower.CellularProjectiveComparison
public import ToricPower.QuasicoherentExactCoproducts
public import ToricPower.QuasicoherentTensorColimits
public import ToricPower.MappedCellularEvaluation
public import ToricPower.HomologicalComplexColimitLinear
public import ToricPower.QuasicoherentTensorLinear

/-!
# The original top augmentation on all cellular coefficients

The source-natural maps on genuine free representables extend by the
actual linear coend density presentation. The extension retains those
maps exactly. Its composite with the actual coend evaluation gives a
natural cellular reconstruction map on every quasicoherent sheaf.
No reconstruction isomorphism is asserted in this construction file.
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
local notation "Cells" => IncidenceObject A
local notation "X" => fan.algebraicRealization
local notation "J" => dualDiagonalLineQuasicoherent fan nonempty regular basis rays
local notation "P₀" => arrangementRightQuasicoherentDiagram fan nonempty regular basis rays
local notation "P" => arrangementRightTopLineDiagram fan nonempty regular basis rays
local notation "Φ" => arrangementQuasicoherentCellularRealization fan nonempty regular basis rays
local notation "rep" => Cellular.representableFunctor ℂ (C := Cells)
local notation "H" => Cellular.realization ℂ P
local notation "single" => HomologicalComplex.single (QCoh X) (ComplexShape.up ℕ) n

/-- The original represented top map with the canonical coend frame
inserted, so both source and target are values of actual diagram functors. -/
def arrangementRepresentedCoendAugmentation : rep ⋙ Φ ⟶ rep ⋙ (H ⋙ single) :=
  arrangementRepresentedQuasicoherentAugmentation fan nonempty regular basis rays ≫
    (Functor.isoWhiskerRight (Cellular.realizationRepresentableNatIso ℂ P) single).inv ≫
      (Functor.associator rep H single).hom

/-- The actual top quotient on every coefficient diagram, with no
projectivity, dimension, or support hypothesis. -/
def arrangementCellularAugmentation : Φ ⟶ H ⋙ single :=
  Cellular.densityExtensionToFunctor ℂ (H ⋙ single) Φ
    (arrangementRepresentedCoendAugmentation fan nonempty regular basis rays)

/-- The extension is literally the original represented map. -/
theorem arrangementCellularAugmentation_representable (c : Cells) :
    (arrangementCellularAugmentation fan nonempty regular basis rays).app
        (Cellular.representable ℂ c) =
      (arrangementRepresentedCoendAugmentation fan nonempty regular basis rays).app (op c) :=
  Cellular.densityExtensionToFunctor_representable ℂ (H ⋙ single) Φ
    (arrangementRepresentedCoendAugmentation fan nonempty regular basis rays) c

/-- The extension respects every original coefficient generator. -/
@[reassoc]
theorem arrangementCellularAugmentation_generator
    (M : Cells ⥤ ModuleCat ℂ) (c : Cells) (x : M.obj c) :
    (Φ).map (Cellular.fromValue ℂ M c x) ≫
        (arrangementCellularAugmentation fan nonempty regular basis rays).app M =
      (arrangementRepresentedCoendAugmentation fan nonempty regular basis rays).app (op c) ≫
        (H ⋙ single).map (Cellular.fromValue ℂ M c x) :=
  Cellular.densityExtensionToFunctor_generator ℂ (H ⋙ single) Φ
    (arrangementRepresentedCoendAugmentation fan nonempty regular basis rays) M c x

/-- The same actual augmentation is a quasi-isomorphism on every
projective coefficient once the separate represented geometry is supplied. -/
theorem arrangementCellularAugmentation_projective_quasiIso
    (represented : ∀ c : Cells,
      QuasiIso (arrangementRepresentedTopAugmentation fan nonempty regular basis rays c))
    (M : Cells ⥤ ModuleCat ℂ) [Projective M] :
    QuasiIso ((arrangementCellularAugmentation fan nonempty regular basis rays).app M) := by
  apply Cellular.naturalComparison_projective_quasiIso ℂ _ _ M
  intro c
  rw [arrangementCellularAugmentation_representable]
  letI := represented c
  letI := arrangementRepresentedQuasicoherentAugmentation_quasiIso_of_top
    fan nonempty regular basis rays c
  change QuasiIso (_ ≫ _ ≫ _)
  infer_instance

/-- The actual quotient is epimorphic on every diagram, without
projectivity or a finite-dimensional coefficient restriction. -/
theorem arrangementCellularAugmentation_epi
    (represented : ∀ c : Cells,
      QuasiIso (arrangementRepresentedTopAugmentation fan nonempty regular basis rays c))
    (M : Cells ⥤ ModuleCat ℂ) :
    Epi ((arrangementCellularAugmentation fan nonempty regular basis rays).app M) := by
  apply Cellular.naturalComparison_epi_of_representables ℂ _ _ M
  intro c
  rw [arrangementCellularAugmentation_representable]
  letI := represented c
  letI := arrangementRepresentedQuasicoherentAugmentation_epi_of_top
    fan nonempty regular basis rays c
  change Epi (_ ≫ _ ≫ _)
  infer_instance

/-- Ordinary coend evaluation, tensored with the genuine top line.
The mapped-coend comparison and the adjunction counit are the actual maps. -/
def arrangementTopLineEvaluation :
    Cellular.homDiagram ℂ P₀ ⋙ H ⟶ tensorRight J :=
  Cellular.mappedRealizationCounit ℂ (tensorRight J) P₀

/-- The actual global cellular evaluation augmentation. Its eventual
quasi-isomorphism is a geometric theorem, not part of its definition. -/
def arrangementCellularEvaluationAugmentation :
    Cellular.homDiagram ℂ P₀ ⋙ Φ ⟶ tensorRight J ⋙ single :=
  Functor.whiskerLeft (Cellular.homDiagram ℂ P₀)
      (arrangementCellularAugmentation fan nonempty regular basis rays) ≫
    (Functor.associator (Cellular.homDiagram ℂ P₀) H single).inv ≫
    Functor.whiskerRight (arrangementTopLineEvaluation fan nonempty regular basis rays) single

end ToricPower

end
