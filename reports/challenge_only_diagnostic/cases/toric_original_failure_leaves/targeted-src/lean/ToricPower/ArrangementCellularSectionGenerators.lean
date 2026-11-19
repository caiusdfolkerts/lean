module

public import ToricPower.ArrangementCellularAffineSections
public import ToricPower.CellularRealizationCoefficientGenerators

/-!
# Original cellular generators in actual affine sections

The quasicoherent inclusion and the genuine affine section comparison
retain each original copower generator and each original cell inclusion.
The formulas apply to unrestricted coefficient vectors.
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

local notation "A" => fanArrangementMatrix fan basis rays
local notation "Cells" => IncidenceObject A
local notation "X" => fan.algebraicRealization
local notation "Q" => arrangementDualLeftCartierDiagram fan nonempty regular basis rays
local notation "Qq" => arrangementDualLeftQuasicoherentDiagram fan nonempty regular basis rays
local notation "I" => quasicoherentInclusion X

local instance cellularSectionGenerators_qcohBiproducts : HasFiniteBiproducts (QCoh X) := HasFiniteBiproducts.of_hasFiniteProducts
local instance cellularSectionGenerators_moduleBiproducts : HasFiniteBiproducts (X).Modules := HasFiniteBiproducts.of_hasFiniteProducts

/-- Forgetting quasicoherence keeps the specified vector/cell map. -/
@[reassoc]
theorem arrangementCellularUnderlyingIso_generator
    (M : Cells ⥤ ModuleCat ℂ) (q : ℕ) (d : NormalizedCell A q) (x : M.obj ⟨q,d⟩) :
    (I).map (Cellular.vectorCopowerInclusion ℂ ((Qq).obj ⟨q,d⟩) (M.obj ⟨q,d⟩) x ≫
      arrangementCellularCochainInclusion A ℂ (Cellular.covariantCopowerDiagram ℂ Qq M) q d) ≫
        (arrangementCellularUnderlyingIso fan nonempty regular basis rays M).hom.f q =
      Cellular.vectorCopowerInclusion ℂ ((Q).obj ⟨q,d⟩) (M.obj ⟨q,d⟩) x ≫
        arrangementCellularCochainInclusion A ℂ (Cellular.covariantCopowerDiagram ℂ Q M) q d := by
  change (I).map (_ ≫ _) ≫ (cellularCoefficientTermIso A ℂ I
      (Cellular.covariantCopowerDiagram ℂ Qq M) q).hom ≫
      ((arrangementCellularCochainFunctor A ℂ).map
        (Cellular.covariantCopowerCoefficientIso ℂ M I Qq).hom).f q = _
  rw [CategoryTheory.Functor.map_comp, Category.assoc,
    cellularCoefficientTermIso_inclusion_assoc, cellularCochainMap_inclusion]
  change (I).map (Cellular.vectorCopowerInclusion ℂ ((Qq).obj ⟨q,d⟩)
    (M.obj ⟨q,d⟩) x) ≫
      (Cellular.vectorCopowerComparisonIso ℂ I ((Qq).obj ⟨q,d⟩) (M.obj ⟨q,d⟩)).hom ≫ _ = _
  rw [Cellular.vectorCopowerComparisonIso_inclusion_assoc]
  rfl

/-- The original sheaf complex has the same full affine Laurent
comparison after undoing the actual quasicoherent inclusion map. -/
def arrangementSheafAffineSectionsIso (σ : fan.cones) (M : Cells ⥤ ModuleCat ℂ) :
    ((FiniteCover.schemeBaseSections ℂ X (fan.affineToricChartι σ).opensRange).mapHomologicalComplex
      (.up ℕ)).obj
      ((arrangementCellularSheafRealization fan nonempty regular basis rays).obj M) ≅
      (arrangementCellularRealization A ℂ
        (reflectedLaurentDiagram A (fanConeRaySet fan rays σ) ℂ)).obj M :=
  ((FiniteCover.schemeBaseSections ℂ X (fan.affineToricChartι σ).opensRange).mapHomologicalComplex
    (.up ℕ)).mapIso (arrangementCellularUnderlyingIso fan nonempty regular basis rays M).symm ≪≫
      arrangementCellularAffineSectionsIso fan nonempty regular basis rays σ M

/-- The original section comparison keeps the complete coefficient
vector and the exact cell inclusion. -/
@[reassoc]
theorem arrangementSheafAffineSectionsIso_generator
    (σ : fan.cones) (M : Cells ⥤ ModuleCat ℂ) (q : ℕ)
    (d : NormalizedCell A q) (x : M.obj ⟨q,d⟩) :
    (FiniteCover.schemeBaseSections ℂ X (fan.affineToricChartι σ).opensRange).map
      (Cellular.vectorCopowerInclusion ℂ ((Q).obj ⟨q,d⟩) (M.obj ⟨q,d⟩) x ≫
        arrangementCellularCochainInclusion A ℂ
          (Cellular.covariantCopowerDiagram ℂ Q M) q d) ≫
      (arrangementSheafAffineSectionsIso fan nonempty regular basis rays σ M).hom.f q =
    (reflectedToricSectionsDiagramIso fan nonempty regular basis rays σ).inv.app ⟨q,d⟩ ≫
      Cellular.vectorCopowerInclusion ℂ
        ((reflectedLaurentDiagram A (fanConeRaySet fan rays σ) ℂ).obj ⟨q,d⟩)
        (M.obj ⟨q,d⟩) x ≫
      arrangementCellularCochainInclusion A ℂ
        (Cellular.covariantCopowerDiagram ℂ
          (reflectedLaurentDiagram A (fanConeRaySet fan rays σ) ℂ) M) q d := by
  let G := FiniteCover.schemeBaseSections ℂ X (fan.affineToricChartι σ).opensRange
  let e := arrangementCellularUnderlyingIso fan nonempty regular basis rays M
  have inverse : e.hom.f q ≫ e.inv.f q = 𝟙 _ :=
    congrArg (fun f => f.f q) e.hom_inv_id
  change (G).map _ ≫ (G).map (e.inv.f q) ≫
    (arrangementCellularAffineSectionsIso fan nonempty regular basis rays σ M).hom.f q = _
  rw [← arrangementCellularUnderlyingIso_generator fan nonempty regular basis rays M q d x]
  rw [← (G).map_comp_assoc]
  change (G).map ((I).map
    (Cellular.vectorCopowerInclusion ℂ ((Qq).obj ⟨q,d⟩) (M.obj ⟨q,d⟩) x ≫
      arrangementCellularCochainInclusion A ℂ (Cellular.covariantCopowerDiagram ℂ Qq M) q d) ≫
        e.hom.f q ≫ e.inv.f q) ≫ _ = _
  erw [inverse, Category.comp_id]
  exact cellularRealizationCoefficientObjectIso_generator A ℂ
    (arrangementAffineSectionFunctor fan σ) Qq
    (reflectedLaurentDiagram A (fanConeRaySet fan rays σ) ℂ)
    (reflectedToricSectionsDiagramIso fan nonempty regular basis rays σ).symm M q d x

end ToricPower

end
