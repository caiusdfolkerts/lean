module

public import ToricPower.ArrangementRepresentableTopAugmentation
public import ToricPower.ArrangementRepresentedEvaluation
public import ToricPower.DiagonalCellularInclusions
public import ToricPower.SingleAugmentationComponent

/-!
# The represented top augmentation on its actual sheaf generators

The original coefficient and pullback comparisons carry each cellular
generator to its original inverse exterior label. Thus the represented
top map is literally the inverse-right incidence map followed by the
original diagonal top quotient. This fixes the actual map before its
affine Laurent coordinates are computed.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory
open TauCeti.Toric ToricPower.IntegralArrangement
open scoped Classical

namespace ToricPower

variable {N : Type} {V : Type*} [AddCommGroup N] [AddCommGroup V]
  [Module ℝ V] {i : N →+ V} (fan : Fan i)
  (nonempty : Nonempty fan.cones) (regular : fan.IsRegular)
  {n s : ℕ} (basis : Module.Basis (Fin n) ℤ (N →+ ℤ)) (rays : Fin s ≃ fan.Ray)

local notation "A" => fanArrangementMatrix fan basis rays
local notation "C" => IncidenceObject A
local notation "X" => fan.algebraicRealization
local notation "Y" => toricDiagonalProduct fan
local notation "Q" => arrangementDualLeftCartierDiagram fan nonempty regular basis rays
local notation "R" => arrangementDualRightCartierDiagram fan nonempty regular basis rays
local notation "M" => diagonalExteriorDualDiagram fan nonempty regular basis rays
local notation "T" => Cellular.covariantTensorDiagram Q R
local notation "P" => Scheme.Modules.pullback (toricDiagonal fan)

local instance pulledCellularInclusionCellsFintype (q : ℕ) :
    Fintype (NormalizedCell A q) := Fintype.ofFinite _
local instance pulledCellularInclusionXBiproducts : HasFiniteBiproducts (X).Modules :=
  HasFiniteBiproducts.of_hasFiniteProducts
local instance pulledCellularInclusionYBiproducts : HasFiniteBiproducts (Y).Modules :=
  HasFiniteBiproducts.of_hasFiniteProducts
local instance pulledCellularInclusionLeftQuasicoherent (c : C) :
    ((Q).obj c).IsQuasicoherent := by
  letI := toricSchemeIntegral fan nonempty
  letI := (invariantCartierDivisor fan nonempty regular
    (arrangementDualLeftCoefficients fan basis rays c)).isInvertible_sheaf
  change (invariantCartierDivisor fan nonempty regular
    (arrangementDualLeftCoefficients fan basis rays c)).sheaf.IsQuasicoherent
  infer_instance

/-- The exact coefficient comparison already used in the pulled
complex, now exposed as a natural isomorphism of its actual labels. -/
def diagonalPulledInverseCoefficientIso : M ⋙ P ≅ T :=
  Functor.isoWhiskerRight
      (diagonalExteriorCoefficientIso fan nonempty regular basis rays) P ≪≫
    diagonalPullbackExteriorDiagramIso fan Q R (fun _ => inferInstance)

/-- Actual forward pullback of the original inverse-cell inclusion. -/
@[reassoc]
theorem diagonalPulledCellularComplexIso_inclusion (q : ℕ)
    (c : NormalizedCell A q) :
    (P).map (biproduct.ι (fun d : NormalizedCell A q =>
        diagonalInverseProductSheaf fan nonempty regular basis rays d) c ≫
      (diagonalExteriorDualTermIso fan nonempty regular basis rays q).hom) ≫
        (diagonalPulledCellularComplexIso fan nonempty regular basis rays).hom.f q =
    (diagonalPulledInverseCoefficientIso fan nonempty regular basis rays).hom.app ⟨q,c⟩ ≫
      arrangementCellularCochainInclusion A ℂ T q c := by
  let e := diagonalExteriorDualComplexIso fan nonempty regular basis rays
  have inverse : e.inv.f q ≫ e.hom.f q = 𝟙 _ :=
    congrArg (fun f => f.f q) e.inv_hom_id
  have original :
      (biproduct.ι (fun d : NormalizedCell A q =>
        diagonalInverseProductSheaf fan nonempty regular basis rays d) c ≫
          (diagonalExteriorDualTermIso fan nonempty regular basis rays q).hom) ≫
        e.hom.f q = arrangementCellularCochainInclusion A ℂ M q c := by
    rw [← diagonalExteriorDualComplexIso_inclusion, Category.assoc,
      inverse, Category.comp_id]
  change (P).map _ ≫ (P).map (e.hom.f q) ≫
      (cellularCoefficientTermIso A ℂ P M q).hom ≫
        ((arrangementCellularCochainFunctor A ℂ).map
          (diagonalPulledInverseCoefficientIso fan nonempty regular basis rays).hom).f q = _
  rw [← Functor.map_comp_assoc, original,
    cellularCoefficientTermIso_inclusion_assoc, cellularCochainMap_inclusion]

/-- The actual inverse comparison on each original cellular inclusion. -/
@[reassoc]
theorem diagonalPulledCellularComplexIso_inverse_inclusion (q : ℕ)
    (c : NormalizedCell A q) :
    arrangementCellularCochainInclusion A ℂ T q c ≫
        (diagonalPulledCellularComplexIso fan nonempty regular basis rays).inv.f q =
      (diagonalPulledInverseCoefficientIso fan nonempty regular basis rays).inv.app ⟨q,c⟩ ≫
        (P).map (biproduct.ι (fun d : NormalizedCell A q =>
          diagonalInverseProductSheaf fan nonempty regular basis rays d) c ≫
            (diagonalExteriorDualTermIso fan nonempty regular basis rays q).hom) := by
  let e := diagonalPulledCellularComplexIso fan nonempty regular basis rays
  have inverse : e.inv.f q ≫ e.hom.f q = 𝟙 _ :=
    congrArg (fun f => f.f q) e.inv_hom_id
  apply (cancel_mono (e.hom.f q)).mp
  rw [Category.assoc, inverse, Category.comp_id, Category.assoc,
    diagonalPulledCellularComplexIso_inclusion]
  simp only [← Category.assoc, Iso.inv_hom_id_app, Category.id_comp]

/-- The specified represented top augmentation acts by the original
inverse-right incidence and the original top-cell quotient. -/
@[reassoc]
theorem arrangementRepresentedTopAugmentation_generator (c : C)
    (d : NormalizedCell A n) (f : c ⟶ (⟨n,d⟩ : C)) :
    (Cellular.vectorCopowerInclusion ℂ ((Q).obj ⟨n,d⟩)
        ((Cellular.representable ℂ c).obj ⟨n,d⟩) (ModuleCat.freeMk f) ≫
      arrangementCellularCochainInclusion A ℂ
        (Cellular.covariantCopowerDiagram ℂ Q (Cellular.representable ℂ c)) n d) ▷
        (R).obj c ≫
      singleAugmentationComponent
        (arrangementRepresentedTopAugmentation fan nonempty regular basis rays c) =
    (Q).obj ⟨n,d⟩ ◁ (R).map f ≫
      (diagonalPulledInverseCoefficientIso fan nonempty regular basis rays).inv.app ⟨n,d⟩ ≫
        (P).map (diagonalInverseCellTopQuotient fan nonempty regular basis rays d) := by
  have component : singleAugmentationComponent
      (dualDiagonalPulledTopAugmentation fan nonempty regular basis rays) =
      (P).map (dualDiagonalTopQuotient fan nonempty regular basis rays) := by
    simp only [singleAugmentationComponent, dualDiagonalPulledTopAugmentation,
      HomologicalComplex.mkHomToSingle_f, Category.assoc,
      Iso.inv_hom_id, Category.comp_id]
  change _ ≫ singleAugmentationComponent
    (cellularRepresentedTensorEvaluation A ℂ Q R c ≫
      (diagonalPulledCellularComplexIso fan nonempty regular basis rays).inv ≫
        dualDiagonalPulledTopAugmentation fan nonempty regular basis rays) = _
  rw [singleAugmentationComponent_comp, singleAugmentationComponent_comp,
    component, cellularRepresentedTensorEvaluation_generator_assoc,
    diagonalPulledCellularComplexIso_inverse_inclusion_assoc,
    ← Functor.map_comp]
  rfl

end ToricPower

end
