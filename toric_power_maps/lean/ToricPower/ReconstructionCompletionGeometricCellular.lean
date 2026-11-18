module

public import ToricPower.ReconstructionCompletionGeometricCoefficients
public import ToricPower.ArrangementCellularInclusions
public import ToricPower.SingleAugmentationComparison

/-!
# The geometric augmentation of the actual cellular functor

An augmentation of the tensor-labelled cellular complex induces a
natural augmentation on inverse-twist section coefficients. The proof
retains the original cellular differential, the original unit-source
section, and the given top quotient.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite

namespace ToricPower.IntegralArrangement

universe v

variable {n s : ℕ} (A : Fin s → Fin n → ℤ) (k : Type) [Field k]
  {B : Type v} [Category.{0} B] [Abelian B] [Linear k B]
  [MonoidalCategory B] [MonoidalPreadditive B] [MonoidalLinear k B]
  [HasCoproducts.{0} B] [HasFiniteBiproducts B]

local instance reconstructionCellularCellsFintype (q : ℕ) :
    Fintype (NormalizedCell A q) := Fintype.ofFinite _
local instance reconstructionCellularOppositeBiproducts : HasFiniteBiproducts Bᵒᵖ :=
  HasFiniteBiproducts.of_hasFiniteProducts

/-- Literal cellular inclusions jointly detect maps from a cochain term. -/
theorem reconstruction_cellular_hom_ext (P : IncidenceObject A ⥤ B)
    (q : ℕ) {E : B} {f g : (arrangementCellularCochainComplex A k P).X q ⟶ E}
    (same : ∀ d : NormalizedCell A q,
      arrangementCellularCochainInclusion A k P q d ≫ f =
        arrangementCellularCochainInclusion A k P q d ≫ g) : f = g := by
  apply Quiver.Hom.op_inj
  apply biproduct.hom_ext
  intro d
  exact congrArg Quiver.Hom.op (same d)

variable (Q R : IncidenceObject A ⥤ B)
  (J : B)
  (ε : arrangementCellularCochainComplex A k (Cellular.covariantTensorDiagram Q R) ⟶
    (HomologicalComplex.single B (.up ℕ) n).obj J)

local notation "T" => Cellular.covariantTensorDiagram Q R
local notation "Φ" => arrangementCellularRealization A k Q

/-- The actual geometric augmentation on an arbitrary coefficient object. -/
def cellularUnitTensorAugmentationAt (E : B) :
    (Φ).obj (Cellular.unitTensorSectionDiagram k R E) ⟶
      (HomologicalComplex.single B (.up ℕ) n).obj (J ⊗ E) :=
  (arrangementCellularCochainFunctor A k).map
      (Cellular.unitTensorEvaluationDiagram k Q R E) ≫
    (cellularCoefficientComplexIso A k (tensorRight E) T).inv ≫
      ((tensorRight E).mapHomologicalComplex (.up ℕ)).map ε ≫
        (HomologicalComplex.singleMapHomologicalComplex (tensorRight E) (.up ℕ) n).hom.app J

/-- Evaluation on every genuine cellular coefficient has its literal
section and its literal top quotient. -/
@[reassoc]
theorem cellularUnitTensorAugmentationAt_generator (E : B)
    (d : NormalizedCell A n) (x : 𝟙_ B ⟶ R.obj ⟨n,d⟩ ⊗ E) :
    Cellular.vectorCopowerInclusion k (Q.obj ⟨n,d⟩)
        ((Cellular.unitTensorSectionDiagram k R E).obj ⟨n,d⟩) x ≫
      arrangementCellularCochainInclusion A k
        (Cellular.covariantCopowerDiagram k Q (Cellular.unitTensorSectionDiagram k R E)) n d ≫
      singleAugmentationComponent (cellularUnitTensorAugmentationAt A k Q R J ε E) =
    (ρ_ (Q.obj ⟨n,d⟩)).inv ≫ (Q.obj ⟨n,d⟩) ◁ x ≫
      (α_ (Q.obj ⟨n,d⟩) (R.obj ⟨n,d⟩) E).inv ≫
        (arrangementCellularCochainInclusion A k T n d ≫
          singleAugmentationComponent ε) ▷ E := by
  unfold cellularUnitTensorAugmentationAt
  rw [singleAugmentationComponent_comp, singleAugmentationComponent_comp,
    singleAugmentationComponent_map, cellularCochainMap_inclusion_assoc]
  change Cellular.vectorCopowerInclusion k (Q.obj ⟨n,d⟩)
      (ModuleCat.of k (𝟙_ B ⟶ R.obj ⟨n,d⟩ ⊗ E)) x ≫
      Cellular.unitTensorEvaluation k (Q.obj ⟨n,d⟩) (R.obj ⟨n,d⟩) E ≫
      arrangementCellularCochainInclusion A k (T ⋙ tensorRight E) n d ≫
        (cellularCoefficientTermIso A k (tensorRight E) T n).inv ≫
          (singleAugmentationComponent ε) ▷ E = _
  rw [Cellular.unitTensorEvaluation_generator_assoc]
  have inclusion := cellularCoefficientTermIso_inclusion A k (tensorRight E) T n d
  have inverse :
      arrangementCellularCochainInclusion A k (T ⋙ tensorRight E) n d ≫
        (cellularCoefficientTermIso A k (tensorRight E) T n).inv =
      (arrangementCellularCochainInclusion A k T n d) ▷ E := by
    rw [← inclusion, Category.assoc, Iso.hom_inv_id, Category.comp_id]
    rfl
  rw [← Category.assoc _ (cellularCoefficientTermIso A k (tensorRight E) T n).inv,
    inverse, ← comp_whiskerRight]

/-- The geometric augmentation respects every coefficient morphism. -/
theorem cellularUnitTensorAugmentationAt_naturality {E E' : B} (h : E ⟶ E') :
    (Φ).map ((Cellular.unitTensorSectionFunctor k R).map h) ≫
        cellularUnitTensorAugmentationAt A k Q R J ε E' =
      cellularUnitTensorAugmentationAt A k Q R J ε E ≫
        (HomologicalComplex.single B (.up ℕ) n).map (J ◁ h) := by
  apply singleAugmentation_ext
  rw [singleAugmentationComponent_comp, singleAugmentationComponent_singleMap]
  apply reconstruction_cellular_hom_ext A k
    (Cellular.covariantCopowerDiagram k Q (Cellular.unitTensorSectionDiagram k R E)) n
  intro d
  apply Cellular.vectorCopower_hom_ext k (Q.obj ⟨n,d⟩)
    ((Cellular.unitTensorSectionDiagram k R E).obj ⟨n,d⟩)
  intro x
  change _ ≫ _ ≫ ((arrangementCellularCochainFunctor A k).map
      (Cellular.covariantCopowerMap k Q
        ((Cellular.unitTensorSectionFunctor k R).map h))).f n ≫ _ = _
  rw [cellularCochainMap_inclusion_assoc]
  change _ ≫ (Cellular.vectorCopowerFunctor k (Q.obj ⟨n,d⟩)).map
      (((Cellular.unitTensorSectionFunctor k R).map h).app ⟨n,d⟩) ≫ _ ≫ _ = _
  rw [Cellular.vectorCopowerInclusion_map_assoc]
  change (Cellular.vectorCopowerInclusion k (Q.obj ⟨n,d⟩)
      ((Cellular.unitTensorSectionDiagram k R E').obj ⟨n,d⟩)
      (x ≫ (R.obj ⟨n,d⟩) ◁ h)) ≫
    arrangementCellularCochainInclusion A k
      (Cellular.covariantCopowerDiagram k Q (Cellular.unitTensorSectionDiagram k R E')) n d ≫
    singleAugmentationComponent (cellularUnitTensorAugmentationAt A k Q R J ε E') = _
  rw [cellularUnitTensorAugmentationAt_generator,
    cellularUnitTensorAugmentationAt_generator_assoc]
  change (ρ_ (Q.obj ⟨n,d⟩)).inv ≫
      (Q.obj ⟨n,d⟩) ◁ (x ≫ (R.obj ⟨n,d⟩) ◁ h) ≫
        (α_ (Q.obj ⟨n,d⟩) (R.obj ⟨n,d⟩) E').inv ≫
          (arrangementCellularCochainInclusion A k T n d ≫
            singleAugmentationComponent ε) ▷ E' =
    (ρ_ (Q.obj ⟨n,d⟩)).inv ≫ (Q.obj ⟨n,d⟩) ◁ x ≫
      (α_ (Q.obj ⟨n,d⟩) (R.obj ⟨n,d⟩) E).inv ≫
        (arrangementCellularCochainInclusion A k T n d ≫
          singleAugmentationComponent ε) ▷ E ≫ J ◁ h
  simp only [whiskerLeft_comp, Category.assoc]
  rw [associator_inv_naturality_right_assoc, whisker_exchange]

/-- The full natural augmentation, on arbitrary module coefficients. -/
def cellularUnitTensorAugmentation :
    Cellular.unitTensorSectionFunctor k R ⋙ Φ ⟶
      tensorLeft J ⋙ HomologicalComplex.single B (.up ℕ) n where
  app E := cellularUnitTensorAugmentationAt A k Q R J ε E
  naturality {_ _} h := cellularUnitTensorAugmentationAt_naturality A k Q R J ε h

end ToricPower.IntegralArrangement

end
