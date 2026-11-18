module

public import ToricPower.ReconstructionCompletionGeometricCellular

/-! # Literal coefficient transport of the natural geometric augmentation -/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits MonoidalCategory

namespace ToricPower.IntegralArrangement

universe v
variable {n s : ℕ} (A : Fin s → Fin n → ℤ) (k : Type) [Field k]
  {B : Type v} [Category.{0} B] [Abelian B] [Linear k B]
  [MonoidalCategory B] [MonoidalPreadditive B] [MonoidalLinear k B]
  [HasCoproducts.{0} B] [HasFiniteBiproducts B]
  (Q R : IncidenceObject A ⥤ B) (J : B)
  (ε : arrangementCellularCochainComplex A k (Cellular.covariantTensorDiagram Q R) ⟶
    (HomologicalComplex.single B (.up ℕ) n).obj J)
  (H : B ⥤ IncidenceObject A ⥤ ModuleCat k)
  (e : H ≅ Cellular.unitTensorSectionFunctor k R)

local notation "Φ" => arrangementCellularRealization A k Q

/-- Transport along the specified full Hom-coefficient comparison. -/
def cellularUnitTensorAugmentationTransport :
    H ⋙ Φ ⟶ tensorLeft J ⋙ HomologicalComplex.single B (.up ℕ) n :=
  Functor.whiskerRight e.hom Φ ≫ cellularUnitTensorAugmentation A k Q R J ε

/-- Transport preserves every original vector coefficient exactly. -/
@[reassoc]
theorem cellularUnitTensorAugmentationTransport_generator (E : B)
    (d : NormalizedCell A n) (h : (H.obj E).obj ⟨n,d⟩) :
    Cellular.vectorCopowerInclusion k (Q.obj ⟨n,d⟩) ((H.obj E).obj ⟨n,d⟩) h ≫
      arrangementCellularCochainInclusion A k (Cellular.covariantCopowerDiagram k Q (H.obj E)) n d ≫
      singleAugmentationComponent
        ((cellularUnitTensorAugmentationTransport A k Q R J ε H e).app E) =
      (ρ_ (Q.obj ⟨n,d⟩)).inv ≫ Q.obj ⟨n,d⟩ ◁ ((e.hom.app E).app ⟨n,d⟩ h) ≫
        (α_ (Q.obj ⟨n,d⟩) (R.obj ⟨n,d⟩) E).inv ≫
          (arrangementCellularCochainInclusion A k (Cellular.covariantTensorDiagram Q R) n d ≫
            singleAugmentationComponent ε) ▷ E := by
  change _ ≫ _ ≫ singleAugmentationComponent
    ((arrangementCellularCochainFunctor A k).map
      (Cellular.covariantCopowerMap k Q (e.hom.app E)) ≫
      cellularUnitTensorAugmentationAt A k Q R J ε E) = _
  rw [singleAugmentationComponent_comp, cellularCochainMap_inclusion_assoc]
  change _ ≫ (Cellular.vectorCopowerFunctor k (Q.obj ⟨n,d⟩)).map
    ((e.hom.app E).app ⟨n,d⟩) ≫ _ ≫ _ = _
  rw [Cellular.vectorCopowerInclusion_map_assoc]
  exact cellularUnitTensorAugmentationAt_generator A k Q R J ε E d _

end ToricPower.IntegralArrangement

end
