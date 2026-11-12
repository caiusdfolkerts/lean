module

public import ToricPower.DiagonalTargetRestriction
public import ToricPower.SchemePullbackTensorFrame

/-!
# Transport of the actual product frame through the diagonal square

The canonical tensor comparisons reduce the augmentation in a product
frame to the tensor of two specified unit-source maps on the overlap.
Those maps retain the complete pullback-square and projection coherence.
Their individual section values are calculated separately.

Development source pending the pinned compiler.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory
open TauCeti.Toric ToricPower.IntegralArrangement

namespace ToricPower



variable {N : Type} {V : Type*} [AddCommGroup N] [AddCommGroup V]
  [Module ℝ V] {latticeMap : N →+ V}
  (fan : Fan latticeMap) (nonempty : Nonempty fan.cones) (regular : fan.IsRegular)
  {n s : ℕ} (basis : Module.Basis (Fin n) ℤ (N →+ ℤ)) (rays : Fin s ≃ fan.Ray)
  (σ τ : fan.cones)

local notation "A" => fanArrangementMatrix fan basis rays
local notation "chart" => diagonalProductChartι fan basis rays σ τ
local notation "overlap" => fan.affineToricChartι (σ ⊓ τ)
local notation "δ" => toricDiagonal fan
local notation "g" => Spec.map (CommRingCat.ofHom (diagonalChartToIntersection fan basis rays σ τ))

/-- The actual first factor frame after transport through the actual
diagonal square, expressed as a map into the literally restricted sheaf. -/
def diagonalRestrictedFirstFrameMap {d : ℕ} (c : NormalizedCell A d) :
    𝟙_ (fan.affineToricChart (σ ⊓ τ)).Modules ⟶
      (diagonalLeftSheaf fan nonempty regular basis rays c).restrict overlap :=
  (Scheme.Modules.pullbackObjUnitIso g).inv ≫
    (Scheme.Modules.pullback g).map
      (diagonalFirstCartierFrame fan nonempty regular basis rays σ τ c).hom ≫
    (pullbackSquareIso δ g overlap chart
      (diagonalProductChart_isPullback fan basis rays σ τ).w).hom.app
      ((Scheme.Modules.pullback (toricDiagonalFirst fan)).obj
        (diagonalLeftSheaf fan nonempty regular basis rays c)) ≫
    (Scheme.Modules.pullback overlap).map
      ((diagonalFirstPullbackIso fan).hom.app
        (diagonalLeftSheaf fan nonempty regular basis rays c)) ≫
    (Scheme.Modules.restrictFunctorIsoPullback overlap).inv.app
      (diagonalLeftSheaf fan nonempty regular basis rays c)

/-- The actual second factor frame, with the corresponding second
projection and second cone chart. -/
def diagonalRestrictedSecondFrameMap {d : ℕ} (c : NormalizedCell A d) :
    𝟙_ (fan.affineToricChart (σ ⊓ τ)).Modules ⟶
      (diagonalRightSheaf fan nonempty regular basis rays c).restrict overlap :=
  (Scheme.Modules.pullbackObjUnitIso g).inv ≫
    (Scheme.Modules.pullback g).map
      (diagonalSecondCartierFrame fan nonempty regular basis rays σ τ c).hom ≫
    (pullbackSquareIso δ g overlap chart
      (diagonalProductChart_isPullback fan basis rays σ τ).w).hom.app
      ((Scheme.Modules.pullback (toricDiagonalSecond fan)).obj
        (diagonalRightSheaf fan nonempty regular basis rays c)) ≫
    (Scheme.Modules.pullback overlap).map
      ((diagonalSecondPullbackIso fan).hom.app
        (diagonalRightSheaf fan nonempty regular basis rays c)) ≫
    (Scheme.Modules.restrictFunctorIsoPullback overlap).inv.app
      (diagonalRightSheaf fan nonempty regular basis rays c)

/-- The actual product frame in the chart adjunct reduces to the
literal tensor of the two actual restricted factor-frame maps. -/
@[reassoc]
theorem diagonalProductFrame_local_tensor {d : ℕ} (c : NormalizedCell A d) :
    (Scheme.Modules.pullbackObjUnitIso g).inv ≫
        (Scheme.Modules.pullback g).map
          (diagonalProductCartierFrame fan nonempty regular basis rays σ τ c).hom ≫
        (pullbackSquareIso δ g overlap chart
          (diagonalProductChart_isPullback fan basis rays σ τ).w).hom.app
          (diagonalProductSheaf fan nonempty regular basis rays c) ≫
        (Scheme.Modules.restrictFunctorIsoPullback overlap).inv.app
          ((Scheme.Modules.pullback δ).obj
            (diagonalProductSheaf fan nonempty regular basis rays c)) ≫
        (Scheme.Modules.restrictFunctor overlap).map
          (diagonalPullbackProductMap fan nonempty regular basis rays c) =
      (λ_ (𝟙_ (fan.affineToricChart (σ ⊓ τ)).Modules)).inv ≫
        (diagonalRestrictedFirstFrameMap fan nonempty regular basis rays σ τ c ⊗ₘ
          diagonalRestrictedSecondFrameMap fan nonempty regular basis rays σ τ c) ≫
        Functor.LaxMonoidal.μ (Scheme.Modules.restrictFunctor overlap)
          (diagonalLeftSheaf fan nonempty regular basis rays c)
          (diagonalRightSheaf fan nonempty regular basis rays c) := by
  exact pullbackSquareTensorFrame_map δ g overlap chart
    (M := (Scheme.Modules.pullback (toricDiagonalFirst fan)).obj
      (diagonalLeftSheaf fan nonempty regular basis rays c))
    (N := (Scheme.Modules.pullback (toricDiagonalSecond fan)).obj
      (diagonalRightSheaf fan nonempty regular basis rays c))
    (P := diagonalLeftSheaf fan nonempty regular basis rays c)
    (Q := diagonalRightSheaf fan nonempty regular basis rays c)
    (diagonalProductChart_isPullback fan basis rays σ τ).w
    (diagonalFirstCartierFrame fan nonempty regular basis rays σ τ c)
    (diagonalSecondCartierFrame fan nonempty regular basis rays σ τ c)
    ((diagonalFirstPullbackIso fan).hom.app
      (diagonalLeftSheaf fan nonempty regular basis rays c))
    ((diagonalSecondPullbackIso fan).hom.app
      (diagonalRightSheaf fan nonempty regular basis rays c))

/-- The actual local adjoint of one product-frame column of the global
augmentation. Its source is the actual pullback of the chart unit sheaf. -/
def diagonalChartFrameAdjunct {d : ℕ} (c : NormalizedCell A d) :
    (Scheme.Modules.pullback g).obj
        (SheafOfModules.unit
          (Spec (.of (DiagonalChartRing ℂ A
            (fanConeRaySet fan rays σ) (fanConeRaySet fan rays τ)))).ringCatSheaf) ⟶
      𝟙_ (fan.affineToricChart (σ ⊓ τ)).Modules :=
  (Scheme.Modules.pullback g).map
      (diagonalProductCartierFrame fan nonempty regular basis rays σ τ c).hom ≫
    (pullbackSquareIso δ g overlap chart
      (diagonalProductChart_isPullback fan basis rays σ τ).w).hom.app
      (diagonalProductSheaf fan nonempty regular basis rays c) ≫
    (Scheme.Modules.restrictFunctorIsoPullback overlap).inv.app
      ((Scheme.Modules.pullback δ).obj
        (diagonalProductSheaf fan nonempty regular basis rays c)) ≫
    (Scheme.Modules.restrictFunctor overlap).map
      (diagonalPullbackProductMap fan nonempty regular basis rays c ≫
        diagonalTensorToStructure fan nonempty regular basis rays c) ≫
    (Scheme.Modules.restrictUnitIso overlap).hom

/-- After the canonical unit normalization, the local adjunct is
literal tensor multiplication of the two restricted factor-frame maps. -/
@[reassoc]
theorem diagonalChartFrameAdjunct_normalized {d : ℕ} (c : NormalizedCell A d) :
    (Scheme.Modules.pullbackObjUnitIso g).inv ≫
        diagonalChartFrameAdjunct fan nonempty regular basis rays σ τ c =
      (λ_ (𝟙_ (fan.affineToricChart (σ ⊓ τ)).Modules)).inv ≫
        (diagonalRestrictedFirstFrameMap fan nonempty regular basis rays σ τ c ⊗ₘ
          diagonalRestrictedSecondFrameMap fan nonempty regular basis rays σ τ c) ≫
        Functor.LaxMonoidal.μ (Scheme.Modules.restrictFunctor overlap)
          (diagonalLeftSheaf fan nonempty regular basis rays c)
          (diagonalRightSheaf fan nonempty regular basis rays c) ≫
        (Scheme.Modules.restrictFunctor overlap).map
          (diagonalTensorToStructure fan nonempty regular basis rays c) ≫
        (Scheme.Modules.restrictUnitIso overlap).hom := by
  unfold diagonalChartFrameAdjunct
  simp only [Functor.map_comp, Category.assoc]
  rw [diagonalProductFrame_local_tensor_assoc]

/-- The actual chart-frame column is the adjunct of the specified map
above, by naturality of the actual scheme adjunction. -/
@[reassoc]
theorem diagonalProductAugmentation_chart_frame_adjunct {d : ℕ}
    (c : NormalizedCell A d) :
    (diagonalProductCartierFrame fan nonempty regular basis rays σ τ c).hom ≫
        (Scheme.Modules.pullback chart).map
          (diagonalProductAugmentation fan nonempty regular basis rays c) ≫
        (diagonalStructureChartIso fan basis rays σ τ).hom =
      (Scheme.Modules.pullbackPushforwardAdjunction g).homEquiv _ _
        (diagonalChartFrameAdjunct fan nonempty regular basis rays σ τ c) := by
  rw [diagonalProductAugmentation_chart_adjunct]
  exact ((Scheme.Modules.pullbackPushforwardAdjunction g).homEquiv_naturality_left
    (diagonalProductCartierFrame fan nonempty regular basis rays σ τ c).hom _).symm

end ToricPower

end
