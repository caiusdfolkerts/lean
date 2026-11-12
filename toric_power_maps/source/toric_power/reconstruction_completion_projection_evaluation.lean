module

public import ToricPower.ReconstructionCompletionProjection
public import ToricPower.ReconstructionCompletionProjectionTensor
public import ToricPower.SchemeRestrictionTensor

/-! # The precise adjunct of affine geometric evaluation

The actual projection map carries evaluation of an inverse-twist unit
section to the tensor of its normalized adjunct. The identity retains
an arbitrary original target morphism and both actual tensor maps.
-/

@[expose] public noncomputable section

set_option quotPrecheck false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory MonoidalCategory

namespace ToricPower

universe u
variable {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]

local notation "F" => Scheme.Modules.pullback j
local notation "G" => Scheme.Modules.pushforward j
local notation "adj" => Scheme.Modules.pullbackPushforwardAdjunction j
local notation "E" => (Scheme.Modules.pushforward j).obj (𝟙_ U.Modules)

/-- The source normalization is the original pullback unit, and the
last map is the inverse of the original oplax tensor comparison. -/
theorem reconstruction_projectionFormulaMap_evaluation
    (Q R : X.Modules) (x : 𝟙_ X.Modules ⟶ R ⊗ E) :
    (ρ_ Q).inv ≫ Q ◁ x ≫ (α_ Q R E).inv ≫
        BondalThomsen.schemeProjectionFormulaMap j (Q ⊗ R) =
      (adj).homEquiv Q ((F).obj (Q ⊗ R))
        ((ρ_ ((F).obj Q)).inv ≫ ((F).obj Q) ◁
          ((Scheme.Modules.pullbackObjUnitIso j).inv ≫
            ((adj).homEquiv (𝟙_ X.Modules) ((F).obj R)).symm
              (x ≫ BondalThomsen.schemeProjectionFormulaMap j R)) ≫
          (Scheme.Modules.pullbackTensorIsoOfOpenImmersion j Q R).inv) := by
  letI : (F).Monoidal := Functor.Monoidal.ofOplaxMonoidal F
  have projection (M : X.Modules) :
      BondalThomsen.schemeProjectionFormulaMap j M = reconstructionUnitProjection adj M := by
    rw [reconstruction_projectionFormulaMap]
    simp only [reconstructionUnitProjection, tensorHom_id]
  have unit : Functor.LaxMonoidal.ε F = (Scheme.Modules.pullbackObjUnitIso j).inv := by
    rw [← Functor.Monoidal.inv_η]
    simp only [Scheme.Modules.pullback_η, IsIso.Iso.inv_hom]
  have tensor : Functor.LaxMonoidal.μ F Q R =
      (Scheme.Modules.pullbackTensorIsoOfOpenImmersion j Q R).inv := by
    rw [← Functor.Monoidal.inv_δ]
    rfl
  rw [projection, projection, ← unit, ← tensor]
  exact reconstructionUnitProjection_evaluation adj Q R x

/-- The complete evaluation, including its specified top quotient,
has the original tensor-section adjunct. -/
theorem reconstruction_projectionFormulaMap_evaluation_map
    (Q R J : X.Modules) (x : 𝟙_ X.Modules ⟶ R ⊗ E)
    (β : Q ⊗ R ⟶ J) :
    (ρ_ Q).inv ≫ Q ◁ x ≫ (α_ Q R E).inv ≫ β ▷ E ≫
        BondalThomsen.schemeProjectionFormulaMap j J =
      (adj).homEquiv Q ((F).obj J)
        ((ρ_ ((F).obj Q)).inv ≫ ((F).obj Q) ◁
          ((Scheme.Modules.pullbackObjUnitIso j).inv ≫
            ((adj).homEquiv (𝟙_ X.Modules) ((F).obj R)).symm
              (x ≫ BondalThomsen.schemeProjectionFormulaMap j R)) ≫
          (Scheme.Modules.pullbackTensorIsoOfOpenImmersion j Q R).inv ≫ (F).map β) := by
  have natural : β ▷ E ≫ BondalThomsen.schemeProjectionFormulaMap j J =
      BondalThomsen.schemeProjectionFormulaMap j (Q ⊗ R) ≫ (G).map ((F).map β) :=
    schemeProjectionFormulaMap_natural j β
  rw [natural]
  rw [← Category.assoc _ _ ((G).map ((F).map β)),
    ← Category.assoc _ _ ((G).map ((F).map β)),
    ← Category.assoc _ _ ((G).map ((F).map β)),
    reconstruction_projectionFormulaMap_evaluation,
    ← Adjunction.homEquiv_naturality_right]
  all_goals simp only [Category.assoc]

end ToricPower

end
