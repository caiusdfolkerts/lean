module

public import ToricPower.SchemeProjectionNaturality
public import ToricPower.SchemeAdjunctUnitSections

/-!
# The actual projection formula as the canonical tensor map

The projection map already used in the affine unit comparison is
identified with the tensor map of actual sheaf pushforward and the
original pullback-adjunction unit. The equality is proved on the
sectionwise tensors that generate the sheaf tensor product.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000

open AlgebraicGeometry CategoryTheory MonoidalCategory Opposite
open scoped TensorProduct

namespace ToricPower

universe u

/-- The genuine right-unit constraint multiplies the original sections. -/
theorem reconstruction_rightUnitor_section {X : Scheme.{u}}
    (M : X.Modules) (U : X.Opens) (s : Γ(M,U)) (t : Γ(X,U)) :
    letI : Module (Γ(X,U)) (M.val.obj (op U)) := (M.val.obj (op U)).isModule
    Scheme.Modules.Hom.app (ρ_ M).hom U
        (schemeTensorSection M (𝟙_ X.Modules) U s t) = t • s := by
  letI : Module (Γ(X,U)) (M.val.obj (op U)) := (M.val.obj (op U)).isModule
  have actual := ConcreteCategory.congr_hom
    (Functor.LaxMonoidal.right_unitality (Scheme.Modules.sectionsFunctor U) M)
    (s ⊗ₜ[Γ(X,U)] t)
  rw [Scheme.Modules.sectionsFunctor_ε] at actual
  replace actual := actual.symm
  change Scheme.Modules.Hom.app (ρ_ M).hom U
      (schemeTensorSection M (𝟙_ X.Modules) U s t) = t • s at actual
  exact actual

variable {U X : Scheme.{u}} (j : U ⟶ X)

/-- The tensor map of actual pushforward preserves the literal tensor
of sections on the inverse-image open. -/
theorem reconstruction_pushforward_tensor_section (M N : U.Modules)
    (V : X.Opens) (s : Γ(M,j ⁻¹ᵁ V)) (t : Γ(N,j ⁻¹ᵁ V)) :
    Scheme.Modules.Hom.app (Functor.LaxMonoidal.μ (Scheme.Modules.pushforward j) M N) V
      (schemeTensorSection ((Scheme.Modules.pushforward j).obj M)
        ((Scheme.Modules.pushforward j).obj N) V s t) =
      schemeTensorSection M N (j ⁻¹ᵁ V) s t :=
  TauCeti.SheafOfModules.pushforward_μ_app_tmul j.toRingCatSheafHom M N (op V) s t

/-- The sectionwise action is the actual pushforward tensor map. -/
theorem reconstruction_projectionAction (M : X.Modules) (N : U.Modules)
    (comparison : M ⟶ (Scheme.Modules.pushforward j).obj N) :
    BondalThomsen.projectionAction j M N comparison =
      (comparison ⊗ₘ
        𝟙 ((Scheme.Modules.pushforward j).obj (𝟙_ U.Modules))) ≫
        Functor.LaxMonoidal.μ (Scheme.Modules.pushforward j) N (𝟙_ U.Modules) ≫
        (Scheme.Modules.pushforward j).map (ρ_ N).hom := by
  apply schemeTensorHom_ext
  intro V s t
  have pure := schemeProjectionAction_pureSection j M N comparison V s t
  have tensor := schemeTensorSection_naturality comparison
    (𝟙 ((Scheme.Modules.pushforward j).obj (𝟙_ U.Modules))) V s t
  change Scheme.Modules.Hom.app
      (comparison ⊗ₘ 𝟙 ((Scheme.Modules.pushforward j).obj (𝟙_ U.Modules))) V
      (schemeTensorSection M ((Scheme.Modules.pushforward j).obj (𝟙_ U.Modules)) V s t) =
    schemeTensorSection ((Scheme.Modules.pushforward j).obj N)
      ((Scheme.Modules.pushforward j).obj (𝟙_ U.Modules)) V (comparison.app V s) t at tensor
  have push := reconstruction_pushforward_tensor_section j N (𝟙_ U.Modules)
    V (comparison.app V s) t
  have unit := reconstruction_rightUnitor_section N (j ⁻¹ᵁ V) (comparison.app V s) t
  change Scheme.Modules.Hom.app ((Scheme.Modules.pushforward j).map (ρ_ N).hom) V
      (schemeTensorSection N (𝟙_ U.Modules) (j ⁻¹ᵁ V) (comparison.app V s) t) =
    BondalThomsen.projectionSectionAction j N V t (comparison.val.app (op V) s) at unit
  refine pure.trans (unit.symm.trans ?_)
  change Scheme.Modules.Hom.app ((Scheme.Modules.pushforward j).map (ρ_ N).hom) V _ =
    Scheme.Modules.Hom.app ((Scheme.Modules.pushforward j).map (ρ_ N).hom) V
      (Scheme.Modules.Hom.app (Functor.LaxMonoidal.μ (Scheme.Modules.pushforward j) N
        (𝟙_ U.Modules)) V
        (Scheme.Modules.Hom.app
          (comparison ⊗ₘ 𝟙 ((Scheme.Modules.pushforward j).obj (𝟙_ U.Modules))) V
          (schemeTensorSection M ((Scheme.Modules.pushforward j).obj (𝟙_ U.Modules)) V s t)))
  exact congrArg (Scheme.Modules.Hom.app ((Scheme.Modules.pushforward j).map (ρ_ N).hom) V)
    (push.symm.trans (congrArg
      (Scheme.Modules.Hom.app (Functor.LaxMonoidal.μ (Scheme.Modules.pushforward j) N
        (𝟙_ U.Modules)) V) tensor.symm))

/-- The original sectionwise projection formula is the original
adjunction unit followed by the canonical pushforward tensor map. -/
theorem reconstruction_projectionFormulaMap (M : X.Modules) :
    BondalThomsen.schemeProjectionFormulaMap j M =
      ((Scheme.Modules.pullbackPushforwardAdjunction j).unit.app M ⊗ₘ
        𝟙 ((Scheme.Modules.pushforward j).obj (𝟙_ U.Modules))) ≫
        Functor.LaxMonoidal.μ (Scheme.Modules.pushforward j)
          ((Scheme.Modules.pullback j).obj M) (𝟙_ U.Modules) ≫
        (Scheme.Modules.pushforward j).map (ρ_ ((Scheme.Modules.pullback j).obj M)).hom :=
  reconstruction_projectionAction j M ((Scheme.Modules.pullback j).obj M)
    ((Scheme.Modules.pullbackPushforwardAdjunction j).unit.app M)

end ToricPower

end
