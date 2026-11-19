module

public import ToricPower.CoherentDerived

/-! ## Source module `ToricPower.CoherentPullback`
Original SHA256: 9531544f35015e1f72e4038aed3c61e7ff62ea1c7e539b1b1ffa60609ac78d0d.
Original sources are retained in `third_party/coherent_sources`.
-/
section CoherentSource10

/-!
# Actual pullback on coherent sheaves

The scheme-module pullback preserves local finite presentation along every
morphism of schemes. Restricting it to coherent sheaves gives the actual
coherent pullback. Along a finite morphism the ordinary pullback--pushforward
adjunction restricts to this full subcategory.

The left adjoint automatically preserves finite colimits. Preservation of
finite limits transfers from the ambient scheme-module functor under that
explicit hypothesis. Proving the ambient exactness from flatness remains a
separate geometric assertion.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

namespace TauCeti.AlgebraicGeometry.FinitelyPresentedSheaf

universe u

variable {X Y : Scheme.{u}}

/-- Ordinary pullback restricted to the full category of finitely presented
module sheaves. -/
def pullback (f : X ⟶ Y) : FinitelyPresentedSheaf Y ⥤ FinitelyPresentedSheaf X :=
  ObjectProperty.lift _ (ObjectProperty.ι _ ⋙ Scheme.Modules.pullback f)
    (fun M => Scheme.Modules.isFinitePresentation_pullback f M.obj)

@[simp]
theorem pullback_obj_underlying (f : X ⟶ Y) (M : FinitelyPresentedSheaf Y) :
    ((pullback f).obj M).obj = (Scheme.Modules.pullback f).obj M.obj := rfl

@[simp]
theorem pullback_map_underlying (f : X ⟶ Y) {M N : FinitelyPresentedSheaf Y}
    (φ : M ⟶ N) : ((pullback f).map φ).hom = (Scheme.Modules.pullback f).map φ.hom := rfl

@[simp]
theorem pullback_comp_inclusion (f : X ⟶ Y) :
    pullback f ⋙ ObjectProperty.ι (SheafOfModules.isFinitePresentation X.ringCatSheaf) =
      ObjectProperty.ι (SheafOfModules.isFinitePresentation Y.ringCatSheaf) ⋙
        Scheme.Modules.pullback f := rfl

instance (f : X ⟶ Y) : (pullback f).Additive := by
  constructor
  intro M N φ ψ
  exact ObjectProperty.hom_ext _
    ((Scheme.Modules.pullback f).map_add (f := φ.hom) (g := ψ.hom))

variable [IsLocallyNoetherian X] [IsLocallyNoetherian Y]

/-- The actual scheme pullback--pushforward adjunction restricted along the
fully faithful coherent inclusions. -/
def pullbackPushforwardAdjunction (f : X ⟶ Y) [IsFinite f] :
    pullback f ⊣ pushforward f :=
  (Scheme.Modules.pullbackPushforwardAdjunction f).restrictFullyFaithful
    (L := pullback f) (R := pushforward f)
    (SheafOfModules.isFinitePresentation Y.ringCatSheaf).fullyFaithfulι
    (SheafOfModules.isFinitePresentation X.ringCatSheaf).fullyFaithfulι
    (Iso.refl _) (Iso.refl _)

instance (f : X ⟶ Y) [IsFinite f] : (pullback f).IsLeftAdjoint :=
  (pullbackPushforwardAdjunction f).isLeftAdjoint

instance (f : X ⟶ Y) [IsFinite f] : PreservesFiniteColimits (pullback f) := by
  infer_instance

/-- Exactness of the ambient scheme-module pullback restricts to coherent
sheaves because their inclusion computes kernels and reflects limits. -/
instance (f : X ⟶ Y) [PreservesFiniteLimits (Scheme.Modules.pullback f)] :
    PreservesFiniteLimits (pullback f) := by
  let F := pullback f
  let I := (SheafOfModules.isFinitePresentation X.ringCatSheaf).ι
  have hFI : PreservesFiniteLimits (F ⋙ I) := by
    change PreservesFiniteLimits
      ((SheafOfModules.isFinitePresentation Y.ringCatSheaf).ι ⋙ Scheme.Modules.pullback f)
    infer_instance
  letI := hFI
  exact preservesFiniteLimits_of_reflects_of_preserves F I

/-- Forgetting the coherent wrapper recovers the ordinary adjunction unit. -/
@[simp]
theorem pullbackPushforwardAdjunction_unit_underlying
    (f : X ⟶ Y) [IsFinite f] (M : FinitelyPresentedSheaf Y) :
    ((pullbackPushforwardAdjunction f).unit.app M).hom =
      (Scheme.Modules.pullbackPushforwardAdjunction f).unit.app M.obj := by
  have h :=
    (Scheme.Modules.pullbackPushforwardAdjunction f).map_restrictFullyFaithful_unit_app
      (L := pullback f) (R := pushforward f)
      (SheafOfModules.isFinitePresentation Y.ringCatSheaf).fullyFaithfulι
      (SheafOfModules.isFinitePresentation X.ringCatSheaf).fullyFaithfulι
      (Iso.refl _) (Iso.refl _) M
  refine h.trans ?_
  change (Scheme.Modules.pullbackPushforwardAdjunction f).unit.app M.obj ≫
      (Scheme.Modules.pushforward f).map (𝟙 ((Scheme.Modules.pullback f).obj M.obj)) ≫
      𝟙 ((Scheme.Modules.pushforward f).obj ((Scheme.Modules.pullback f).obj M.obj)) = _
  rw [CategoryTheory.Functor.map_id, Category.comp_id]
  exact Category.comp_id _

/-- Restrict an actual natural module-sheaf projection to coherent objects. -/
def unitProjection (f : X ⟶ Y) [IsFinite f]
    (ρ : Scheme.Modules.pullback f ⋙ Scheme.Modules.pushforward f ⟶ 𝟭 Y.Modules) :
    pullback f ⋙ pushforward f ⟶ 𝟭 (FinitelyPresentedSheaf Y) where
  app M := ObjectProperty.homMk (ρ.app M.obj)
  naturality _ _ φ := ObjectProperty.hom_ext _ (ρ.naturality φ.hom)

/-- The coherent unit and projection satisfy the same splitting equation
as the actual scheme-module unit and projection. -/
theorem unitProjection_retract (f : X ⟶ Y) [IsFinite f]
    (ρ : Scheme.Modules.pullback f ⋙ Scheme.Modules.pushforward f ⟶ 𝟭 Y.Modules)
    (hρ : (Scheme.Modules.pullbackPushforwardAdjunction f).unit ≫ ρ = 𝟙 (𝟭 Y.Modules)) :
    (pullbackPushforwardAdjunction f).unit ≫ unitProjection f ρ =
      𝟙 (𝟭 (FinitelyPresentedSheaf Y)) := by
  apply NatTrans.ext
  funext M
  apply ObjectProperty.hom_ext _
  change ((pullbackPushforwardAdjunction f).unit.app M).hom ≫ ρ.app M.obj = 𝟙 M.obj
  rw [pullbackPushforwardAdjunction_unit_underlying]
  exact NatTrans.congr_app hρ M.obj

end TauCeti.AlgebraicGeometry.FinitelyPresentedSheaf


-- Close scopes implicitly ended by the original source EOF.
end
end CoherentSource10
