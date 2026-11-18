module

public import ToricPower.QuasicoherentOpenAdjunction
public import ToricPower.CechComparison.AffineCoverExtensions

/-!
# Enough injectives in the actual quasicoherent category

On each affine chart, the proved tilde equivalence supplies an injective
embedding of the restricted quasicoherent sheaf. Exact open restriction
shows that affine direct image preserves these injectives. Their finite
product is injective, and the adjoint embeddings jointly give a monomorphism
because equality of sheaf morphisms is detected on the actual open cover.

The construction uses no derived-category equivalence and no assumed
quasicoherent injective resolution.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

namespace ToricPower

universe u

/-- The literal tilde equivalence transfers enough injectives on an affine
spectrum. This is an equivalence of the actual full subcategory `QCoh`. -/
instance quasicoherentSpecEnoughInjectives (R : CommRingCat.{u}) :
    EnoughInjectives (QCoh (Spec R)) :=
  EnoughInjectives.of_equivalence (tildeEquiv (R := R)).inverse

variable {X : Scheme.{u}} (cover : Scheme.AffineOpenCover.{u} X)

/-- Choose an actual injective presentation on each affine chart. -/
def quasicoherentChartInjectivePresentation (M : QCoh X) (i : cover.I₀) :
    InjectivePresentation ((quasicoherentRestriction (cover.f i)).obj M) :=
  Classical.choice (EnoughInjectives.presentation _)

variable [∀ i, IsAffineHom (cover.f i)]

/-- Direct image of the chosen chart injective, still in actual `QCoh X`. -/
def quasicoherentChartInjectivePushforward (M : QCoh X) (i : cover.I₀) : QCoh X :=
  (quasicoherentAffinePushforward (cover.f i)).obj
    (quasicoherentChartInjectivePresentation cover M i).J

instance quasicoherentChartInjectivePushforward_injective (M : QCoh X) (i : cover.I₀) :
    Injective (quasicoherentChartInjectivePushforward cover M i) :=
  (quasicoherentOpenAdjunction (cover.f i)).map_injective _
    (quasicoherentChartInjectivePresentation cover M i).injective

/-- The actual adjoint of the chosen chart embedding. -/
def quasicoherentChartInjectiveComponent (M : QCoh X) (i : cover.I₀) :
    M ⟶ quasicoherentChartInjectivePushforward cover M i :=
  (quasicoherentOpenAdjunction (cover.f i)).homEquiv _ _
    (quasicoherentChartInjectivePresentation cover M i).f

variable [Finite cover.I₀]

/-- The finite product of the actual affine direct images. -/
def quasicoherentCoverInjectiveObject (M : QCoh X) : QCoh X :=
  ∏ᶜ quasicoherentChartInjectivePushforward cover M

instance quasicoherentCoverInjectiveObject_injective (M : QCoh X) :
    Injective (quasicoherentCoverInjectiveObject cover M) := by
  unfold quasicoherentCoverInjectiveObject
  infer_instance

/-- The cover embedding uses the actual adjunction maps, component by component. -/
def quasicoherentCoverInjectiveEmbedding (M : QCoh X) :
    M ⟶ quasicoherentCoverInjectiveObject cover M :=
  Pi.lift (quasicoherentChartInjectiveComponent cover M)

instance quasicoherentCoverInjectiveEmbedding_mono (M : QCoh X) :
    Mono (quasicoherentCoverInjectiveEmbedding cover M) where
  right_cancellation {T} f g h := by
    apply ObjectProperty.hom_ext
    apply BondalThomsen.FiniteQuasicoherentPushforward.hom_ext_of_openCover
      cover.openCover
    intro i
    let adj := quasicoherentOpenAdjunction (cover.f i)
    let p := quasicoherentChartInjectivePresentation cover M i
    letI : Mono p.f := p.mono
    have hc : f ≫ quasicoherentChartInjectiveComponent cover M i =
        g ≫ quasicoherentChartInjectiveComponent cover M i := by
      have ht := h =≫ Pi.π (quasicoherentChartInjectivePushforward cover M) i
      simpa only [quasicoherentCoverInjectiveEmbedding, Category.assoc,
        Pi.lift_comp_π] using ht
    have hl := congrArg (adj.homEquiv _ p.J).symm hc
    have hf : (quasicoherentRestriction (cover.f i)).map f ≫ p.f =
        (quasicoherentRestriction (cover.f i)).map g ≫ p.f := by
      simpa only [quasicoherentChartInjectiveComponent, adj, p,
        Adjunction.homEquiv_naturality_left_symm, Equiv.symm_apply_apply] using hl
    exact congrArg (fun t => t.hom) ((cancel_mono p.f).mp hf)

/-- A complete actual injective presentation; its monomorphism and injectivity
are the preceding proved results. -/
def quasicoherentCoverInjectivePresentation (M : QCoh X) : InjectivePresentation M where
  J := quasicoherentCoverInjectiveObject cover M
  injective := inferInstance
  f := quasicoherentCoverInjectiveEmbedding cover M
  mono := inferInstance

include cover in
/-- Every quasicoherent sheaf has an injective embedding when an actual finite
affine cover with affine chart maps is given. -/
theorem quasicoherentEnoughInjectivesOfFiniteAffineCover : EnoughInjectives (QCoh X) where
  presentation M := ⟨quasicoherentCoverInjectivePresentation cover M⟩

/-- A quasicompact separated scheme has enough injectives in its actual
quasicoherent category. No Noetherian hypothesis is needed for this assertion. -/
instance quasicoherentEnoughInjectives (X : Scheme.{u}) [CompactSpace X] [X.IsSeparated] :
    EnoughInjectives (QCoh X) := by
  let cover := BondalThomsen.FiniteAffineCoverQuasicoherentExtensions.finiteAffineOpenCover X
  letI (i : cover.I₀) : IsAffineHom (cover.f i) :=
    BondalThomsen.QuasicoherentFlasqueTowerConstruction.affineSource_isAffineHom (cover.f i)
  exact quasicoherentEnoughInjectivesOfFiniteAffineCover cover

end ToricPower

end
