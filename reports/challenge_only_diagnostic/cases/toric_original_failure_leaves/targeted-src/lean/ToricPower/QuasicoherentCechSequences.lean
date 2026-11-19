module

public import ToricPower.QuasicoherentInjectiveFlasque
public import ToricPower.CechComparison.StepNaturality

/-!
# Actual injective cokernel sequences for the natural Čech comparison

The chosen injective sequence lives in the actual quasicoherent category.
Its exact image in all module sheaves has a flasque middle term by the
proved quasicoherent-injective flasqueness theorem. Any coefficient map
extends to a morphism of these sequences; no functorial choice is assumed.
-/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 500000

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

namespace ToricPower.CechNaturality
universe u

/-- A comparison of two genuinely chosen injective cokernel sequences. -/
def injectiveCokernelComparison {C : Type*} [Category C] [Abelian C] [EnoughInjectives C]
    {M N : C} (mapping : M ⟶ N) :
    TauCeti.injectiveCokernelSequence M ⟶ TauCeti.injectiveCokernelSequence N := by
  let middle := Injective.factorThru (mapping ≫ Injective.ι N) (Injective.ι M)
  have square : Injective.ι M ≫ middle = mapping ≫ Injective.ι N :=
    Injective.comp_factorThru (mapping ≫ Injective.ι N) (Injective.ι M)
  exact
    { τ₁ := mapping
      τ₂ := middle
      τ₃ := cokernel.map (Injective.ι M) (Injective.ι N) mapping middle square
      comm₁₂ := square.symm
      comm₂₃ := (cokernel.π_desc _ _ _).symm }

@[simp]
theorem injectiveCokernelComparison_τ₁ {C : Type*} [Category C] [Abelian C]
    [EnoughInjectives C] {M N : C} (mapping : M ⟶ N) :
    (injectiveCokernelComparison mapping).τ₁ = mapping := rfl

variable {X : Scheme.{u}} [CompactSpace X] [X.IsSeparated]

/-- The exact underlying sequence of actual module sheaves. -/
abbrev quasicoherentUnderlyingInjectiveSequence (M : QCoh X) : ShortComplex X.Modules :=
  (TauCeti.injectiveCokernelSequence M).map (quasicoherentInclusion X)

theorem quasicoherentUnderlyingInjectiveSequence_shortExact (M : QCoh X) :
    (quasicoherentUnderlyingInjectiveSequence M).ShortExact :=
  (TauCeti.injectiveCokernelSequence_shortExact M).map_of_exact (quasicoherentInclusion X)

instance quasicoherentUnderlyingInjectiveSequence_first (M : QCoh X) :
    (quasicoherentUnderlyingInjectiveSequence M).X₁.IsQuasicoherent :=
  M.property

instance quasicoherentUnderlyingInjectiveSequence_middle (M : QCoh X) :
    (quasicoherentUnderlyingInjectiveSequence M).X₂.IsQuasicoherent :=
  (Injective.under M).property

instance quasicoherentUnderlyingInjectiveSequence_last (M : QCoh X) :
    (quasicoherentUnderlyingInjectiveSequence M).X₃.IsQuasicoherent :=
  (TauCeti.injectiveCokernelSequence M).X₃.property

instance quasicoherentUnderlyingInjectiveSequence_flasque [IsLocallyNoetherian X]
    (M : QCoh X) :
    (quasicoherentUnderlyingInjectiveSequence M).X₂.presheaf.IsFlasque :=
  quasicoherentInjective_isFlasque (Injective.under M)

/-- An actual module-sheaf sequence comparison above any quasicoherent map. -/
def quasicoherentUnderlyingInjectiveComparison {M N : QCoh X} (mapping : M ⟶ N) :
    quasicoherentUnderlyingInjectiveSequence M ⟶ quasicoherentUnderlyingInjectiveSequence N :=
  (quasicoherentInclusion X).mapShortComplex.map (injectiveCokernelComparison mapping)

@[simp]
theorem quasicoherentUnderlyingInjectiveComparison_τ₁ {M N : QCoh X} (mapping : M ⟶ N) :
    (quasicoherentUnderlyingInjectiveComparison mapping).τ₁ = mapping.hom := rfl

@[simp]
theorem quasicoherentUnderlyingInjectiveComparison_τ₃ {M N : QCoh X} (mapping : M ⟶ N) :
    (quasicoherentUnderlyingInjectiveComparison mapping).τ₃ =
      (injectiveCokernelComparison mapping).τ₃.hom := rfl

end ToricPower.CechNaturality
