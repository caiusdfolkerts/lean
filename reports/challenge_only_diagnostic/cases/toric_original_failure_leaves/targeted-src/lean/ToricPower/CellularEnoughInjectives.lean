module

public import ToricPower.CellularPointSerre
public import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic

/-!
# Enough injectives for actual vector-space incidence diagrams

The embedding is the product of the genuine evaluation--coinduction
units. Its component indexed by an object, evaluated at that object's
identity, recovers the original vector. Neither the diagram category
nor the vector spaces are assumed finite.
-/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits

namespace ToricPower.Cellular

universe u
variable (k : Type u) [Field k] {C : Type u} [Category.{u} C]

def diagramInjectiveFamily (F : C ⥤ ModuleCat.{u} k) (c : C) : C ⥤ ModuleCat.{u} k :=
  pointCoinduced k c (F.obj c)

instance diagramInjectiveFamily_injective (F : C ⥤ ModuleCat.{u} k) (c : C) :
    Injective (diagramInjectiveFamily k F c) := by
  letI : Injective (F.obj c) := vectorSpace_injective k _
  exact pointCoinduced_injective k c (F.obj c)

def diagramInjectiveEmbedding (F : C ⥤ ModuleCat.{u} k) :
    F ⟶ ∏ᶜ diagramInjectiveFamily k F :=
  Pi.lift fun c => (pointCoinducedUnit k c).app F

theorem diagramInjectiveEmbedding_π (F : C ⥤ ModuleCat.{u} k) (c : C) :
    diagramInjectiveEmbedding k F ≫ Pi.π (diagramInjectiveFamily k F) c =
      (pointCoinducedUnit k c).app F := by
  exact Pi.lift_comp_π _ _

instance diagramInjectiveEmbedding_mono (F : C ⥤ ModuleCat.{u} k) :
    Mono (diagramInjectiveEmbedding k F) := by
  rw [NatTrans.mono_iff_mono_app]
  intro c
  rw [ModuleCat.mono_iff_injective]
  intro x y equal
  have h := congrArg (fun z : (∏ᶜ diagramInjectiveFamily k F).obj c =>
    (Pi.π (diagramInjectiveFamily k F) c).app c z (𝟙 c)) equal
  change (diagramInjectiveEmbedding k F ≫ Pi.π (diagramInjectiveFamily k F) c).app c x (𝟙 c) =
    (diagramInjectiveEmbedding k F ≫ Pi.π (diagramInjectiveFamily k F) c).app c y (𝟙 c) at h
  rw [diagramInjectiveEmbedding_π] at h
  change F.map (𝟙 c) x = F.map (𝟙 c) y at h
  simpa only [CategoryTheory.Functor.map_id, ModuleCat.id_apply] using h

def diagramInjectivePresentation (F : C ⥤ ModuleCat.{u} k) : InjectivePresentation F where
  J := ∏ᶜ diagramInjectiveFamily k F
  f := diagramInjectiveEmbedding k F

instance diagramEnoughInjectives : EnoughInjectives (C ⥤ ModuleCat.{u} k) where
  presentation F := ⟨diagramInjectivePresentation k F⟩

end ToricPower.Cellular

end
