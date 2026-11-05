module

public import PaperVerification.AlternatingSectionSheaf
public import PaperVerification.AlternatingSectionSpan

/-!
# Detecting the zero section by its genuine local evaluations

The exterior-power universal property and the sheafification adjunction
show that vanishing of the alternating evaluation on all local vectors
is exactly the vanishing required of the constructed sheaf morphism.
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false

open CategoryTheory
open TauCeti.SheafOfModules (ringCatSheaf)

universe u v w

namespace PaperVerification.AlternatingSectionPresheaf

variable {C : Type v} [Category.{w} C] {R : Cᵒᵖ ⥤ CommRingCat.{u}}
variable {M : PresheafOfModulesOfCommRing.{u} R}
variable {P N : Type u} [Fintype P]
variable (a b : P → N)
variable (coord : N → (M ⟶ PresheafOfModulesOfCommRing.unit R))
variable (c : P → (PresheafOfModulesOfCommRing.unit R).sections)

/-- Values on decomposable wedges detect the zero presheaf morphism. -/
theorem functional_eq_zero
    (h : ∀ (X : Cᵒᵖ) (v : Fin 2 → M.obj X), localForm a b coord c X v = 0) :
    functional a b coord c = 0 := by
  apply PresheafOfModules.hom_ext
  intro X
  apply ModuleCat.exteriorPower.hom_ext
  apply ModuleCat.AlternatingMap.ext
  intro v
  change ModuleCat.exteriorPower.desc (localForm a b coord c X)
    (ModuleCat.exteriorPower.mk v) = 0
  exact (ModuleCat.exteriorPower.desc_mk _ v).trans (h X v)

end PaperVerification.AlternatingSectionPresheaf

namespace PaperVerification.AlternatingSectionSheaf

variable {C : Type v} [Category.{w} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat RingCat.{u})]
variable [HasWeakSheafify J AddCommGrpCat.{u}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
variable {R : Sheaf J CommRingCat.{u}}
variable {M : SheafOfModules.{u} (ringCatSheaf R)}
variable {P N : Type u} [Fintype P]
variable (a b : P → N)
variable (coord : N → (M ⟶ SheafOfModules.unit (ringCatSheaf R)))
variable (c : P → (SheafOfModules.unit (ringCatSheaf R)).val.sections)

/-- The actual sheaf morphism is zero if all its original local alternating
evaluations vanish.  Sheafification introduces no additional hypothesis. -/
theorem functional_eq_zero
    (h : ∀ (X : Cᵒᵖ) (v : Fin 2 → M.val.obj X),
      AlternatingSectionPresheaf.localForm a b (fun i ↦ (coord i).val) c X v = 0) :
    functional a b coord c = 0 := by
  have hp := AlternatingSectionPresheaf.functional_eq_zero
    a b (fun i ↦ (coord i).val) c h
  unfold functional
  rw [hp, Functor.map_zero, Limits.zero_comp]

end PaperVerification.AlternatingSectionSheaf
