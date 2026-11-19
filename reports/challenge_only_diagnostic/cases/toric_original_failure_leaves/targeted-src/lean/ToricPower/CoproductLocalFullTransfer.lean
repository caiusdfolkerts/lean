module

public import Mathlib.CategoryTheory.Limits.Shapes.Products
public import Mathlib.CategoryTheory.EssentialImage

/-!
# Transporting an actual coproduct through local Hom bijections

A functor need not be fully faithful everywhere to preserve a particular
coproduct. It suffices that it is essentially surjective and induces
bijections on maps out of that coproduct and out of each summand.
This is the form needed for localization on K-projective complexes.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits

namespace ToricPower

universe u v u' v' w
variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]
  {I : Type w} {family : I → C}
  (F : C ⥤ D) [F.EssSurj] (cofan : Cofan family) (colimit : IsColimit cofan)
  (pointBijective : ∀ Y : C, Function.Bijective (F.map : (cofan.pt ⟶ Y) → _))
  (summandBijective : ∀ (i : I) (Y : C), Function.Bijective
    (F.map : (family i ⟶ Y) → _))

def imageCofan : Cofan (fun i => F.obj (family i)) :=
  Cofan.mk (F.obj cofan.pt) (fun i => F.map (cofan.inj i))

include colimit pointBijective summandBijective

theorem imageCofan_hom_ext {Y : D} {f g : F.obj cofan.pt ⟶ Y}
    (same : ∀ i, F.map (cofan.inj i) ≫ f = F.map (cofan.inj i) ≫ g) : f = g := by
  let Z := F.objPreimage Y
  let e : F.obj Z ≅ Y := F.objObjPreimageIso Y
  obtain ⟨f', hf⟩ := (pointBijective Z).surjective (f ≫ e.inv)
  obtain ⟨g', hg⟩ := (pointBijective Z).surjective (g ≫ e.inv)
  apply (cancel_mono e.inv).mp
  rw [← hf, ← hg]
  congr 1
  apply colimit.hom_ext
  rintro ⟨i⟩
  apply (summandBijective i Z).injective
  simpa only [CategoryTheory.Functor.map_comp, hf, hg, ← Category.assoc, Cofan.inj]
    using congrArg (fun h => h ≫ e.inv) (same i)

theorem imageCofan_exists_desc (target : Cofan (fun i => F.obj (family i))) :
    ∃ (desc : F.obj cofan.pt ⟶ target.pt),
      ∀ i, F.map (cofan.inj i) ≫ desc = target.inj i := by
  let Z := F.objPreimage target.pt
  let e : F.obj Z ≅ target.pt := F.objObjPreimageIso target.pt
  have liftExists (i : I) : ∃ f : family i ⟶ Z, F.map f = target.inj i ≫ e.inv :=
    (summandBijective i Z).surjective _
  choose maps equations using liftExists
  let source : Cofan family := Cofan.mk Z maps
  let desc := colimit.desc source
  refine ⟨F.map desc ≫ e.hom, fun i => ?_⟩
  rw [← Category.assoc, ← CategoryTheory.Functor.map_comp]
  rw [show cofan.inj i ≫ desc = maps i from colimit.fac source ⟨i⟩, equations,
    Category.assoc, e.inv_hom_id, Category.comp_id]

/-- The mapped actual cofan is colimiting under the explicit local
Hom-bijection hypotheses. -/
def isColimitImageCofan : IsColimit (imageCofan F cofan) := by
  have existsDesc := imageCofan_exists_desc F cofan colimit pointBijective summandBijective
  choose desc equations using existsDesc
  refine Cofan.IsColimit.mk _ desc equations (fun target m same => ?_)
  apply imageCofan_hom_ext F cofan colimit pointBijective summandBijective
  intro i
  exact (same i).trans (equations target i).symm

end ToricPower

end

