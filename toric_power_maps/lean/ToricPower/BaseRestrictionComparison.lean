module

public import ToricPower.ElementPullbackBaseChange

/-! # Original restriction functors respect composition and natural frames -/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Functor

namespace ToricPower.ElementPushdown

variable {C D E : Type} [SmallCategory C] [SmallCategory D] [SmallCategory E]
  {A : Type*} [Category* A]

/-- The composite of actual restrictions is restriction along the
original composite of indexing functors. -/
def baseRestrictionCompIso (F : C ⥤ D) (G : D ⥤ E) :
    baseRestriction G (D := A) ⋙ baseRestriction F ≅ baseRestriction (F ⋙ G) :=
  NatIso.ofComponents (fun _ => Iso.refl _) (by
    intro M N f
    apply NatTrans.ext
    funext c
    simp [baseRestriction])

/-- A specified natural frame of indexing functors induces precisely
the corresponding frame of coefficient restrictions. -/
def baseRestrictionCongrIso {F G : C ⥤ D} (e : F ≅ G) :
    baseRestriction F (D := A) ≅ baseRestriction G :=
  NatIso.ofComponents (fun M => isoWhiskerRight e M) (by
    intro M N f
    apply NatTrans.ext
    funext c
    exact (f.naturality (e.hom.app c)).symm)

end ToricPower.ElementPushdown

end
