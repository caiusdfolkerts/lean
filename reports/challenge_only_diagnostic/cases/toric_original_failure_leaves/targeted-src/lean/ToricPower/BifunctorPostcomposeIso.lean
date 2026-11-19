module

public import Mathlib.CategoryTheory.Functor.Currying

/-! # A small natural-isomorphism adapter for coefficient diagrams -/

@[expose] public section
open CategoryTheory CategoryTheory.Functor

namespace ToricPower

variable {L A C D E : Type*} [Category* L] [Category* A] [Category* C]
  [Category* D] [Category* E]

/-- An ordinary coefficient comparison acts naturally on both variables
of a genuine bifunctor; the target retains the literal composed maps. -/
def flippedCompositePostcomposeIso (T : L ⥤ A ⥤ C)
    {F : C ⥤ E} {G : C ⥤ D} {H : D ⥤ E} (e : F ≅ G ⋙ H) :
    (T ⋙ (Functor.whiskeringRight A C E).obj F).flip ≅
      T.flip ⋙ (Functor.whiskeringRight L C D).obj G ⋙
        (Functor.whiskeringRight L D E).obj H :=
  NatIso.ofComponents
    (fun a => NatIso.ofComponents (fun l => e.app ((T.obj l).obj a))
      (fun f => e.hom.naturality ((T.map f).app a)))
    (fun f => by
      apply NatTrans.ext
      funext l
      exact e.hom.naturality ((T.obj l).map f))

end ToricPower

end
