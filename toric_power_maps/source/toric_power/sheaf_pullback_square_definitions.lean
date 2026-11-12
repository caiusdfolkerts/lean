module

public import ToricPower.SheafRestrictionPullbackCoherence

/-!
# Local frame coherence for actual pullback squares

Pasting a source chart restriction onto a commuting scheme square gives
the same canonical pullback comparison. The statements retain all
composition and equality isomorphisms of the ordinary pullback functor.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1000000

open AlgebraicGeometry CategoryTheory MonoidalCategory
open AlgebraicGeometry.Scheme.Modules

namespace ToricPower

universe u

variable {A B C X Y : Scheme.{u}}

/-- Composition coherence in the direction convenient for pasting charts. -/
@[reassoc]
theorem pullbackComp_associative_hom (f : A ⟶ B) (g : B ⟶ C) (h : C ⟶ X)
    (M : X.Modules) :
    (pullbackComp f g).hom.app ((pullback h).obj M) ≫
      (pullbackComp (f ≫ g) h).hom.app M =
        (pullback f).map ((pullbackComp g h).hom.app M) ≫
          (pullbackComp f (g ≫ h)).hom.app M ≫ eqToHom (by simp) := by
  have associativity :=
    pullback_map_pullbackComp_hom_app_comp_pullbackComp_hom_app f g h M
  have reversed := congrArg (fun a => a ≫ eqToHom
    (show (pullback (f ≫ (g ≫ h))).obj M =
      (pullback ((f ≫ g) ≫ h)).obj M by simp)) associativity.symm
  simpa only [Category.assoc, eqToHom_trans, eqToHom_refl,
    Category.comp_id] using reversed

/-- Equality transports commute with the composition isomorphism. -/
@[reassoc]
theorem pullbackComp_map_congr (f : A ⟶ B) {a b : B ⟶ X} (e : a = b)
    (M : X.Modules) :
    (pullback f).map ((pullbackCongr e).hom.app M) ≫
      (pullbackComp f b).hom.app M =
        (pullbackComp f a).hom.app M ≫
          (pullbackCongr (congrArg (fun a => f ≫ a) e)).hom.app M := by
  subst b
  simp [pullbackCongr]

/-- Equality transport is read on each module without unfolding pullback. -/
theorem pullbackCongr_hom_app_eqToHom {f g : A ⟶ B} (e : f = g) (M : B.Modules) :
    (pullbackCongr e).hom.app M =
      eqToHom (congrArg (fun f => (pullback f).obj M) e) := by
  subst g
  simp [pullbackCongr]

/-- The canonical comparison associated to a commuting square. -/
abbrev chartPullbackSquare (f : X ⟶ Y) (a : A ⟶ X) (b : B ⟶ Y) (g : A ⟶ B)
    (square : a ≫ f = g ≫ b) :
    pullback b ⋙ pullback g ≅ pullback f ⋙ pullback a :=
  pullbackComp g b ≪≫ pullbackCongr square.symm ≪≫ (pullbackComp a f).symm

/-- The square comparison is the prescribed composite natural transformation. -/
theorem chartPullbackSquare_hom (f : X ⟶ Y) (a : A ⟶ X)
    (b : B ⟶ Y) (g : A ⟶ B) (square : a ≫ f = g ≫ b) :
    (chartPullbackSquare f a b g square).hom =
      (pullbackComp g b).hom ≫ (pullbackCongr square.symm).hom ≫
        (pullbackComp a f).inv := rfl

/-- Evaluation of the comparison at any actual module sheaf. -/
theorem chartPullbackSquare_hom_app (f : X ⟶ Y) (a : A ⟶ X)
    (b : B ⟶ Y) (g : A ⟶ B) (square : a ≫ f = g ≫ b) (M : Y.Modules) :
    (chartPullbackSquare f a b g square).hom.app M =
      (pullbackComp g b).hom.app M ≫
        (pullbackCongr square.symm).hom.app M ≫ (pullbackComp a f).inv.app M := by
  have evaluation := congrArg
    (fun mapping : pullback b ⋙ pullback g ⟶ pullback f ⋙ pullback a => mapping.app M)
    (chartPullbackSquare_hom f a b g square)
  simpa only [NatTrans.comp_app] using evaluation

end ToricPower
