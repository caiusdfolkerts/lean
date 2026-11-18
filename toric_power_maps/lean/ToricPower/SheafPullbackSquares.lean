module

public import ToricPower.SheafPullbackSquareDefinitions

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

private theorem compose_square_transport {D : Type*} [Category D]
    {P Q R S T U V W : D}
    (p : P ⟶ Q) (q : Q ⟶ R) (r : R ⟶ S) (s : S ⟶ T)
    (t : Q ⟶ U) (u : U ⟶ S) (v : P ⟶ V) (w : V ⟶ W)
    (x : W ⟶ U) (y : W ⟶ T)
    (hc : q ≫ r = t ≫ u) (ha : p ≫ t = v ≫ w ≫ x)
    (ht : x ≫ u ≫ s = y) :
    p ≫ q ≫ r ≫ s = v ≫ w ≫ y := by
  calc
    _ = p ≫ (q ≫ r) ≫ s := by simp only [Category.assoc]
    _ = p ≫ (t ≫ u) ≫ s := by rw [hc]
    _ = (p ≫ t) ≫ u ≫ s := by simp only [Category.assoc]
    _ = (v ≫ w ≫ x) ≫ u ≫ s := by rw [ha]
    _ = v ≫ w ≫ (x ≫ u ≫ s) := by simp only [Category.assoc]
    _ = v ≫ w ≫ y := by rw [ht]

/-- The composition and equality transports used in pasting a square
form the expected commutative diagram. -/
private theorem square_transport_coherence (f : X ⟶ Y) (a : A ⟶ X)
    (b : B ⟶ Y) (g : A ⟶ B) (square : a ≫ f = g ≫ b)
    (c : C ⟶ A) (M : Y.Modules)
    (pasted : (c ≫ a) ≫ f = (c ≫ g) ≫ b) :
    (pullback c).map ((pullbackComp g b).hom.app M) ≫
      (pullback c).map ((pullbackCongr square.symm).hom.app M) ≫
        (pullbackComp c (a ≫ f)).hom.app M ≫
          eqToHom (congrArg (fun h => (pullback h).obj M) (Category.assoc c a f).symm) =
    (pullbackComp c g).hom.app ((pullback b).obj M) ≫
      (pullbackComp (c ≫ g) b).hom.app M ≫
        (pullbackCongr pasted.symm).hom.app M := by
  have hc := pullbackComp_map_congr c square.symm M
  have ha := pullback_map_pullbackComp_hom_app_comp_pullbackComp_hom_app c g b M
  exact compose_square_transport
    ((pullback c).map ((pullbackComp g b).hom.app M))
    ((pullback c).map ((pullbackCongr square.symm).hom.app M))
    ((pullbackComp c (a ≫ f)).hom.app M)
    (eqToHom (congrArg (fun h => (pullback h).obj M) (Category.assoc c a f).symm))
    ((pullbackComp c (g ≫ b)).hom.app M)
    ((pullbackCongr (congrArg (fun h => c ≫ h) square.symm)).hom.app M)
    ((pullbackComp c g).hom.app ((pullback b).obj M))
    ((pullbackComp (c ≫ g) b).hom.app M)
    (eqToHom (congrArg (fun h => (pullback h).obj M) (Category.assoc c g b)))
    ((pullbackCongr pasted.symm).hom.app M) hc ha
    (by simp only [pullbackCongr_hom_app_eqToHom, eqToHom_trans])


/-- A generic cancellation calculation, separated from scheme pullback
so that none of its proof steps unfolds a sheaf-valued functor. -/
private theorem map_comparison_cancel {D E : Type*} [Category D] [Category E]
    (F : D ⥤ E) {P Q R S : D} {T U : E}
    (a : P ⟶ Q) (b : Q ⟶ R) (frame : S ≅ R)
    (t : F.obj S ⟶ T) (e : T ≅ U) (p : F.obj R ⟶ U) (rhs : F.obj P ⟶ U)
    (composition : t ≫ e.hom = F.map frame.hom ≫ p)
    (coherence : F.map a ≫ F.map b ≫ p = rhs) :
    F.map (a ≫ b ≫ frame.inv) ≫ t = rhs ≫ e.inv := by
  apply (cancel_mono e.hom).mp
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id, composition,
    CategoryTheory.Functor.map_comp]
  simpa only [Category.assoc, ← CategoryTheory.Functor.map_comp_assoc,
    Iso.inv_hom_id, CategoryTheory.Functor.map_id, Category.id_comp] using coherence

/-- Pasting a further chart map onto a square respects its actual
pullback comparison. -/
theorem chartPullbackSquare_precompose (f : X ⟶ Y) (a : A ⟶ X)
    (b : B ⟶ Y) (g : A ⟶ B) (square : a ≫ f = g ≫ b)
    (c : C ⟶ A) (M : Y.Modules)
    (pasted : (c ≫ a) ≫ f = (c ≫ g) ≫ b) :
    (pullback c).map ((chartPullbackSquare f a b g square).hom.app M) ≫
      (pullbackComp c a).hom.app ((pullback f).obj M) =
        (pullbackComp c g).hom.app ((pullback b).obj M) ≫
          (chartPullbackSquare f (c ≫ a) b (c ≫ g) pasted).hom.app M := by
  have comparison := map_comparison_cancel (pullback c)
    ((pullbackComp g b).hom.app M) ((pullbackCongr square.symm).hom.app M)
    ((pullbackComp a f).app M)
    ((pullbackComp c a).hom.app ((pullback f).obj M))
    ((pullbackComp (c ≫ a) f).app M)
    ((pullbackComp c (a ≫ f)).hom.app M ≫
      eqToHom (congrArg (fun h => (pullback h).obj M) (Category.assoc c a f).symm))
    ((pullbackComp c g).hom.app ((pullback b).obj M) ≫
      (pullbackComp (c ≫ g) b).hom.app M ≫ (pullbackCongr pasted.symm).hom.app M)
    (pullbackComp_associative_hom c a f M)
    (square_transport_coherence f a b g square c M pasted)
  simpa only [chartPullbackSquare_hom_app, Iso.app_hom, Iso.app_inv,
    Category.assoc (obj := C.Modules)] using comparison

end ToricPower
