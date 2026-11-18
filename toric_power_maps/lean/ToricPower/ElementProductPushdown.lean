module

public import ToricPower.ElementPushdownAdjunction

/-!
# Product direct image for a genuine discrete covering

When every incidence bijects the fibers, a coefficient diagram has a
product direct image as well as its coproduct direct image. Each target
sheet follows its unique incoming lift. The construction retains all
sheets, including infinite fibers.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor

namespace ToricPower.ElementProduct

universe u v

variable {C : Type} [SmallCategory C] (B : C ⥤ Type)
  (bijective : ∀ {c d : C} (f : c ⟶ d), Function.Bijective (B.map f))
  {D : Type u} [Category.{v} D] [HasProducts.{0} D]

def mapEquiv {c d : C} (f : c ⟶ d) : B.obj c ≃ B.obj d :=
  Equiv.ofBijective (B.map f) (bijective f)

def incomingLift {c d : C} (f : c ⟶ d) (t : B.obj d) :
    B.elementsMk c ((mapEquiv B bijective f).symm t) ⟶ B.elementsMk d t :=
  ⟨f,(mapEquiv B bijective f).apply_symm_apply t⟩

def cell (E : B.Elements ⥤ D) (c : C) : D :=
  ∏ᶜ (fun r : B.obj c => E.obj (B.elementsMk c r))

def projection (E : B.Elements ⥤ D) (c : C) (r : B.obj c) :
    cell B E c ⟶ E.obj (B.elementsMk c r) :=
  Pi.π (fun t : B.obj c => E.obj (B.elementsMk c t)) r

theorem projection_transport (E : B.Elements ⥤ D) (c : C)
    (r t : B.obj c) (h : r = t) :
    projection B E c r ≫ E.map (eqToHom (congrArg (B.elementsMk c) h)) =
      projection B E c t := by
  subst t
  rw [eqToHom_refl,E.map_id,Category.comp_id]

def map (E : B.Elements ⥤ D) {c d : C} (f : c ⟶ d) : cell B E c ⟶ cell B E d :=
  Pi.lift (fun t => projection B E c ((mapEquiv B bijective f).symm t) ≫
    E.map (incomingLift B bijective f t))

@[reassoc]
theorem map_projection (E : B.Elements ⥤ D) {c d : C}
    (f : c ⟶ d) (t : B.obj d) :
    map B bijective E f ≫ projection B E d t =
      projection B E c ((mapEquiv B bijective f).symm t) ≫
        E.map (incomingLift B bijective f t) :=
  Pi.lift_comp_π _ _

/-- Every actual lifted arrow determines the corresponding projection
formula, including its literal endpoint transport. -/
@[reassoc]
theorem map_projection_lifted (E : B.Elements ⥤ D)
    {c d : B.Elements} (f : c ⟶ d) :
    map B bijective E f.hom ≫ projection B E d.obj d.val =
      projection B E c.obj c.val ≫ E.map f := by
  have inverse : (mapEquiv B bijective f.hom).symm d.val = c.val :=
    (mapEquiv B bijective f.hom).injective
      (((mapEquiv B bijective f.hom).apply_symm_apply d.val).trans f.map_val.symm)
  let h : B.elementsMk c.obj ((mapEquiv B bijective f.hom).symm d.val) = c :=
    congrArg (B.elementsMk c.obj) inverse
  have lifted : incomingLift B bijective f.hom d.val = eqToHom h ≫ f := by
    apply (Elements.π B).map_injective
    rw [Functor.map_comp]
    change f.hom = (Elements.π B).map (eqToHom h) ≫ f.hom
    rw [eqToHom_map]
    simp
  rw [map_projection,lifted,E.map_comp,← Category.assoc]
  rw [projection_transport B E c.obj _ _ inverse]

theorem map_id (E : B.Elements ⥤ D) (c : C) :
    map B bijective E (𝟙 c) = 𝟙 (cell B E c) := by
  apply Pi.hom_ext
  intro r
  have h := map_projection_lifted B bijective E (𝟙 (B.elementsMk c r))
  change map B bijective E (𝟙 c) ≫ projection B E c r =
    𝟙 (cell B E c) ≫ projection B E c r
  simpa only [Elements.id_hom,E.map_id,Category.comp_id,Category.id_comp] using h

theorem map_comp (E : B.Elements ⥤ D) {c d e : C}
    (f : c ⟶ d) (g : d ⟶ e) :
    map B bijective E (f ≫ g) = map B bijective E f ≫ map B bijective E g := by
  apply Pi.hom_ext
  intro t
  let e' := B.elementsMk e t
  let d' := B.elementsMk d ((mapEquiv B bijective g).symm t)
  let c' := B.elementsMk c ((mapEquiv B bijective f).symm d'.val)
  let f' : c' ⟶ d' := incomingLift B bijective f d'.val
  let g' : d' ⟶ e' := incomingLift B bijective g t
  change map B bijective E (f ≫ g) ≫ projection B E e t =
    (map B bijective E f ≫ map B bijective E g) ≫ projection B E e t
  calc
    _ = projection B E c'.obj c'.val ≫ E.map (f' ≫ g') :=
      map_projection_lifted B bijective E (f' ≫ g')
    _ = projection B E c'.obj c'.val ≫ E.map f' ≫ E.map g' := by
      rw [E.map_comp]
    _ = map B bijective E f ≫ projection B E d'.obj d'.val ≫ E.map g' := by
      rw [← Category.assoc,← map_projection_lifted B bijective E f',Category.assoc]
      rfl
    _ = _ := by
      rw [← map_projection_lifted B bijective E g',Category.assoc]
      rfl

def obj (E : B.Elements ⥤ D) : C ⥤ D where
  obj := cell B E
  map := map B bijective E
  map_id := map_id B bijective E
  map_comp := map_comp B bijective E

def cellMap {E F : B.Elements ⥤ D} (α : E ⟶ F) (c : C) : cell B E c ⟶ cell B F c :=
  Limits.Pi.map (fun r => α.app (B.elementsMk c r))

@[reassoc]
theorem cellMap_projection {E F : B.Elements ⥤ D} (α : E ⟶ F)
    (c : C) (r : B.obj c) :
    cellMap B α c ≫ projection B F c r =
      projection B E c r ≫ α.app (B.elementsMk c r) :=
  Pi.map_π _ _

def mapNat {E F : B.Elements ⥤ D} (α : E ⟶ F) :
    obj B bijective E ⟶ obj B bijective F where
  app := cellMap B α
  naturality {c d} f := by
    apply Pi.hom_ext
    intro t
    change (map B bijective E f ≫ cellMap B α d) ≫ projection B F d t =
      (cellMap B α c ≫ map B bijective F f) ≫ projection B F d t
    simp only [Category.assoc,cellMap_projection,map_projection_assoc,map_projection,
      cellMap_projection_assoc]
    rw [α.naturality]

/-- Product direct image with every unique incoming sheet retained. -/
def functor : (B.Elements ⥤ D) ⥤ (C ⥤ D) where
  obj := obj B bijective
  map := mapNat B bijective
  map_id E := by
    apply NatTrans.ext
    funext c
    exact Limits.Pi.map_id
  map_comp {E F G} α β := by
    apply NatTrans.ext
    funext c
    change Limits.Pi.map (fun r : B.obj c => α.app (B.elementsMk c r) ≫
        β.app (B.elementsMk c r)) =
      Limits.Pi.map (fun r : B.obj c => α.app (B.elementsMk c r)) ≫
        Limits.Pi.map (fun r : B.obj c => β.app (B.elementsMk c r))
    exact (Limits.Pi.map_comp_map _ _).symm

end ToricPower.ElementProduct

end
