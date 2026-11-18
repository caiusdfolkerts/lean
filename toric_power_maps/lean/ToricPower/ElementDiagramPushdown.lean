module

public import Mathlib.CategoryTheory.Elements
public import Mathlib.CategoryTheory.Limits.Shapes.Products
public import Mathlib.CategoryTheory.Limits.Preserves.FunctorCategory
public import Mathlib.Algebra.Category.ModuleCat.AB

/-!
# Actual direct image along a category of elements

The fiber at a base object is the categorical coproduct over all its
elements. Every incidence follows its unique lift. The construction is
natural in the entire coefficient diagram and is exact for module
coefficients, by the actual AB4 theorem. It applies in particular to all
sheets of the finite toric-power covering category.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor

namespace ToricPower.ElementPushdown

universe u v

variable {C : Type} [SmallCategory C] (B : C ⥤ Type)
  {D : Type u} [Category.{v} D] [HasCoproducts.{0} D]

def lift {c d : C} (f : c ⟶ d) (r : B.obj c) :
    B.elementsMk c r ⟶ B.elementsMk d (B.map f r) := ⟨f,rfl⟩

def cell (E : B.Elements ⥤ D) (c : C) : D :=
  ∐ (fun r : B.obj c => E.obj (B.elementsMk c r))

def inclusion (E : B.Elements ⥤ D) (c : C) (r : B.obj c) :
    E.obj (B.elementsMk c r) ⟶ cell B E c :=
  Limits.Sigma.ι (fun t : B.obj c => E.obj (B.elementsMk c t)) r

def map (E : B.Elements ⥤ D) {c d : C} (f : c ⟶ d) : cell B E c ⟶ cell B E d :=
  Sigma.desc (fun r => E.map (lift B f r) ≫ inclusion B E d (B.map f r))

@[reassoc]
theorem inclusion_map (E : B.Elements ⥤ D) {c d : C} (f : c ⟶ d) (r : B.obj c) :
    inclusion B E c r ≫ map B E f = E.map (lift B f r) ≫ inclusion B E d (B.map f r) :=
  Sigma.ι_desc _ _

/-- The inclusion formula with its actual endpoints, including the
transport recorded in a morphism of the category of elements. -/
@[reassoc]
theorem inclusion_map_lifted (E : B.Elements ⥤ D) {c d : B.Elements} (f : c ⟶ d) :
    inclusion B E c.obj c.val ≫ map B E f.hom = E.map f ≫ inclusion B E d.obj d.val := by
  cases c with
  | @mk c r =>
    cases d with
    | @mk d t =>
      cases f with
      | mk f h =>
        change c ⟶ d at f
        change B.map f r = t at h
        subst t
        exact inclusion_map B E f r

theorem map_id (E : B.Elements ⥤ D) (c : C) : map B E (𝟙 c) = 𝟙 (cell B E c) := by
  apply Sigma.hom_ext
  intro r
  have h := inclusion_map_lifted B E (𝟙 (B.elementsMk c r))
  change inclusion B E c r ≫ map B E (𝟙 c) =
    inclusion B E c r ≫ 𝟙 (cell B E c)
  rw [Category.comp_id]
  simpa only [Functor.Elements.id_hom, E.map_id,
    Category.id_comp, Category.comp_id] using h

theorem map_comp (E : B.Elements ⥤ D) {c d e : C} (f : c ⟶ d) (g : d ⟶ e) :
    map B E (f ≫ g) = map B E f ≫ map B E g := by
  apply Sigma.hom_ext
  intro r
  let c' := B.elementsMk c r
  let d' := B.elementsMk d (B.map f r)
  let e' := B.elementsMk e (B.map g (B.map f r))
  let f' : c' ⟶ d' := lift B f r
  let g' : d' ⟶ e' := lift B g (B.map f r)
  change inclusion B E c r ≫ map B E (f ≫ g) =
    inclusion B E c r ≫ (map B E f ≫ map B E g)
  calc
    _ = E.map (f' ≫ g') ≫ inclusion B E e'.obj e'.val :=
      inclusion_map_lifted B E (f' ≫ g')
    _ = E.map f' ≫ E.map g' ≫ inclusion B E e'.obj e'.val := by
      rw [E.map_comp, Category.assoc]
    _ = E.map f' ≫ inclusion B E d'.obj d'.val ≫ map B E g := by
      rw [← inclusion_map_lifted B E g']
      rfl
    _ = _ := by
      rw [← Category.assoc, ← inclusion_map_lifted B E f', Category.assoc]
      rfl

def obj (E : B.Elements ⥤ D) : C ⥤ D where
  obj := cell B E
  map := map B E
  map_id := map_id B E
  map_comp := map_comp B E

def cellMap {E F : B.Elements ⥤ D} (α : E ⟶ F) (c : C) : cell B E c ⟶ cell B F c :=
  Limits.Sigma.map (fun r => α.app (B.elementsMk c r))

@[reassoc]
theorem inclusion_cellMap {E F : B.Elements ⥤ D} (α : E ⟶ F) (c : C) (r : B.obj c) :
    inclusion B E c r ≫ cellMap B α c = α.app (B.elementsMk c r) ≫ inclusion B F c r :=
  Sigma.ι_map _ _

def mapNat {E F : B.Elements ⥤ D} (α : E ⟶ F) : obj B E ⟶ obj B F where
  app := cellMap B α
  naturality {c d} f := by
    apply Sigma.hom_ext
    intro r
    change inclusion B E c r ≫ (map B E f ≫ cellMap B α d) =
      inclusion B E c r ≫ (cellMap B α c ≫ map B F f)
    rw [inclusion_map_assoc, inclusion_cellMap, inclusion_cellMap_assoc,
      inclusion_map, ← Category.assoc, ← Category.assoc, α.naturality]

/-- The genuine coproduct direct image of whole diagrams. -/
def functor : (B.Elements ⥤ D) ⥤ (C ⥤ D) where
  obj := obj B
  map := mapNat B
  map_id E := by
    apply NatTrans.ext
    funext c
    exact Limits.Sigma.map_id
  map_comp {E F G} α β := by
    apply NatTrans.ext
    funext c
    change Limits.Sigma.map (fun r : B.obj c =>
      α.app (B.elementsMk c r) ≫ β.app (B.elementsMk c r)) =
        Limits.Sigma.map (fun r : B.obj c => α.app (B.elementsMk c r)) ≫
          Limits.Sigma.map (fun r : B.obj c => β.app (B.elementsMk c r))
    exact (Limits.Sigma.map_comp_map
      (fun r : B.obj c => β.app (B.elementsMk c r))
      (fun r : B.obj c => α.app (B.elementsMk c r))).symm

/-- Evaluation is exactly restriction to the complete fiber followed
by its actual categorical coproduct. -/
def fiberColimitIso (E : B.Elements ⥤ D) (c : C) :
    cell B E c ≅ colimit
      (Discrete.functor (fun r : B.obj c => B.elementsMk c r) ⋙ E) :=
  HasColimit.isoOfNatIso
    (show Discrete.functor (fun r : B.obj c => E.obj (B.elementsMk c r)) ≅
      Discrete.functor (fun r : B.obj c => B.elementsMk c r) ⋙ E from
      Discrete.natIso (fun _ => Iso.refl _))

@[reassoc]
theorem inclusion_fiberColimitIso (E : B.Elements ⥤ D) (c : C) (r : B.obj c) :
    inclusion B E c r ≫ (fiberColimitIso B E c).hom =
      colimit.ι (Discrete.functor (fun t : B.obj c => B.elementsMk c t) ⋙ E)
        (Discrete.mk r) := by
  dsimp only [fiberColimitIso, inclusion, Sigma.ι]
  rw [HasColimit.ι_isoOfNatIso_hom]
  simp

def evaluationIso (c : C) :
    functor B (D := D) ⋙ (evaluation C D).obj c ≅
      (whiskeringLeft (Discrete (B.obj c)) B.Elements D).obj
          (Discrete.functor (fun r => B.elementsMk c r)) ⋙ colim :=
  NatIso.ofComponents (fun E => fiberColimitIso B E c) (by
    intro E F α
    apply Sigma.hom_ext
    intro r
    change inclusion B E c r ≫
        (cellMap B α c ≫ (fiberColimitIso B F c).hom) =
      inclusion B E c r ≫ ((fiberColimitIso B E c).hom ≫
        colimMap (whiskerLeft
          (Discrete.functor (fun t : B.obj c => B.elementsMk c t)) α))
    rw [inclusion_cellMap_assoc, inclusion_fiberColimitIso,
      inclusion_fiberColimitIso_assoc, ι_colimMap]
    rfl)

instance modulePreservesFiniteLimits (R : Type) [CommRing R] :
    PreservesFiniteLimits (functor B (D := ModuleCat.{0} R)) :=
  preservesFiniteLimits_of_evaluation _ (fun c =>
    preservesFiniteLimits_of_natIso (evaluationIso B (D := ModuleCat.{0} R) c).symm)

instance modulePreservesFiniteColimits (R : Type) [CommRing R] :
    PreservesFiniteColimits (functor B (D := ModuleCat.{0} R)) :=
  preservesFiniteColimits_of_evaluation _ (fun c =>
    preservesFiniteColimits_of_natIso (evaluationIso B (D := ModuleCat.{0} R) c).symm)

instance moduleAdditive (R : Type) [CommRing R] :
    (functor B (D := ModuleCat.{0} R)).Additive :=
  (functor B (D := ModuleCat.{0} R)).additive_of_preserves_binary_products

end ToricPower.ElementPushdown

end
