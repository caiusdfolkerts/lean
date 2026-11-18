module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
public import Mathlib.CategoryTheory.Sites.SheafHom
public import Mathlib.CategoryTheory.Sites.Subsheaf
public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.Topology.Sheaves.SheafCondition.UniqueGluing
public import Mathlib.CategoryTheory.Retract
public import ToricPower.PowerProjection
public import ToricPower.AffineSplitting

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-! # Actual power-map sheaves and their local splittings

The consolidated source retains all proof bodies and their provenance.
The global overlap identity at the sheaf level remains a separate proof
obligation; no global retraction is asserted by this module.
-/

/-! ## ToricPower/SheafDescent.lean -/

section PowerSheafSource0

/-! # Actual module-sheaf descent

This file consolidates the sheaf of linear morphisms, ordinary open base
change, and morphism gluing. Its source manifest records the original files.
No imported theorem is replaced by an assumption.
-/

/-! ## TauCeti/Algebra/Category/ModuleCat/Sheaf/Hom.lean -/

section SheafDescentSource0

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
/-!
# The sheaf of linear morphisms

For a presheaf of modules and a sheaf of modules over a sheaf of rings, local linear morphisms
from the first to the second form a sheaf of sets; only the target has to be a sheaf. This is
the gluing input for the dual sheaf: take the target to be the structure sheaf.
The construction works over any site and does not require commutativity of the rings.

Over an object `U`, a section is an additive morphism between the restrictions of the source
and the target to the slice over `U`, whose components are linear over the restricted structure
sheaf. Restriction pulls such morphisms back along arrows. Linearity is local because
equality of target sections can be checked on a covering sieve, so compatible local linear
morphisms glue uniquely.

The resulting sheaf `PresheafOfModules.linearHom` has local sections over `U` equivalent to
morphisms between the restricted presheaves of modules (`PresheafOfModules.linearHomObjEquiv`).
When the source is a sheaf as well, they are equivalent to morphisms between the restricted
module sheaves, and global sections are equivalent to morphisms of the original module sheaves.
The declarations `SheafOfModules.linearHomObjEquiv`, `SheafOfModules.linearHomSectionsEquiv`,
and `SheafOfModules.linearHomObjEquiv_map_app` expose these identifications and their behavior
under restriction. They support dot notation directly, for example `M.val.linearHom N` and
`M.linearHomObjEquiv N U`.

## Sources

The construction builds on Mathlib's `presheafHom`. Its gluing proof uses the sheaf result
`Presheaf.IsSheaf.hom` together with the subfunctor criterion `Subfunctor.isSheaf_iff`.

This file constructs the underlying sheaf of sets; it does not equip it with a module
structure or identify it with a categorical internal Hom.
-/

public section

open CategoryTheory Opposite

noncomputable section

namespace TauCeti
namespace SheafOfModules

universe u v w w'

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  {R : Sheaf J RingCat.{w}} (M : PresheafOfModules.{w'} R.obj) (N : SheafOfModules.{w'} R)

/-- The subpresheaf of additive local morphisms that commute with scalar multiplication. -/
private def linearHomSubfunctor : Subfunctor (presheafHom M.presheaf N.val.presheaf) where
  obj U := {φ | ∀ (V : Over U.unop) (r : R.obj.obj (op V.left)) (m : M.obj (op V.left)),
    φ.app (op V) (r • m) =
      (r • · : N.val.obj (op V.left) → N.val.obj (op V.left)) (φ.app (op V) m)}
  map f _ h V r m := h ((Over.map f.unop).obj V) r m

/-- Linearity of a local additive morphism can be checked on a covering sieve. -/
private theorem mem_linearHomSubfunctor_of_cover {U : Cᵒᵖ}
    (φ : (presheafHom M.presheaf N.val.presheaf).obj U)
    (S : Sieve U.unop) (hS : S ∈ J U.unop)
    (hφ : ∀ ⦃V⦄ (f : V ⟶ U.unop), S f →
      (presheafHom M.presheaf N.val.presheaf).map f.op φ ∈
        (linearHomSubfunctor M N).obj (op V)) :
    φ ∈ (linearHomSubfunctor M N).obj U := by
  dsimp only [presheafHom] at φ
  intro V r m
  have hN := (isSheaf_iff_isSheaf_of_type _ _).1
    (Presheaf.isSheaf_comp_of_isSheaf J N.val.presheaf (CategoryTheory.forget _) N.isSheaf)
  apply (hN _ (J.pullback_stable V.hom hS)).isSeparatedFor.ext
  intro W f hf
  have hlin := hφ (f ≫ V.hom) hf (Over.mk (𝟙 W))
    (R.obj.map f.op r) (M.presheaf.map f.op m)
  -- Read the restricted morphism at the identity of the slice.
  have hmap (s : M.obj (op W)) := ConcreteCategory.congr_hom
    (presheafHom_map_app_op_mk_id (F := M.presheaf) (G := N.val.presheaf)
      (f ≫ V.hom) φ) s
  have hlin' := (hmap (R.obj.map f.op r • M.presheaf.map f.op m)).symm.trans <|
    hlin.trans (congrArg (fun s : N.val.obj (op W) => R.obj.map f.op r • s)
      (hmap (M.presheaf.map f.op m)))
  -- Naturality and semilinearity identify this local equality with the restriction
  -- of the desired equality on V.
  have hnat (s : M.obj (op V.left)) :
      φ.app (op (Over.mk (f ≫ V.hom))) (M.presheaf.map f.op s) =
        N.val.presheaf.map f.op (φ.app (op V) s) :=
    congrArg (fun g => g s) (φ.naturality (Over.homMk f : Over.mk (f ≫ V.hom) ⟶ V).op)
  exact (hnat (r • m)).symm.trans <|
    (congrArg (φ.app (op (Over.mk (f ≫ V.hom))))) (M.map_smul f.op r m) |>.trans <|
      hlin'.trans <| (congrArg (fun s : N.val.obj (op W) => R.obj.map f.op r • s) (hnat m)).trans
        (N.val.map_smul f.op r (φ.app (op V) m)).symm

/-- Local linear morphisms satisfy the sheaf condition. -/
private theorem isSheaf_linearHomSubfunctor :
    Presheaf.IsSheaf J (linearHomSubfunctor M N).toFunctor := by
  rw [isSheaf_iff_isSheaf_of_type]
  apply ((linearHomSubfunctor M N).isSheaf_iff
    ((isSheaf_iff_isSheaf_of_type _ _).1 (N.isSheaf.hom M.presheaf))).2
  intro U φ hφ
  exact mem_linearHomSubfunctor_of_cover M N φ _ hφ (fun _ _ hf => hf)

end SheafOfModules
end TauCeti

namespace PresheafOfModules

universe u v w w'

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  {R : Sheaf J RingCat.{w}} (M : PresheafOfModules.{w'} R.obj) (N : SheafOfModules.{w'} R)

/-- The sheaf of sets of local linear morphisms from a presheaf of modules to a sheaf of
modules. Only the target has to be a sheaf. -/
def linearHom : Sheaf J (Type (max u v w')) where
  obj := (TauCeti.SheafOfModules.linearHomSubfunctor M N).toFunctor
  property := TauCeti.SheafOfModules.isSheaf_linearHomSubfunctor M N

/-- Convert a linear Hom section over `U` to a morphism of the restricted presheaves of
modules. -/
private def linearHomObjToFun (U : C) (φ : (M.linearHom N).obj.obj (op U)) :
    (pushforward₀ (Over.forget U) R.obj).obj M ⟶ (pushforward₀ (Over.forget U) R.obj).obj N.val :=
  homMk φ.val (fun V ↦ φ.property V.unop)

/-- Convert a morphism of restricted presheaves of modules to its underlying linear Hom
section. -/
private def linearHomObjInvFun (U : C)
    (φ : (pushforward₀ (Over.forget U) R.obj).obj M ⟶
      (pushforward₀ (Over.forget U) R.obj).obj N.val) :
    (M.linearHom N).obj.obj (op U) :=
  ⟨(toPresheaf _).map φ, fun V r m ↦ (φ.app (op V)).hom.map_smul r m⟩

/-- Sections over `U` of the sheaf of local linear morphisms from a presheaf of modules are
precisely the morphisms between the restrictions to the slice over `U`. -/
def linearHomObjEquiv (U : C) :
    (M.linearHom N).obj.obj (op U) ≃
      ((pushforward₀ (Over.forget U) R.obj).obj M ⟶
        (pushforward₀ (Over.forget U) R.obj).obj N.val) where
  toFun := linearHomObjToFun M N U
  invFun := linearHomObjInvFun M N U
  left_inv φ := by
    apply Subtype.ext
    apply NatTrans.ext
    funext V
    ext m
    rfl
  right_inv φ := by
    ext V m
    rfl

/-- Evaluate a local linear Hom section at a slice object and a source section. -/
def linearHomApp (U : C) (φ : (M.linearHom N).obj.obj (op U))
    (V : Over U) (m : M.obj (op V.left)) : N.val.obj (op V.left) :=
  φ.val.app (op V) m

-- This is not a simp lemma: `Over.forget_obj` rewrites the dependent module structure in its
-- left-hand side.
/-- The morphism associated to a local linear Hom section evaluates to the section's component. -/
theorem linearHomObjEquiv_app (U : C)
    (φ : (M.linearHom N).obj.obj (op U)) (V : Over U) (m : M.obj (op V.left)) :
    ((M.linearHomObjEquiv N U φ).app (op V)) m = M.linearHomApp N U φ V m := by
  rfl

/-- The local linear Hom section associated to a morphism evaluates to the morphism's component. -/
@[simp]
theorem linearHomObjEquiv_symm_app (U : C)
    (φ : (pushforward₀ (Over.forget U) R.obj).obj M ⟶
      (pushforward₀ (Over.forget U) R.obj).obj N.val)
    (V : Over U) (m : M.obj (op V.left)) :
    M.linearHomApp N U ((M.linearHomObjEquiv N U).symm φ) V m = (φ.app (op V)) m := by
  rfl

-- This is not a simp lemma: `Over.forget_obj` and `Over.mk_left` rewrite the slice object
-- `Over.mk g` inside the implicit arguments of the coercion on its left-hand side.
/-- Restriction of a local linear morphism restricts its component linear maps. -/
theorem linearHomObjEquiv_map_app {U V W : C} (f : V ⟶ U) (g : W ⟶ V)
    (φ : (M.linearHom N).obj.obj (op U)) (m : M.obj (op W)) :
    ((M.linearHomObjEquiv N V ((M.linearHom N).obj.map f.op φ)).app (op (Over.mk g))) m =
      ((M.linearHomObjEquiv N U φ).app (op (Over.mk (g ≫ f)))) m := by
  rw [linearHomObjEquiv_app, linearHomObjEquiv_app]
  exact ConcreteCategory.congr_hom (presheafHom_map_app g f (g ≫ f) rfl φ.val) m

end PresheafOfModules

namespace SheafOfModules

universe u v w w'

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  {R : Sheaf J RingCat.{w}} (M N : SheafOfModules.{w'} R)

/-- Sections of the linear Hom sheaf over an object are precisely morphisms between the
restricted sheaves of modules.

The lemmas `linearHomObjEquiv_app` and `linearHomObjEquiv_symm_app` give the componentwise
evaluation formulas in both directions. -/
def linearHomObjEquiv (U : C) :
    (M.val.linearHom N).obj.obj (op U) ≃ (M.over U ⟶ N.over U) :=
  (M.val.linearHomObjEquiv N U).trans
    ((fullyFaithfulForget _).homEquiv (X := M.over U) (Y := N.over U)).symm

/-- The morphism associated to a local linear Hom section evaluates to the section's component. -/
theorem linearHomObjEquiv_app (U : C)
    (φ : (M.val.linearHom N).obj.obj (op U)) (V : Over U) (m : M.val.obj (op V.left)) :
    ((linearHomObjEquiv M N U φ).val.app (op V)) m = M.val.linearHomApp N U φ V m := by
  rfl

/-- The local linear Hom section associated to a morphism evaluates to the morphism's component. -/
@[simp]
theorem linearHomObjEquiv_symm_app (U : C) (φ : M.over U ⟶ N.over U)
    (V : Over U) (m : M.val.obj (op V.left)) :
    M.val.linearHomApp N U ((linearHomObjEquiv M N U).symm φ) V m =
      (φ.val.app (op V)) m := by
  rfl

/-- Restriction of a Hom section restricts its component linear maps. -/
@[simp]
theorem linearHomObjEquiv_map_app {U V W : C} (f : V ⟶ U) (g : W ⟶ V)
    (φ : (M.val.linearHom N).obj.obj (op U)) (m : M.val.obj (op W)) :
    ((linearHomObjEquiv M N V ((M.val.linearHom N).obj.map f.op φ)).val.app
      (op (Over.mk g))) m =
        ((linearHomObjEquiv M N U φ).val.app (op (Over.mk (g ≫ f)))) m := by
  rw [linearHomObjEquiv_app, linearHomObjEquiv_app]
  exact ConcreteCategory.congr_hom (presheafHom_map_app g f (g ≫ f) rfl φ.val) m

/-- Convert a global linear Hom section to its morphism of module sheaves. -/
private def linearHomSectionsToFun (s : (M.val.linearHom N).obj.sections) : M ⟶ N :=
  ⟨PresheafOfModules.homMk
    (presheafHomSectionsEquiv M.val.presheaf N.val.presheaf
      ⟨fun U ↦ (s.val U).val, fun f ↦ congrArg Subtype.val (s.property f)⟩)
    (fun U ↦ (s.val U).property (Over.mk (𝟙 U.unop)))⟩

/-- The morphism converted from a global section evaluates at the identity slice. -/
private theorem linearHomSectionsToFun_app (s : (M.val.linearHom N).obj.sections) (U : Cᵒᵖ)
    (m : M.val.obj U) :
    ((linearHomSectionsToFun M N s).val.app U) m =
      (s.val U).val.app (op (Over.mk (𝟙 U.unop))) m := by
  rfl

/-- Global conversion agrees componentwise with the objectwise conversion. -/
private theorem linearHomSectionsToObjFun_app (s : (M.val.linearHom N).obj.sections) (U : Cᵒᵖ)
    (m : M.val.obj U) :
    ((linearHomSectionsToFun M N s).val.app U) m =
      ((linearHomObjEquiv M N U.unop (s.val U)).val.app
        (op (Over.mk (𝟙 U.unop)))) m := by
  rfl

/-- Global sections of the linear Hom sheaf are morphisms of sheaves of modules. -/
def linearHomSectionsEquiv : (M.val.linearHom N).obj.sections ≃ (M ⟶ N) where
  toFun := linearHomSectionsToFun M N
  invFun φ :=
    ⟨fun U => (linearHomObjEquiv M N U.unop).symm (φ.over U.unop), by
      intro U V f
      apply Subtype.ext
      apply NatTrans.ext
      funext W
      ext m
      -- Subtype projection removes the linearity witness; the remaining map is presheaf Hom.
      exact ConcreteCategory.congr_hom
        (presheafHom_map_app W.unop.hom f.unop (W.unop.hom ≫ f.unop) rfl
          ((linearHomObjEquiv M N U.unop).symm (φ.over U.unop)).val) m⟩
  left_inv s := by
    apply Subtype.ext
    funext U
    apply Subtype.ext
    apply NatTrans.ext
    funext V
    ext m
    let t : (presheafHom M.val.presheaf N.val.presheaf).sections :=
      ⟨fun U => (s.val U).val, fun f => congrArg Subtype.val (s.property f)⟩
    exact congrArg (fun z => (z.val U).app V m)
      ((presheafHomSectionsEquiv M.val.presheaf N.val.presheaf).left_inv t)
  right_inv φ := by
    ext U m
    -- Forget the module structure and use the inverse law for additive presheaf morphisms.
    exact congrArg (fun ψ => ψ.app U m)
      ((presheafHomSectionsEquiv M.val.presheaf N.val.presheaf).right_inv
        ((PresheafOfModules.toPresheaf _).map φ.val))

/-- The morphism associated to a global Hom section is read at the identity of each slice. -/
@[simp]
theorem linearHomSectionsEquiv_app (s : (M.val.linearHom N).obj.sections) (U : Cᵒᵖ)
    (m : M.val.obj U) :
    ((linearHomSectionsEquiv M N s).val.app U) m =
      ((linearHomObjEquiv M N U.unop (s.val U)).val.app
        (op (Over.mk (𝟙 U.unop)))) m := by
  exact linearHomSectionsToObjFun_app M N s U m

/-- The global Hom section associated to a morphism restricts to that morphism on each slice. -/
@[simp]
theorem linearHomSectionsEquiv_symm_apply (φ : M ⟶ N) (U : Cᵒᵖ) :
    ((linearHomSectionsEquiv M N).symm φ).val U =
      (linearHomObjEquiv M N U.unop).symm (φ.over U.unop) := by rfl

end SheafOfModules


-- Close scopes implicitly ended by the original source EOF.
end
end
end SheafDescentSource0


/-! ## ToricPower/OpenRestriction.lean -/

section SheafDescentSource1

/-! # Ordinary direct image restricted to an invariant open chart

This file constructs the actual base-change map for a commutative square
whose horizontal maps are open immersions.  It is an isomorphism when the
inverse image of the lower open lies in the upper open.  The construction
uses the unit and counit of restriction, so its scalar compatibility comes
from the given morphisms of schemes.

There is no assumed base-change theorem or replacement notion of sheaf.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry Opposite

namespace ToricPower

universe u

variable {X X' Y Y' : Scheme.{u}}
  (f : X ⟶ Y) (g : X' ⟶ Y') (j : X' ⟶ X) (k : Y' ⟶ Y)
  [IsOpenImmersion j] [IsOpenImmersion k]

/-- A commutative square identifies the two composite ordinary direct
images. -/
def pushforwardSquareIso (hsq : j ≫ f = g ≫ k) :
    Scheme.Modules.pushforward j ⋙ Scheme.Modules.pushforward f ≅
      Scheme.Modules.pushforward g ⋙ Scheme.Modules.pushforward k :=
  Scheme.Modules.pushforwardComp j f ≪≫
    Scheme.Modules.pushforwardCongr hsq ≪≫
      (Scheme.Modules.pushforwardComp g k).symm

/-- The canonical comparison from restriction of direct image to direct
image of restriction. -/
def pushforwardRestrictionMap (hsq : j ≫ f = g ≫ k) (M : X.Modules) :
    ((Scheme.Modules.pushforward f).obj M).restrict k ⟶
      (Scheme.Modules.pushforward g).obj (M.restrict j) :=
  (Scheme.Modules.restrictFunctor k).map
      ((Scheme.Modules.pushforward f).map
        ((Scheme.Modules.restrictAdjunction j).unit.app M)) ≫
    ((Scheme.Modules.restrictFunctor k).mapIso
      ((pushforwardSquareIso f g j k hsq).app (M.restrict j))).hom ≫
    ((Scheme.Modules.restrictFunctorAdjCounitIso k).app
      ((Scheme.Modules.pushforward g).obj (M.restrict j))).hom

/-- On an open contained in the range of `j`, the restriction unit is
an isomorphism on sections.  This is proved from the underlying sheaf
restriction map along equal open sets. -/
theorem isIso_restrictPushforwardUnit
    (hpre : f ⁻¹ᵁ k.opensRange ≤ j.opensRange) (M : X.Modules) :
    IsIso ((Scheme.Modules.restrictFunctor k).map
      ((Scheme.Modules.pushforward f).map
        ((Scheme.Modules.restrictAdjunction j).unit.app M))) := by
  let α := (Scheme.Modules.restrictFunctor k).map
    ((Scheme.Modules.pushforward f).map
      ((Scheme.Modules.restrictAdjunction j).unit.app M))
  have hα (U : Y'.Opensᵒᵖ) : IsIso (α.val.app U) := by
    rw [ConcreteCategory.isIso_iff_bijective]
    let V : X.Opens := f ⁻¹ᵁ k ''ᵁ U.unop
    have hV : V ≤ j.opensRange :=
      (f.preimage_mono (k.image_le_opensRange U.unop)).trans hpre
    have he : j ''ᵁ j ⁻¹ᵁ V = V := by
      rw [j.image_preimage_eq_opensRange_inf]
      exact inf_eq_right.mpr hV
    change Function.Bijective
      (M.presheaf.map (homOfLE (j.image_preimage_le V)).op)
    have hm : homOfLE (j.image_preimage_le V) = eqToHom he :=
      Subsingleton.elim _ _
    rw [hm]
    exact ConcreteCategory.bijective_of_isIso _
  change IsIso α
  rw [← isIso_iff_of_reflects_iso _ (SheafOfModules.forget _)]
  letI (U : Y'.Opensᵒᵖ) : IsIso (α.val.app U) := hα U
  exact (PresheafOfModules.isoMk (fun U => asIso (α.val.app U))
    fun _ _ t => α.val.naturality t).isIso_hom

/-- Base change for ordinary module-sheaf direct image along an open
immersion, under the literal inverse-image condition. -/
def pushforwardRestrictionIso (hsq : j ≫ f = g ≫ k)
    (hpre : f ⁻¹ᵁ k.opensRange ≤ j.opensRange) (M : X.Modules) :
    ((Scheme.Modules.pushforward f).obj M).restrict k ≅
      (Scheme.Modules.pushforward g).obj (M.restrict j) := by
  letI := isIso_restrictPushforwardUnit f j k hpre M
  letI : IsIso (pushforwardRestrictionMap f g j k hsq M) := by
    unfold pushforwardRestrictionMap
    infer_instance
  exact asIso (pushforwardRestrictionMap f g j k hsq M)

end ToricPower


-- Close scopes implicitly ended by the original source EOF.
end
end SheafDescentSource1


/-! ## ToricPower/SheafHomGluing.lean -/

section SheafDescentSource2

/-! # Gluing actual linear morphisms on an open cover

The local maps in this file are morphisms of actual sheaves on the slice
sites, not additional algebraic structure on a fan. The Hom sheaf supplies
existence and uniqueness of their global gluing. This is the descent step
for the compatible affine power-map projections.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

namespace ToricPower

universe u v

variable {X : Scheme.{u}} (M N : X.Modules)

/-- Pointwise compatibility of actual local module morphisms. -/
def LocalModuleHomsCompatible {ι : Type v} (U : ι → X.Opens)
    (φ : ∀ i, M.over (U i) ⟶ N.over (U i)) : Prop :=
  ∀ i j (W : X.Opens) (hWi : W ≤ U i) (hWj : W ≤ U j)
    (s : M.val.obj (op W)),
    ((φ i).val.app (op (Over.mk (homOfLE hWi)))) s =
      ((φ j).val.app (op (Over.mk (homOfLE hWj)))) s

private def homSectionFromTop
    (s : (M.val.linearHom N).obj.obj (op (⊤ : X.Opens))) :
    (M.val.linearHom N).obj.sections :=
  ⟨fun U => (M.val.linearHom N).obj.map (homOfLE (le_top : U.unop ≤ ⊤)).op s, by
    intro U V f
    rw [← CategoryTheory.Functor.map_comp_apply]
    rfl⟩

private theorem linearHomSections_compatible {ι : Type v} (U : ι → X.Opens)
    (φ : ∀ i, M.over (U i) ⟶ N.over (U i))
    (hφ : LocalModuleHomsCompatible M N U φ) :
    TopCat.Presheaf.IsCompatible (M.val.linearHom N).obj U
      (fun i => (SheafOfModules.linearHomObjEquiv M N (U i)).symm (φ i)) := by
  intro i j
  apply (SheafOfModules.linearHomObjEquiv M N (U i ⊓ U j)).injective
  ext V s
  change ((SheafOfModules.linearHomObjEquiv M N (U i ⊓ U j)
      ((M.val.linearHom N).obj.map (homOfLE inf_le_left).op
        ((SheafOfModules.linearHomObjEquiv M N (U i)).symm (φ i)))).val.app
      (op (Over.mk V.unop.hom))) s =
    ((SheafOfModules.linearHomObjEquiv M N (U i ⊓ U j)
      ((M.val.linearHom N).obj.map (homOfLE inf_le_right).op
        ((SheafOfModules.linearHomObjEquiv M N (U j)).symm (φ j)))).val.app
      (op (Over.mk V.unop.hom))) s
  rw [SheafOfModules.linearHomObjEquiv_map_app,
    SheafOfModules.linearHomObjEquiv_map_app,
    Equiv.apply_symm_apply, Equiv.apply_symm_apply]
  exact hφ i j V.unop.left
    ((leOfHom V.unop.hom).trans inf_le_left)
    ((leOfHom V.unop.hom).trans inf_le_right) s

/-- Compatible local module morphisms glue to an actual global module
morphism. Their restrictions agree literally, not merely up to isomorphism. -/
theorem exists_moduleHom_of_openCover {ι : Type v} (U : ι → X.Opens)
    (hU : iSup U = ⊤) (φ : ∀ i, M.over (U i) ⟶ N.over (U i))
    (hφ : LocalModuleHomsCompatible M N U φ) :
    ∃ ψ : M ⟶ N, ∀ i, ψ.over (U i) = φ i := by
  let F := M.val.linearHom N
  let sf := fun i => (SheafOfModules.linearHomObjEquiv M N (U i)).symm (φ i)
  obtain ⟨s, hs, _⟩ := TopCat.Sheaf.existsUnique_gluing' F U ⊤ (fun _ => homOfLE le_top)
    (by rw [hU]) sf (linearHomSections_compatible M N U φ hφ)
  let t := homSectionFromTop M N s
  let ψ := SheafOfModules.linearHomSectionsEquiv M N t
  refine ⟨ψ, fun i => ?_⟩
  apply (SheafOfModules.linearHomObjEquiv M N (U i)).symm.injective
  have hi := congrArg (fun z => z.val (op (U i)))
    ((SheafOfModules.linearHomSectionsEquiv M N).left_inv t)
  exact hi.trans (hs i)

/-- Global morphisms of module sheaves are determined by their restrictions
to any open cover. -/
theorem moduleHom_ext_openCover {ι : Type v} (U : ι → X.Opens)
    (hU : iSup U = ⊤) {φ ψ : M ⟶ N}
    (h : ∀ i, φ.over (U i) = ψ.over (U i)) : φ = ψ := by
  let F := M.val.linearHom N
  let s := (SheafOfModules.linearHomSectionsEquiv M N).symm φ
  let t := (SheafOfModules.linearHomSectionsEquiv M N).symm ψ
  have hlocal (i : ι) : s.val (op (U i)) = t.val (op (U i)) := by
    change (SheafOfModules.linearHomObjEquiv M N (U i)).symm (φ.over (U i)) =
      (SheafOfModules.linearHomObjEquiv M N (U i)).symm (ψ.over (U i))
    rw [h i]
  have htop : s.val (op (⊤ : X.Opens)) = t.val (op (⊤ : X.Opens)) := by
    have hc : TopCat.Presheaf.IsCompatible F.obj U (fun i => s.val (op (U i))) := by
      intro i j
      exact (s.property _).trans (s.property _).symm
    obtain ⟨z, hz, huniq⟩ := TopCat.Sheaf.existsUnique_gluing' F U ⊤ (fun _ => homOfLE le_top)
      (by rw [hU]) (fun i => s.val (op (U i))) hc
    apply (huniq _ (fun i => s.property _)).trans
    symm
    exact huniq _ (fun i => (t.property _).trans (hlocal i).symm)
  apply (SheafOfModules.linearHomSectionsEquiv M N).symm.injective
  apply Subtype.ext
  funext W
  exact (s.property (homOfLE (le_top : W.unop ≤ ⊤)).op).symm.trans
    ((congrArg (F.obj.map (homOfLE (le_top : W.unop ≤ ⊤)).op) htop).trans
      (t.property _))

theorem existsUnique_moduleHom_of_openCover {ι : Type v} (U : ι → X.Opens)
    (hU : iSup U = ⊤) (φ : ∀ i, M.over (U i) ⟶ N.over (U i))
    (hφ : LocalModuleHomsCompatible M N U φ) :
    ∃! ψ : M ⟶ N, ∀ i, ψ.over (U i) = φ i := by
  obtain ⟨ψ, hψ⟩ := exists_moduleHom_of_openCover M N U hU φ hφ
  refine ⟨ψ, hψ, fun χ hχ => ?_⟩
  exact moduleHom_ext_openCover M N U hU (fun i => (hχ i).trans (hψ i).symm)

/-- A compatible family of actual local retracts descends to a retract of
the global module sheaves. Both arrows are glued, and the retraction identity
is checked on the same open cover. -/
def moduleRetract_of_openCover {ι : Type v} (U : ι → X.Opens)
    (hU : iSup U = ⊤) (r : ∀ i, Retract (M.over (U i)) (N.over (U i)))
    (hi : LocalModuleHomsCompatible M N U (fun i => (r i).i))
    (hr : LocalModuleHomsCompatible N M U (fun i => (r i).r)) :
    Retract M N := by
  classical
  let ei := exists_moduleHom_of_openCover M N U hU (fun i => (r i).i) hi
  let er := exists_moduleHom_of_openCover N M U hU (fun i => (r i).r) hr
  refine ⟨ei.choose, er.choose, ?_⟩
  apply moduleHom_ext_openCover M M U hU
  intro i
  change ei.choose.over (U i) ≫ er.choose.over (U i) = 𝟙 (M.over (U i))
  rw [ei.choose_spec i, er.choose_spec i]
  exact (r i).retract

/-- Convert a morphism on the ordinary open subscheme to the equivalent
morphism on the slice site used by the Hom sheaf. The conversion uses the
actual equivalence of module-sheaf categories. -/
def moduleHomOverOfRestrict (U : X.Opens)
    (φ : M.restrict U.ι ⟶ N.restrict U.ι) : M.over U ⟶ N.over U :=
  (Scheme.Modules.overEquiv U).functor.preimage
    ((Scheme.Modules.overFunctorEquiv U).hom.app M ≫ φ ≫
      (Scheme.Modules.overFunctorEquiv U).inv.app N)

@[simp]
theorem moduleHomOverOfRestrict_map (U : X.Opens)
    (φ : M.restrict U.ι ⟶ N.restrict U.ι) :
    (Scheme.Modules.overEquiv U).functor.map (moduleHomOverOfRestrict M N U φ) =
      (Scheme.Modules.overFunctorEquiv U).hom.app M ≫ φ ≫
        (Scheme.Modules.overFunctorEquiv U).inv.app N := by
  exact (Scheme.Modules.overEquiv U).functor.map_preimage _

/-- Passing from an open subscheme to its slice site preserves an actual
retraction. This provides the input required by `moduleRetract_of_openCover`. -/
def moduleRetractOverOfRestrict (U : X.Opens)
    (r : Retract (M.restrict U.ι) (N.restrict U.ι)) :
    Retract (M.over U) (N.over U) where
  i := moduleHomOverOfRestrict M N U r.i
  r := moduleHomOverOfRestrict N M U r.r
  retract := by
    apply (Scheme.Modules.overEquiv U).functor.map_injective
    simp only [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_id, moduleHomOverOfRestrict_map,
      Category.assoc, Iso.inv_hom_id_app_assoc]
    rw [← Category.assoc r.i r.r, r.retract]
    simp

end ToricPower


-- Close scopes implicitly ended by the original source EOF.
end
end SheafDescentSource2


end PowerSheafSource0


/-! ## ToricPower/PowerChartSplitting.lean -/

section PowerSheafSource1

/-! # The coefficient projection on the literal toric chart

The ring in this file is TauCeti's actual `affineCoordinateRing hi σ`.
The monoid equivalence only removes a multiplicative type tag; the power
endomorphism remains the same coordinate-ring homomorphism defining the
geometric power map. No chart decomposition is assumed.
-/

@[expose] public noncomputable section

open MonoidAlgebra AlgebraicGeometry CategoryTheory TauCeti.Toric

namespace ToricPower

section Transport

variable {R M N : Type*} [Semiring R] [Monoid M] [Monoid N]

theorem comapDomain_transport (e : M ≃* N) (p : M →* M) (q : N →* N)
    (hp : Function.Injective p) (hq : Function.Injective q)
    (he : ∀ m, e (p m) = q (e m)) (a : R[M]) :
    mapDomain e (comapDomain p hp a) = comapDomain q hq (mapDomain e a) := by
  ext n
  obtain ⟨m, rfl⟩ := e.surjective n
  change (Finsupp.mapDomain e (a.coeff.comapDomain p hp.injOn)) (e m) =
    (Finsupp.mapDomain e a.coeff) (q (e m))
  rw [Finsupp.mapDomain_apply_of_injective e.injective, ← he,
    Finsupp.mapDomain_apply_of_injective e.injective]
  rfl

theorem mapDomain_power_transport (e : M ≃* N) (p : M →* M) (q : N →* N)
    (he : ∀ m, e (p m) = q (e m)) (a : R[M]) :
    mapDomain e (mapDomain p a) = mapDomain q (mapDomain e a) := by
  induction a using induction_linear with
  | zero => simp
  | add a b ha hb => simp only [mapDomain_add, ha, hb]
  | single m r => simp only [mapDomain_single, he]

end Transport

universe u

variable {N : Type u} {V : Type*} [AddCommGroup N] [AddCommGroup V]
  [Module ℝ V] {i : N →+ V}

theorem dualExponentPower_injective (hi : IsIntegralLattice i)
    (σ : PointedCone ℝ V) (ell : ℕ) (hell : 0 < ell) :
    Function.Injective (exponentPower ell (dualSemigroup hi σ)) := by
  intro a b hab
  apply Multiplicative.toAdd.injective
  apply Subtype.ext
  apply characterPower_injective ell hell
  exact congrArg (fun m : Multiplicative (dualSemigroup hi σ) =>
    Multiplicative.ofAdd m.toAdd.val) hab

private theorem dualPower_typeTag (hi : IsIntegralLattice i)
    (σ : PointedCone ℝ V) (ell : ℕ) (hell : 0 < ell)
    (m : Multiplicative (dualSemigroup hi σ)) :
    dualSemigroupMultiplicativeEquiv hi σ (exponentPower ell (dualSemigroup hi σ) m) =
      restrictedMonoidPower (exponentPower ell (N →+ ℤ)) (dualSemigroup hi σ).toSubmonoid
        (dualSubmonoid_power_mem hi σ ell hell)
        (dualSemigroupMultiplicativeEquiv hi σ m) := rfl

/-- The actual affine coefficient projection on the dual semigroup ring. -/
def toricChartProjection (hi : IsIntegralLattice i) (σ : PointedCone ℝ V)
    (ell : ℕ) (hell : 0 < ell) :
    affineCoordinateRing hi σ →+ affineCoordinateRing hi σ :=
  comapDomainAddMonoidHom (exponentPower ell (dualSemigroup hi σ))
    (dualExponentPower_injective hi σ ell hell)

theorem toricChartProjection_mul (hi : IsIntegralLattice i) (σ : PointedCone ℝ V)
    (ell : ℕ) (hell : 0 < ell) (a b : affineCoordinateRing hi σ) :
    toricChartProjection hi σ ell hell
      (mapDomain (exponentPower ell (dualSemigroup hi σ)) a * b) =
      a * toricChartProjection hi σ ell hell b := by
  let e := dualSemigroupMultiplicativeEquiv hi σ
  let p := exponentPower ell (dualSemigroup hi σ)
  let q := restrictedMonoidPower (exponentPower ell (N →+ ℤ))
    (dualSemigroup hi σ).toSubmonoid (dualSubmonoid_power_mem hi σ ell hell)
  have hp := dualExponentPower_injective hi σ ell hell
  have hq := restrictedMonoidPower_injective (exponentPower ell (N →+ ℤ))
    (characterPower_injective ell hell) (dualSemigroup hi σ).toSubmonoid
    (dualSubmonoid_power_mem hi σ ell hell)
  have he := dualPower_typeTag hi σ ell hell
  apply mapDomain_injective (R := ℂ) (f := e) e.injective
  change mapDomain e (comapDomain p hp (mapDomain p a * b)) =
    mapDomain e (a * comapDomain p hp b)
  rw [comapDomain_transport e p q hp hq he, mapDomain_mul,
    mapDomain_power_transport e p q he,
    restrictedProjection_mapDomain_mul (exponentPower ell (N →+ ℤ))
      (characterPower_injective ell hell) (dualSemigroup hi σ).toSubmonoid
      (dualSubmonoid_power_mem hi σ ell hell),
    mapDomain_mul, comapDomain_transport e p q hp hq he]

theorem toricChartProjection_retract (hi : IsIntegralLattice i)
    (σ : PointedCone ℝ V) (ell : ℕ) (hell : 0 < ell)
    (a : affineCoordinateRing hi σ) :
    toricChartProjection hi σ ell hell
      (mapDomain (exponentPower ell (dualSemigroup hi σ)) a) = a := by
  ext m
  exact Finsupp.mapDomain_apply_of_injective
    (dualExponentPower_injective hi σ ell hell) a.coeff m

/-- The literal ring morphism whose spectrum is the affine power map. -/
def chartPowerRingHom (Φ : Fan i) (σ : Φ.cones) (ell : ℕ) :
    CommRingCat.of (affineCoordinateRing Φ.lattice σ.val) ⟶
      CommRingCat.of (affineCoordinateRing Φ.lattice σ.val) :=
  CommRingCat.ofHom
    (affineCoordinateRingMap Φ.lattice Φ.lattice (ell • AddMonoidHom.id N)
      ((ell : ℝ) • LinearMap.id) (power_lattice_compatibility i ell)
      (powerConeMapsTo σ.val ell)).toRingHom

theorem chartPowerRingHom_apply (Φ : Fan i) (σ : Φ.cones) (ell : ℕ)
    (a : affineCoordinateRing Φ.lattice σ.val) :
    chartPowerRingHom Φ σ ell a =
      mapDomain (exponentPower ell (dualSemigroup Φ.lattice σ.val)) a := by
  exact congrArg (fun f : affineCoordinateRing Φ.lattice σ.val →+*
    affineCoordinateRing Φ.lattice σ.val => f a)
    (power_affineCoordinateRingMap_eq Φ ell σ)

/-- A genuine module morphism out of the scalar-restricted coordinate ring. -/
def chartPowerModuleProjection (Φ : Fan i) (σ : Φ.cones)
    (ell : ℕ) (hell : 0 < ell) :
    affineRestrictedRing (chartPowerRingHom Φ σ ell) ⟶
      ModuleCat.of (affineCoordinateRing Φ.lattice σ.val)
        (affineCoordinateRing Φ.lattice σ.val) :=
  ModuleCat.ofHom
    (X := affineRestrictedRing (chartPowerRingHom Φ σ ell))
    (Y := ModuleCat.of (affineCoordinateRing Φ.lattice σ.val)
      (affineCoordinateRing Φ.lattice σ.val))
    { toricChartProjection Φ.lattice σ.val ell hell with
      map_smul' := fun a b => by
        change toricChartProjection Φ.lattice σ.val ell hell
          (chartPowerRingHom Φ σ ell (show affineCoordinateRing Φ.lattice σ.val from a) *
            (show affineCoordinateRing Φ.lattice σ.val from b)) =
            (show affineCoordinateRing Φ.lattice σ.val from a) *
              toricChartProjection Φ.lattice σ.val ell hell
                (show affineCoordinateRing Φ.lattice σ.val from b)
        rw [chartPowerRingHom_apply]
        exact toricChartProjection_mul Φ.lattice σ.val ell hell a b }

/-- The structure sheaf of each actual affine toric chart is a retract of
its ordinary direct image by every positive power map. -/
def chartPowerStructureRetract (Φ : Fan i) (σ : Φ.cones)
    (ell : ℕ) (hell : 0 < ell) :
    Retract (affineStructureSheaf (CommRingCat.of (affineCoordinateRing Φ.lattice σ.val)))
      ((Scheme.Modules.pushforward (Spec.map (chartPowerRingHom Φ σ ell))).obj
        (affineStructureSheaf (CommRingCat.of (affineCoordinateRing Φ.lattice σ.val)))) :=
  affineStructureRetract (chartPowerRingHom Φ σ ell)
    (chartPowerModuleProjection Φ σ ell hell) fun a => by
      change toricChartProjection Φ.lattice σ.val ell hell
        (chartPowerRingHom Φ σ ell a) = a
      rw [chartPowerRingHom_apply]
      exact toricChartProjection_retract Φ.lattice σ.val ell hell a

end ToricPower


-- Close scopes implicitly ended by the original source EOF.
end
end PowerSheafSource1


/-! ## ToricPower/PowerChartNaturality.lean -/

section PowerSheafSource2

/-! # Naturality of the actual toric-chart projection

Every affine chart embeds in the same Laurent group algebra.  The chart
projection is the restriction of coefficient extraction in that algebra,
and the actual face-coordinate homomorphism preserves the Laurent image.
This proves the overlap identity without choosing a separate basis on
each cone.  Sheaf descent is a further step, not part of the statement here.
-/

@[expose] public noncomputable section

open MonoidAlgebra TauCeti.Toric

namespace ToricPower

variable {N V : Type*} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {i : N →+ V}

/-- The literal embedding of an affine coordinate ring into the Laurent
group algebra of the character lattice. -/
def chartLaurentMap (hi : IsIntegralLattice i) (σ : PointedCone ℝ V)
    (a : affineCoordinateRing hi σ) : ℂ[Multiplicative (N →+ ℤ)] :=
  mapDomain (dualSemigroup hi σ).toSubmonoid.subtype
    (mapDomain (dualSemigroupMultiplicativeEquiv hi σ) a)

theorem chartLaurentMap_injective (hi : IsIntegralLattice i)
    (σ : PointedCone ℝ V) : Function.Injective (chartLaurentMap hi σ) := by
  intro a b h
  apply mapDomain_injective (R := ℂ)
    (f := dualSemigroupMultiplicativeEquiv hi σ)
    (dualSemigroupMultiplicativeEquiv hi σ).injective
  exact mapDomain_injective (R := ℂ)
    (f := (dualSemigroup hi σ).toSubmonoid.subtype)
    (fun _ _ h => Subtype.ext h) h

@[simp] theorem chartLaurentMap_single (hi : IsIntegralLattice i)
    (σ : PointedCone ℝ V) (m : dualSemigroup hi σ) (z : ℂ) :
    chartLaurentMap hi σ (single (Multiplicative.ofAdd m) z) =
      single (Multiplicative.ofAdd m.val) z := by
  simp only [chartLaurentMap, mapDomain_single]
  rfl

/-- The actual toric face map is the identity on Laurent characters. -/
theorem chartLaurentMap_face (hi : IsIntegralLattice i)
    {τ σ : PointedCone ℝ V} (hτσ : τ.IsFaceOf σ)
    (a : affineCoordinateRing hi σ) :
    chartLaurentMap hi τ (faceAffineCoordinateRingMap hi hτσ a) =
      chartLaurentMap hi σ a := by
  induction a using induction_linear with
  | zero => simp [chartLaurentMap]
  | add a b ha hb =>
      simp only [map_add, chartLaurentMap, mapDomain_add] at ha hb ⊢
      rw [ha, hb]
  | single m z =>
      change chartLaurentMap hi τ
        (faceAffineCoordinateRingMap hi hτσ
          (single (Multiplicative.ofAdd m.toAdd) z)) =
        chartLaurentMap hi σ (single (Multiplicative.ofAdd m.toAdd) z)
      simp only [faceAffineCoordinateRingMap_single, chartLaurentMap_single]

/-- The coefficient projection on a cone is the restriction of the one
canonical coefficient projection on the ambient Laurent algebra. -/
theorem chartLaurentMap_projection (hi : IsIntegralLattice i)
    (σ : PointedCone ℝ V) (ell : ℕ) (hell : 0 < ell)
    (a : affineCoordinateRing hi σ) :
    chartLaurentMap hi σ (toricChartProjection hi σ ell hell a) =
      comapDomain (exponentPower ell (N →+ ℤ))
        (characterPower_injective ell hell) (chartLaurentMap hi σ a) := by
  let S := (dualSemigroup hi σ).toSubmonoid
  let e := dualSemigroupMultiplicativeEquiv hi σ
  let p := exponentPower ell (dualSemigroup hi σ)
  let q := restrictedMonoidPower (exponentPower ell (N →+ ℤ)) S
    (dualSubmonoid_power_mem hi σ ell hell)
  have hp := dualExponentPower_injective hi σ ell hell
  have hq := restrictedMonoidPower_injective (exponentPower ell (N →+ ℤ))
    (characterPower_injective ell hell) S (dualSubmonoid_power_mem hi σ ell hell)
  have he : ∀ m, e (p m) = q (e m) := fun _ => rfl
  change mapDomain S.subtype (mapDomain e (comapDomain p hp a)) =
    comapDomain (exponentPower ell (N →+ ℤ))
      (characterPower_injective ell hell) (mapDomain S.subtype (mapDomain e a))
  rw [comapDomain_transport e p q hp hq he]
  exact submonoidProjection_ambient (exponentPower ell (N →+ ℤ))
    (characterPower_injective ell hell) S
    (dualSubmonoid_power_mem hi σ ell hell) (mapDomain e a)

/-- Coefficient extraction commutes with the genuine coordinate-ring
restriction attached to every face inclusion.  No smoothness or
full-dimensionality assumption is needed. -/
theorem toricChartProjection_face (hi : IsIntegralLattice i)
    {τ σ : PointedCone ℝ V} (hτσ : τ.IsFaceOf σ)
    (ell : ℕ) (hell : 0 < ell) (a : affineCoordinateRing hi σ) :
    faceAffineCoordinateRingMap hi hτσ (toricChartProjection hi σ ell hell a) =
      toricChartProjection hi τ ell hell (faceAffineCoordinateRingMap hi hτσ a) := by
  apply chartLaurentMap_injective hi τ
  rw [chartLaurentMap_face, chartLaurentMap_projection,
    chartLaurentMap_projection, chartLaurentMap_face]

end ToricPower


-- Close scopes implicitly ended by the original source EOF.
end
end PowerSheafSource2


/-! ## ToricPower/PowerSheafCharts.lean -/

section PowerSheafSource3

/-! # The global power-map direct image on its actual affine charts

The chart comparison here is a comparison of ordinary sheaves on the
glued toric scheme.  In particular the chart retract is a retract of the
restriction of the global direct image, not of a separately postulated
module attached to a cone.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry TauCeti.Toric

namespace ToricPower

universe u

variable {N : Type u} {V : Type*} [AddCommGroup N] [AddCommGroup V]
  [Module ℝ V] {i : N →+ V}

/-- The literal chartwise identification of the ordinary direct image of
the structure sheaf by a positive toric power map. -/
def toricPowerStructureChartIso (Φ : Fan i) (ell : ℕ) (hell : 0 < ell)
    (σ : Φ.cones) :
    ((Scheme.Modules.pushforward (toricPowerMap Φ ell)).obj
      (SheafOfModules.unit Φ.algebraicRealization.ringCatSheaf)).restrict
        (Φ.affineToricChartι σ) ≅
      (Scheme.Modules.pushforward (Spec.map (chartPowerRingHom Φ σ ell))).obj
        (affineStructureSheaf
          (CommRingCat.of (affineCoordinateRing Φ.lattice σ.val))) := by
  have e := pushforwardRestrictionIso (toricPowerMap Φ ell) (affinePowerMap Φ ell σ)
      (Φ.affineToricChartι σ) (Φ.affineToricChartι σ)
      (toricPowerMap_affine_chart Φ ell hell σ)
      (by
        change (toricPowerMap Φ ell) ⁻¹' Set.range (Φ.affineToricChartι σ) ⊆
          Set.range (Φ.affineToricChartι σ)
        exact (toricPowerMap_preimage_chart Φ ell hell σ).subset)
      (SheafOfModules.unit Φ.algebraicRealization.ringCatSheaf) ≪≫
    (Scheme.Modules.pushforward (affinePowerMap Φ ell σ)).mapIso
      (Scheme.Modules.restrictUnitIso (Φ.affineToricChartι σ))
  simpa only [affinePowerMap, affineToricSchemeMap_def, chartPowerRingHom] using e

/-- On every actual affine chart, the structure sheaf is a retract of the
restriction of the global power-map direct image.  Compatibility of these
retractions on overlaps is a separate descent assertion. -/
def toricPowerRestrictedStructureRetract (Φ : Fan i)
    (ell : ℕ) (hell : 0 < ell) (σ : Φ.cones) :
    Retract
      (Scheme.Modules.restrict (SheafOfModules.unit Φ.algebraicRealization.ringCatSheaf)
        (Φ.affineToricChartι σ))
      (((Scheme.Modules.pushforward (toricPowerMap Φ ell)).obj
        (SheafOfModules.unit Φ.algebraicRealization.ringCatSheaf)).restrict
          (Φ.affineToricChartι σ)) :=
  ((Retract.ofIso (Scheme.Modules.restrictUnitIso (Φ.affineToricChartι σ))).trans
    (chartPowerStructureRetract Φ σ ell hell)).trans
      (Retract.ofIso (toricPowerStructureChartIso Φ ell hell σ).symm)

end ToricPower


-- Close scopes implicitly ended by the original source EOF.
end
end PowerSheafSource3
