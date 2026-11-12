module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Submodule
public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.AlgebraicGeometry.FunctionField
public import Mathlib.AlgebraicGeometry.Stalk
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackFree
public import Mathlib.Topology.Sheaves.Flasque
public import Mathlib.Algebra.Category.Grp.Adjunctions
public import Mathlib.Algebra.Category.Grp.EquivalenceGroupAddGroup
public import Mathlib.Algebra.Category.Ring.Adjunctions
public import Mathlib.CategoryTheory.Sites.Whiskering
public import Mathlib.Topology.Sheaves.Abelian
public import Mathlib.Topology.Sheaves.AddCommGrpCat
public import Mathlib.Topology.Sheaves.LocallySurjective
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import Mathlib.CategoryTheory.Preadditive.Biproducts
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import Mathlib.Algebra.Category.Ring.Limits
public import Mathlib.CategoryTheory.Monoidal.Braided.Basic
public import Mathlib.CategoryTheory.Monoidal.NaturalTransformation
public import Mathlib.LinearAlgebra.DirectSum.Finsupp
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Generator
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Monoidal
public import Mathlib.CategoryTheory.Localization.Monoidal.Basic
public import Mathlib.CategoryTheory.MorphismProperty.Limits
public import Mathlib.CategoryTheory.Sites.LocallyBijective
public import Mathlib.CategoryTheory.Sites.Localization
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Localization
public import Mathlib.CategoryTheory.Localization.Monoidal.Braided
public import Mathlib.Algebra.Category.ModuleCat.Products
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.OfCommRing
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Free
public import Mathlib.LinearAlgebra.StdBasis
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree
public import Mathlib.AlgebraicGeometry.Properties

/-! # Cartier divisors and their actual invertible sheaves

This consolidation preserves the recovered proof bodies and avoids repeated
import initialization during development. Each source section has explicit
upstream provenance. Verification is established only by successful compiler
and axiom-audit records for this exact file.
-/

/-! ## Recovered file CartierBase

Source SHA256: 213c93f5738fb04fa6704c3c34b168d8c65290438b04f0d5f32f11e9e41ac738.
The original named source sections and every proof body follow unchanged.
-/

/-! Exact proof bodies split from the uncompiled SchemeCore candidate.
No proof is replaced by an assumption. See `third_party/TauCeti/scheme_split.json`.
Verification requires an ordinary successful compiler record for this exact file. -/

/-! ## Unchanged proof bodies from `TauCeti.Algebra.Category.ModuleCat.Sheaf.Submodule`

Upstream commit: 6b896c7c411221eb78639e4be8ead6e479a62893.
Original SHA256: d99cb49d18f4cc3e649fc0fc970fc337446aec1dba56210c2cfb397ad040e789.
Module/import commands alone are relocated; EOF scopes are closed explicitly.
-/
section CartierSource00
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/


/-!
# Factoring a morphism through a submodule of a (pre)sheaf of modules

Mathlib's `PresheafOfModules.Submodule` and `SheafOfModules.Submodule` package a submodule of a
(pre)sheaf of modules together with the inclusion `N.ι` of the associated (pre)sheaf of modules.
This file supplies the missing universal property of that inclusion: a morphism whose sections all
land in `N` factors through `N`, uniquely because `N.ι` is a monomorphism.

## Main declarations

* `TauCeti.PresheafOfModules.liftToSubmodule` and `TauCeti.SheafOfModules.liftToSubmodule`, the
  factorization itself, with `liftToSubmodule_ι` recording that it does factor the given morphism;
* `TauCeti.SheafOfModules.isIso_liftToSubmodule`: the factorization is an isomorphism when the
  morphism is injective on sections with image exactly `N`;
* `TauCeti.SheafOfModules.Submodule.homOfLE`, the inclusion of one submodule of a sheaf of modules
  into a larger one;
* `SheafOfModules.Submodule.overIsoOfEq`, the identification over `V` of two submodules
  with the same sections over every object above `V`.

No formalization is vendored; the constructions are `AddMonoidHom.codRestrict` applied section by
section, assembled by Mathlib's `PresheafOfModules.homMk`.
-/

public section

universe v v₁ u₁ u

open CategoryTheory Opposite

variable {C : Type u₁} [Category.{v₁} C]

namespace TauCeti

namespace PresheafOfModules

variable {R : Cᵒᵖ ⥤ RingCat.{u}} {M P : _root_.PresheafOfModules.{v} R}

noncomputable section

/-- A morphism of presheaves of modules all of whose sections lie in a submodule `N` of the
target factors through the presheaf of modules attached to `N`. -/
def liftToSubmodule (N : M.Submodule) (φ : P ⟶ M)
    (hφ : ∀ (U : Cᵒᵖ) (s : P.obj U), φ.app U s ∈ N.obj U) :
    P ⟶ N.toPresheafOfModules :=
  _root_.PresheafOfModules.homMk
    { app U := AddCommGrpCat.ofHom
        (((φ.app U).hom.toAddMonoidHom).codRestrict (N.obj U) (hφ U))
      naturality := by
        intro U V f
        ext x
        apply Subtype.ext
        exact _root_.PresheafOfModules.naturality_apply φ f x }
    (by
      intro U r m
      apply Subtype.ext
      exact (φ.app U).hom.map_smul r m)

@[simp]
lemma liftToSubmodule_app_coe (N : M.Submodule) (φ : P ⟶ M)
    (hφ : ∀ (U : Cᵒᵖ) (s : P.obj U), φ.app U s ∈ N.obj U) (U : Cᵒᵖ) (s : P.obj U) :
    ((liftToSubmodule N φ hφ).app U s).val = φ.app U s :=
  (rfl)

@[reassoc (attr := simp)]
lemma liftToSubmodule_ι (N : M.Submodule) (φ : P ⟶ M)
    (hφ : ∀ (U : Cᵒᵖ) (s : P.obj U), φ.app U s ∈ N.obj U) :
    liftToSubmodule N φ hφ ≫ N.ι = φ := by
  ext U s
  exact liftToSubmodule_app_coe N φ hφ U s

lemma ι_app_mem (N : M.Submodule) (U : Cᵒᵖ) (s : N.toPresheafOfModules.obj U) :
    N.ι.app U s ∈ N.obj U :=
  s.2

end

end PresheafOfModules

namespace SheafOfModules

variable {J : GrothendieckTopology C} {R : Sheaf J RingCat.{u}}
  {M P : _root_.SheafOfModules.{v} R}

noncomputable section

/-- A morphism of sheaves of modules all of whose sections lie in a submodule `N` of the target
factors through the sheaf of modules attached to `N`. -/
def liftToSubmodule (N : M.Submodule) (φ : P ⟶ M)
    (hφ : ∀ (U : Cᵒᵖ) (s : P.val.obj U), φ.val.app U s ∈ N.toSubmodule.obj U) :
    P ⟶ N.toSheafOfModules :=
  ⟨PresheafOfModules.liftToSubmodule N.toSubmodule φ.val hφ⟩

@[simp]
lemma liftToSubmodule_val_app_coe (N : M.Submodule) (φ : P ⟶ M)
    (hφ : ∀ (U : Cᵒᵖ) (s : P.val.obj U), φ.val.app U s ∈ N.toSubmodule.obj U)
    (U : Cᵒᵖ) (s : P.val.obj U) :
    ((liftToSubmodule N φ hφ).val.app U s).val = φ.val.app U s :=
  (rfl)

@[reassoc (attr := simp)]
lemma liftToSubmodule_ι (N : M.Submodule) (φ : P ⟶ M)
    (hφ : ∀ (U : Cᵒᵖ) (s : P.val.obj U), φ.val.app U s ∈ N.toSubmodule.obj U) :
    liftToSubmodule N φ hφ ≫ N.ι = φ :=
  _root_.SheafOfModules.Hom.ext (PresheafOfModules.liftToSubmodule_ι N.toSubmodule φ.val hφ)

lemma ι_val_app_mem (N : M.Submodule) (U : Cᵒᵖ) (s : N.toSheafOfModules.val.obj U) :
    N.ι.val.app U s ∈ N.toSubmodule.obj U :=
  PresheafOfModules.ι_app_mem N.toSubmodule U s

/-- The inclusion of a submodule sheaf is injective on sections. -/
lemma ι_val_app_injective (N : M.Submodule) (U : Cᵒᵖ) :
    Function.Injective (N.ι.val.app U) :=
  Subtype.val_injective

/-- The image of the inclusion on sections is the defining submodule. -/
@[simp]
lemma range_ι_val_app (N : M.Submodule) (U : Cᵒᵖ) :
    Set.range (N.toSubmodule.ι.app U) = N.toSubmodule.obj U := by
  ext s
  exact ⟨fun ⟨t, ht⟩ ↦ ht ▸ ι_val_app_mem N U t, fun hs ↦ ⟨⟨s, hs⟩, rfl⟩⟩

/-- The factorization `liftToSubmodule N φ hφ` is an isomorphism when `φ` is injective on sections
and every section of `N` is in the image of `φ`. -/
lemma isIso_liftToSubmodule (N : M.Submodule) (φ : P ⟶ M)
    (hφ : ∀ (U : Cᵒᵖ) (s : P.val.obj U), φ.val.app U s ∈ N.toSubmodule.obj U)
    (hinj : ∀ U : Cᵒᵖ, Function.Injective (φ.val.app U))
    (hsurj : ∀ (U : Cᵒᵖ) (s : M.val.obj U), s ∈ N.toSubmodule.obj U → ∃ t, φ.val.app U t = s) :
    IsIso (liftToSubmodule N φ hφ) := by
  rw [← isIso_iff_of_reflects_iso _ (_root_.SheafOfModules.forget _)]
  have (U : Cᵒᵖ) : IsIso ((liftToSubmodule N φ hφ).val.app U) := by
    rw [ConcreteCategory.isIso_iff_bijective]
    refine ⟨fun a b hab ↦ hinj U ?_, fun s ↦ ?_⟩
    · simpa only [liftToSubmodule_val_app_coe] using congrArg Subtype.val hab
    · obtain ⟨t, ht⟩ := hsurj U s.1 s.2
      exact ⟨t, Subtype.ext (by simpa only [liftToSubmodule_val_app_coe] using ht)⟩
  exact (_root_.PresheafOfModules.isoMk (fun U ↦ asIso ((liftToSubmodule N φ hφ).val.app U))
    fun _ _ f ↦ (liftToSubmodule N φ hφ).val.naturality f).isIso_hom

namespace Submodule

/-- The inclusion of a submodule of a sheaf of modules into a larger one. The hypothesis is
stated for the underlying submodules of the presheaf of modules, which is what
`SheafOfModules.Submodule.le_iff` says the order on submodules of a sheaf of modules is. -/
def homOfLE {N₁ N₂ : M.Submodule} (h : N₁.toSubmodule ≤ N₂.toSubmodule) :
    N₁.toSheafOfModules ⟶ N₂.toSheafOfModules :=
  ⟨_root_.PresheafOfModules.Submodule.homOfLE h⟩

@[reassoc (attr := simp)]
lemma homOfLE_ι {N₁ N₂ : M.Submodule} (h : N₁.toSubmodule ≤ N₂.toSubmodule) :
    homOfLE h ≫ N₂.ι = N₁.ι :=
  _root_.SheafOfModules.Hom.ext (_root_.PresheafOfModules.Submodule.homOfLE_ι h)

end Submodule

end

end SheafOfModules

end TauCeti

namespace SheafOfModules.Submodule

variable {J : GrothendieckTopology C} {R : Sheaf J RingCat.{u}} {M : SheafOfModules.{v} R}

noncomputable section

/-- Two submodules of a sheaf of modules which have the same sections over every object above `V`
give isomorphic sheaves of modules over `V`, compatibly with their inclusions (`overIsoOfEq_hom_ι`,
`overIsoOfEq_inv_ι`). -/
def overIsoOfEq (N₁ N₂ : M.Submodule) (V : C)
    (h : ∀ (W : C) (_ : W ⟶ V), N₁.toSubmodule.obj (op W) = N₂.toSubmodule.obj (op W)) :
    N₁.toSheafOfModules.over V ≅ N₂.toSheafOfModules.over V :=
  (SheafOfModules.fullyFaithfulForget _).preimageIso <|
    PresheafOfModules.isoMk
      (fun W ↦
        letI := ((N₁.toSheafOfModules.over V).val.obj W).isModule
        letI := ((N₂.toSheafOfModules.over V).val.obj W).isModule
        LinearEquiv.toModuleIso
          (LinearEquiv.ofEq _ _ (h _ W.unop.hom)))
      (fun _ _ _ ↦ rfl)

/-- The inclusion of a submodule remains a monomorphism after restricting to an object. -/
instance instMonoιOver (N : M.Submodule) (V : C) : Mono (N.ι.over V) := by
  apply (SheafOfModules.forget _).mono_of_mono_map
  -- `SheafOfModules.forget` sends a morphism to its underlying presheaf morphism `.val` by
  -- definition, and Mathlib has no `forget_map` lemma to rewrite with, so we restate the goal.
  change Mono (N.ι.over V).val
  apply PresheafOfModules.mono_of_injective
  intro W
  exact Subtype.val_injective

/-- The isomorphism `overIsoOfEq` is compatible with the inclusions into `M`. -/
@[reassoc (attr := simp)]
lemma overIsoOfEq_hom_ι (N₁ N₂ : M.Submodule) (V : C)
    (h : ∀ (W : C) (_ : W ⟶ V), N₁.toSubmodule.obj (op W) = N₂.toSubmodule.obj (op W)) :
    (overIsoOfEq N₁ N₂ V h).hom ≫ N₂.ι.over V = N₁.ι.over V := by
  ext W s
  rfl

/-- The inverse of `overIsoOfEq` is compatible with the inclusions into `M`. -/
@[reassoc (attr := simp)]
lemma overIsoOfEq_inv_ι (N₁ N₂ : M.Submodule) (V : C)
    (h : ∀ (W : C) (_ : W ⟶ V), N₁.toSubmodule.obj (op W) = N₂.toSubmodule.obj (op W)) :
    (overIsoOfEq N₁ N₂ V h).inv ≫ N₁.ι.over V = N₂.ι.over V := by
  ext W s
  rfl

end

end SheafOfModules.Submodule

end
end CartierSource00

/-! ## Upstream proof bodies from `TauCeti.AlgebraicGeometry.Modules.GlobalSections` (compatibility edits recorded)

Upstream commit: 6b896c7c411221eb78639e4be8ead6e479a62893.
Original SHA256: 15199b6ef7b70adb9f925496caabd181496c885f2be3f8fef7d40709b9d7af9e.
Module/import commands are relocated; EOF scopes are closed explicitly.
Target-version compatibility edits are recorded in
`audit/toric_power/scheme_pass1_repairs.json`; these bodies are not yet verified.
-/
section CartierSource01
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/


/-!
# Global-functions actions on sheaves of modules

This file constructs the canonical action of the ring of global functions on a sheaf of modules
on a scheme, shows that multiplication by a global unit is an isomorphism, and records how the
action is carried along a morphism of schemes `f : X ⟶ Y`: pushing forward multiplication by
`f^♯ r` is multiplication by `r`, and pulling back multiplication by `r` is multiplication by
`f^♯ r` (`Scheme.Modules.pushforward_map_globalSectionsSmul` and
`Scheme.Modules.pullback_map_globalSectionsSmul`). It also records the restriction of this
action to the base ring for a scheme over a commutative ring, and the morphism
`Scheme.baseRingToStructurePresheaf` from the constant presheaf of the base ring to the structure
presheaf. Pullback of local functions by a morphism over the base preserves these images
(`AlgebraicGeometry.Scheme.Modules.app_baseRingToStructurePresheaf`).

These constructions are independent of sheaf cohomology. They supply the scalar actions used by
`TauCeti.AlgebraicGeometry.Cohomology.Module.Basic`.
-/

public section

open CategoryTheory Limits TopologicalSpace AlgebraicGeometry Scheme.Modules Opposite

universe u

noncomputable section

namespace AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}} {M N : X.Modules}

/-- The restriction of a global function to an open subset. -/
private def restrictGlobal (U : X.Opens) (r : Γ(X, ⊤)) :
    X.ringCatSheaf.obj.obj (.op U) :=
  X.presheaf.map (homOfLE le_top).op r

/-- Multiplication by a global function, as a morphism of sheaves of modules. -/
def globalSectionsSmul
    (M : X.Modules) (r : Γ(X, ⊤)) : M ⟶ M where
  val.app U := by
    letI : CommRing (X.ringCatSheaf.obj.obj U) :=
      inferInstanceAs (CommRing (X.presheaf.obj U))
    exact ModuleCat.ofHom <|
      LinearMap.lsmul (X.ringCatSheaf.obj.obj U) (M.val.obj U) (restrictGlobal U.unop r)
  val.naturality {U V} f := by
    let : CommRing (X.ringCatSheaf.obj.obj U) :=
      inferInstanceAs (CommRing (X.presheaf.obj U))
    let : CommRing (X.ringCatSheaf.obj.obj V) :=
      inferInstanceAs (CommRing (X.presheaf.obj V))
    ext x
    dsimp only [ModuleCat.hom_comp, ModuleCat.hom_ofHom, LinearMap.coe_comp,
      Function.comp_apply, LinearMap.lsmul_apply]
    rw [M.val.map_smul]
    -- The restriction-of-scalars wrapper is transparent but has no lemma exposing this
    -- pointwise goal, so normalize it to the presheaf action explicitly.
    change restrictGlobal V.unop r • M.val.map f x =
      X.ringCatSheaf.obj.map f (restrictGlobal U.unop r) • M.val.map f x
    congr 1
    change X.presheaf.map (homOfLE le_top).op r =
      X.presheaf.map f (X.presheaf.map (homOfLE le_top).op r)
    rw [← Functor.map_comp_apply]
    congr

@[simp]
lemma globalSectionsSmul_app
    (M : X.Modules) (r : Γ(X, ⊤)) (U : X.Opens) :
    (globalSectionsSmul M r).app U = (M.smul (X.presheaf.map U.leTop.op r)).asHom := by
  rfl

-- In the next four proofs, sheaf-morphism extensionality leaves pointwise bundled-module goals.
-- The wrappers have no pointwise equality lemmas, so each `change` records the corresponding
-- public presheaf/module formulation before applying the ring and module laws.
@[simp]
lemma globalSectionsSmul_zero
    (M : X.Modules) : globalSectionsSmul M 0 = 0 := by
  ext U x
  change X.presheaf.map U.leTop.op 0 • x = 0
  simp

@[simp]
lemma globalSectionsSmul_add
    (M : X.Modules) (r s : Γ(X, ⊤)) :
    globalSectionsSmul M (r + s) = globalSectionsSmul M r + globalSectionsSmul M s := by
  ext U x
  change X.presheaf.map U.leTop.op (r + s) • x =
    X.presheaf.map U.leTop.op r • x +
      X.presheaf.map U.leTop.op s • x
  simp [add_smul]

@[simp]
lemma globalSectionsSmul_one
    (M : X.Modules) : globalSectionsSmul M 1 = 𝟙 M := by
  ext U x
  change X.presheaf.map U.leTop.op 1 • x = x
  simp

@[simp]
lemma globalSectionsSmul_mul
    (M : X.Modules) (r s : Γ(X, ⊤)) :
    globalSectionsSmul M (r * s) = globalSectionsSmul M s ≫ globalSectionsSmul M r := by
  ext U x
  change X.presheaf.map U.leTop.op (r * s) • x =
    X.presheaf.map U.leTop.op r •
      X.presheaf.map U.leTop.op s • x
  rw [map_mul, mul_smul]

/-- Multiplication by a global unit is an isomorphism, with inverse multiplication by the inverse
unit. -/
instance isIso_globalSectionsSmul_units
    (M : X.Modules) (u : Γ(X, ⊤)ˣ) : IsIso (globalSectionsSmul M u) :=
  ⟨globalSectionsSmul M ↑u⁻¹,
    by rw [← globalSectionsSmul_mul, Units.inv_mul, globalSectionsSmul_one],
    by rw [← globalSectionsSmul_mul, Units.mul_inv, globalSectionsSmul_one]⟩

/-- The action of global functions on a sheaf of modules, bundled as a ring homomorphism into
the endomorphism ring of the sheaf. -/
def globalSectionsAction
    (M : X.Modules) : Γ(X, ⊤) →+* End M where
  toFun r := End.of (globalSectionsSmul M r)
  map_one' := by
    apply End.ext
    exact globalSectionsSmul_one M
  map_mul' := fun r s ↦ by
    apply End.ext
    exact globalSectionsSmul_mul M r s
  map_zero' := by
    apply End.ext
    exact globalSectionsSmul_zero M
  map_add' := fun r s ↦ by
    apply End.ext
    exact globalSectionsSmul_add M r s

@[simp]
lemma globalSectionsAction_apply
    (M : X.Modules) (r : Γ(X, ⊤)) :
    globalSectionsAction M r = End.of (globalSectionsSmul M r) :=
  by rfl

/-- Multiplication by a global function is natural in the sheaf of modules. -/
@[reassoc]
lemma globalSectionsSmul_naturality
    (f : M ⟶ N) (r : Γ(X, ⊤)) :
    globalSectionsSmul M r ≫ f = f ≫ globalSectionsSmul N r := by
  ext U x
  -- As above, extensionality exposes the underlying bundled maps only definitionally.
  change f.app U (X.presheaf.map U.leTop.op r • x) =
    X.presheaf.map U.leTop.op r • f.app U x
  exact f.app_smul _ _

section Functoriality

variable {Y : Scheme.{u}} (f : X ⟶ Y)

/-- Pushing forward multiplication by the pullback `f^♯ r` of a global function `r` on `Y` gives
multiplication by `r` on the pushforward. -/
@[simp]
lemma pushforward_map_globalSectionsSmul
    (N : X.Modules) (r : Γ(Y, ⊤)) :
    (pushforward f).map (globalSectionsSmul N (f.appTop r)) =
      globalSectionsSmul ((pushforward f).obj N) r := by
  refine hom_ext _ _ fun U ↦ ?_
  rw [pushforward_map_app, globalSectionsSmul_app, globalSectionsSmul_app]
  -- The sections of the pushforward over `U` are the sections of `N` over `f ⁻¹ᵁ U`, with scalars
  -- restricted along `f.app U`; no lemma exposes this, so record it explicitly.
  change (N.smul (X.presheaf.map (f ⁻¹ᵁ U).leTop.op (f.appTop r))).asHom =
    (N.smul (f.app U (Y.presheaf.map U.leTop.op r))).asHom
  congr 2
  exact (ConcreteCategory.comp_apply _ _ r).symm.trans
    (congrArg (· r) (f.naturality U.leTop.op)).symm

/-- Pulling back multiplication by a global function `r` on `Y` gives multiplication by the
pullback `f^♯ r` of `r` on the pullback. -/
@[simp]
lemma pullback_map_globalSectionsSmul
    (M : Y.Modules) (r : Γ(Y, ⊤)) :
    (pullback f).map (globalSectionsSmul M r) =
      globalSectionsSmul ((pullback f).obj M) (f.appTop r) := by
  -- Both sides are determined by their adjuncts `M ⟶ f_* f^* M`, which agree by naturality of
  -- the unit and of the global-functions action.
  apply ((pullbackPushforwardAdjunction f).homEquiv M
    ((pullback f).obj M)).injective
  simp only [Adjunction.homEquiv_apply, pushforward_map_globalSectionsSmul]
  exact ((pullbackPushforwardAdjunction f).unit.naturality (globalSectionsSmul M r)).symm.trans
    (globalSectionsSmul_naturality ((pullbackPushforwardAdjunction f).unit.app M) r)

end Functoriality

end AlgebraicGeometry.Scheme.Modules

section Base

variable (R : Type u) [CommRing R] (X : Scheme.{u}) [X.Over (Spec (.of R))]

namespace AlgebraicGeometry.Scheme.Modules

/-- The homomorphism from the base ring to global functions on a scheme over that ring. -/
def baseRingToGlobalSections : R →+* Γ(X, ⊤) :=
  ((Scheme.ΓSpecIso (.of R)).inv ≫ (X ↘ Spec (.of R)).appTop).hom

/-- The base ring acts through the pullback along the structure morphism: `r` is sent to the
global function obtained by pulling back the function on `Spec R` corresponding to `r`. -/
@[simp]
lemma baseRingToGlobalSections_apply (r : R) :
    baseRingToGlobalSections R X r =
      (X ↘ Spec (.of R)).appTop ((Scheme.ΓSpecIso (.of R)).inv r) :=
  (rfl)

end AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry.Scheme

/-- The morphism from the constant presheaf of rings `R` to the structure presheaf of a scheme
over `R`: on an open `U` it is the base ring map to global functions followed by restriction
to `U`. -/
def baseRingToStructurePresheaf :
    (Functor.const X.Opensᵒᵖ).obj (CommRingCat.of R) ⟶ X.presheaf where
  app U := CommRingCat.ofHom (Modules.baseRingToGlobalSections R X) ≫
    X.presheaf.map U.unop.leTop.op
  naturality U V i := by
    simp only [Functor.const_obj_obj, Functor.const_obj_map, Category.id_comp, Category.assoc,
      ← Functor.map_comp]
    rfl

/-- On an open `U`, the base ring maps to sections over `U` through global functions followed by
restriction to `U`. -/
@[simp]
lemma baseRingToStructurePresheaf_app (U : X.Opensᵒᵖ) :
    (X.baseRingToStructurePresheaf R).app U =
      CommRingCat.ofHom (Modules.baseRingToGlobalSections R X) ≫
        X.presheaf.map U.unop.leTop.op :=
  (rfl)

/-- On an open `U`, the base-ring map `R → Γ(X, U)` is the composite of `R ≅ Γ(Spec R, ⊤)` with
the map on functions induced by the structure morphism. -/
lemma baseRingToStructurePresheaf_app_eq_appLE (U : X.Opens) :
    (X.baseRingToStructurePresheaf R).app (op U) =
      (Scheme.ΓSpecIso (.of R)).inv ≫ (X ↘ Spec (.of R)).appLE ⊤ U le_top := by
  ext r
  rw [baseRingToStructurePresheaf_app, CommRingCat.comp_apply, CommRingCat.comp_apply,
    CommRingCat.ofHom_apply, Modules.baseRingToGlobalSections_apply]
  -- Both sides restrict the pullback of `r` from `⊤` to `U`; `appLE ⊤ U` is by definition
  -- `app ⊤` followed by that restriction.
  rfl

variable {R} in
/-- Compatible structure morphisms make the actions of the two base rings on sections
into a scalar tower. -/
theorem baseRingToStructurePresheaf_app_algebraMap
    {S : Type u} [CommRing S] [Algebra R S] [X.Over (Spec (.of S))]
    (h : (X ↘ Spec (.of S)) ≫ Spec.map (CommRingCat.ofHom (algebraMap R S)) =
      (X ↘ Spec (.of R))) (U : X.Opens) (r : R) :
    (X.baseRingToStructurePresheaf S).app (op U) (algebraMap R S r) =
      (X.baseRingToStructurePresheaf R).app (op U) r := by
  have htop := congrArg Scheme.Hom.appTop h
  rw [Scheme.Hom.comp_appTop] at htop
  have hΓ : CommRingCat.ofHom (algebraMap R S) ≫ (Scheme.ΓSpecIso (.of S)).inv ≫
      (X ↘ Spec (.of S)).appTop =
      (Scheme.ΓSpecIso (.of R)).inv ≫ (X ↘ Spec (.of R)).appTop := by
    rw [Scheme.ΓSpecIso_inv_naturality_assoc, htop]
  rw [Scheme.baseRingToStructurePresheaf_app, Scheme.baseRingToStructurePresheaf_app,
    CommRingCat.comp_apply, CommRingCat.comp_apply, CommRingCat.ofHom_apply,
    CommRingCat.ofHom_apply, Scheme.Modules.baseRingToGlobalSections_apply,
    Scheme.Modules.baseRingToGlobalSections_apply]
  -- The base-ring maps use global sections followed by restriction to `U`.
  exact congrArg (fun a ↦ X.presheaf.map U.leTop.op a)
    (ConcreteCategory.congr_hom hΓ r)

end AlgebraicGeometry.Scheme

namespace AlgebraicGeometry.Scheme.Modules

variable {X} in
/-- Pullback of local functions along a morphism over `Spec R` preserves the image of the
base ring. -/
lemma app_baseRingToStructurePresheaf {Y : Scheme.{u}} [Y.Over (Spec (.of R))]
    (f : X ⟶ Y) [f.IsOver (Spec (.of R))] (U : Y.Opens) (r : R) :
    f.app U ((Y.baseRingToStructurePresheaf R).app (op U) r) =
      (X.baseRingToStructurePresheaf R).app (op (f ⁻¹ᵁ U)) r := by
  rw [Scheme.baseRingToStructurePresheaf_app, Scheme.baseRingToStructurePresheaf_app]
  -- The maps obtained from `CommRingCat.ofHom` compute through their bundled ring homs.
  change f.app U (Y.presheaf.map U.leTop.op (baseRingToGlobalSections R Y r)) =
    X.presheaf.map (f ⁻¹ᵁ U).leTop.op (baseRingToGlobalSections R X r)
  rw [← ConcreteCategory.comp_apply, f.naturality U.leTop.op]
  have h := congrArg Scheme.Hom.appTop
    (HomIsOver.comp_over (f := f) (S := Spec (.of R)))
  rw [Scheme.Hom.comp_appTop] at h
  rw [ConcreteCategory.comp_apply, baseRingToGlobalSections_apply,
    baseRingToGlobalSections_apply, ← h, ConcreteCategory.comp_apply]
  rfl

/-- Global sections of a sheaf of modules on a scheme over a commutative ring form a module over
the base ring. The priority is below the default so that the canonical action of
`Γ(X, ⊤)` is still the one found when the base ring is the ring of global functions itself. -/
instance (priority := 900) globalSectionsBaseModule
    (M : X.Modules) : Module R Γ(M, ⊤) :=
  Module.compHom Γ(M, ⊤) (baseRingToGlobalSections R X)

@[simp]
lemma base_smul_globalSections
    (M : X.Modules) (r : R) (x : Γ(M, ⊤)) :
    r • x = baseRingToGlobalSections R X r • x :=
  rfl

end AlgebraicGeometry.Scheme.Modules

end Base

end

end
end CartierSource01

/-! ## Unchanged proof bodies from `TauCeti.AlgebraicGeometry.Scheme.Opens`

Upstream commit: 6b896c7c411221eb78639e4be8ead6e479a62893.
Original SHA256: 945f605ee0490b8fc30650f0eeda95cc0054e0b2e06ffb5afbee842b8a8e87e6.
Module/import commands alone are relocated; EOF scopes are closed explicitly.
-/
section CartierSource02
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/


/-!
# Open subsets of schemes

This file records general-purpose facts about open subsets of schemes.

## Main declarations

* `TauCeti.AlgebraicGeometry.Scheme.instNonemptyTop` states that the whole space is a nonempty open
  subset of any nonempty scheme.
* `AlgebraicGeometry.IsAffineOpen.presheaf_map_fromSpec_appIso_hom` identifies restriction of
  structure-sheaf sections along the affine chart `Spec Γ(X, U)`.
* `AlgebraicGeometry.Scheme.Hom.appLE_eq_id_of_eq_id` identifies the restriction maps of a scheme
  endomorphism equal to the identity.
* `AlgebraicGeometry.Scheme.existsUnique_gluing_affineOpens`: sections over the affine opens,
  compatible with restriction, glue to a unique global section.
* `AlgebraicGeometry.IsAffineOpen.fromSpec_appLE_self` and
  `AlgebraicGeometry.Scheme.Hom.appLE_ΓSpecIso_hom_naturality` compute the global sections of
  affine charts `Spec R ⟶ X` and their precomposites with `Spec.map φ`.
-/

open TopologicalSpace AlgebraicGeometry

namespace TauCeti

namespace AlgebraicGeometry

universe u

public section

open CategoryTheory Opposite

noncomputable section

variable {X : Scheme.{u}} {U : X.Opens}

/-- If an endomorphism `f` of `X` equals the identity, then so does each of its restriction maps
`Γ(X, U) ⟶ Γ(X, U)`. -/
theorem _root_.AlgebraicGeometry.Scheme.Hom.appLE_eq_id_of_eq_id {f : X ⟶ X}
    (hf : f = 𝟙 X) (U : X.Opens) (e : U ≤ f ⁻¹ᵁ U) : f.appLE U U e = 𝟙 _ := by
  subst hf
  rw [Scheme.Hom.appLE, Scheme.Hom.id_app]
  exact (Category.id_comp _).trans (X.presheaf.map_id _)

/-- **Sections glue along the affine opens.** A family of sections `s U ∈ Γ(X, U)`, one over each
affine open `U` of `X`, compatible with restriction from an affine open to a smaller one, consists
of the restrictions of a unique global section. -/
theorem _root_.AlgebraicGeometry.Scheme.existsUnique_gluing_affineOpens (X : Scheme.{u})
    (s : ∀ U : X.affineOpens, Γ(X, U.1))
    (hs : ∀ (U V : X.affineOpens) (h : V.1 ≤ U.1), X.presheaf.map (homOfLE h).op (s U) = s V) :
    ∃! t : Γ(X, ⊤), ∀ U : X.affineOpens, X.presheaf.map (homOfLE le_top).op t = s U := by
  -- every open `V` is covered by the affine opens it contains
  have hcov (V : X.Opens) : V ≤ ⨆ W : {W : X.affineOpens // W.1 ≤ V}, W.1.1 := fun x hx ↦ by
    obtain ⟨_, ⟨W, hW, rfl⟩, hxW, hWV⟩ :=
      X.isBasis_affineOpens.exists_subset_of_mem_open hx V.isOpen
    exact Opens.mem_iSup.mpr ⟨⟨⟨W, hW⟩, hWV⟩, hxW⟩
  refine X.sheaf.existsUnique_gluing' (fun U : X.affineOpens ↦ U.1) ⊤ (fun _ ↦ homOfLE le_top)
    (iSup_affineOpens_eq_top X).ge s fun U U' ↦ ?_
  -- on `U ⊓ U'`, the two restrictions agree on every affine open `W ⊆ U ⊓ U'`
  refine X.sheaf.eq_of_locally_eq' (fun W : {W : X.affineOpens // W.1 ≤ U.1 ⊓ U'.1} ↦ W.1.1) _
    (fun W ↦ homOfLE W.2) (hcov _) _ _ fun W ↦ ?_
  -- stated through `X.presheaf`, the underlying presheaf of `X.sheaf`
  have h₁ : X.presheaf.map (homOfLE W.2).op (X.presheaf.map (Opens.infLELeft U.1 U'.1).op (s U)) =
      s W.1 := by
    rw [← ConcreteCategory.comp_apply, ← Functor.map_comp]
    exact hs U W.1 (W.2.trans inf_le_left)
  have h₂ :
      X.presheaf.map (homOfLE W.2).op (X.presheaf.map (Opens.infLERight U.1 U'.1).op (s U')) =
        s W.1 := by
    rw [← ConcreteCategory.comp_apply, ← Functor.map_comp]
    exact hs U' W.1 (W.2.trans inf_le_right)
  exact h₁.trans h₂.symm

/-- Along the open immersion `hU.fromSpec : Spec Γ(X, U) ⟶ X` onto an affine open `U`,
restricting a section of `𝒪_X` from `U` to the image of an open `V` and transporting it to `V`
gives the restriction to `V` of the corresponding global section of `Spec Γ(X, U)`. -/
@[reassoc]
theorem _root_.AlgebraicGeometry.IsAffineOpen.presheaf_map_fromSpec_appIso_hom
    (hU : IsAffineOpen U) (V : (Spec Γ(X, U)).Opens) :
    X.presheaf.map (homOfLE (by
        simpa [hU.opensRange_fromSpec] using hU.fromSpec.image_le_opensRange V)).op ≫
      (hU.fromSpec.appIso V).hom =
      (Scheme.ΓSpecIso Γ(X, U)).inv ≫ (Spec Γ(X, U)).presheaf.map V.leTop.op := by
  rw [← hU.fromSpec.appLE_appIso_inv (by simp [hU.fromSpec_preimage_self]), Category.assoc,
    Iso.inv_hom_id, Category.comp_id, Scheme.Hom.appLE, hU.fromSpec_app_self, Category.assoc,
    ← Functor.map_comp]
  rfl

/-- Pulling a section over an affine open `U` back to all of `Spec Γ(X, U)` along `hU.fromSpec`
is the inverse of the global-sections isomorphism of `Spec`. -/
theorem _root_.AlgebraicGeometry.IsAffineOpen.fromSpec_appLE_self (hU : IsAffineOpen U)
    (e : ⊤ ≤ hU.fromSpec ⁻¹ᵁ U) :
    hU.fromSpec.appLE U ⊤ e = (Scheme.ΓSpecIso Γ(X, U)).inv := by
  rw [Scheme.Hom.appLE, hU.fromSpec_app_self, Category.assoc, ← Functor.map_comp]
  exact (congrArg _ ((congrArg _ (Subsingleton.elim _ _)).trans
    ((Spec Γ(X, U)).presheaf.map_id _))).trans (Category.comp_id _)

/-- Global sections of an affine chart `f : Spec R ⟶ Y` are natural in `R`: precomposing `f` with
`Spec.map φ` turns the induced map `Γ(Y, V) ⟶ R` into its composite with `φ`. -/
theorem _root_.AlgebraicGeometry.Scheme.Hom.appLE_ΓSpecIso_hom_naturality {R S : CommRingCat.{u}}
    {Y : Scheme.{u}} (f : Spec R ⟶ Y) {q : Spec S ⟶ Y} (φ : R ⟶ S) (h : q = Spec.map φ ≫ f)
    {V : Y.Opens} (e : ⊤ ≤ f ⁻¹ᵁ V) (e' : ⊤ ≤ q ⁻¹ᵁ V) :
    q.appLE V ⊤ e' ≫ (Scheme.ΓSpecIso S).hom =
      (f.appLE V ⊤ e ≫ (Scheme.ΓSpecIso R).hom) ≫ φ := by
  subst h
  -- `Scheme.Hom.appLE_eq_app` at `⊤` applies because `Spec.map φ ⁻¹ᵁ ⊤` is `⊤` by definition.
  have h : (Spec.map φ ≫ f).appLE V ⊤ e' = f.appLE V ⊤ e ≫ (Spec.map φ).appTop :=
    (Scheme.Hom.appLE_comp_appLE (Spec.map φ) f V ⊤ ⊤ e le_top).symm.trans
      (congrArg (f.appLE V ⊤ e ≫ ·) (Scheme.Hom.appLE_eq_app (Spec.map φ) (U := ⊤)))
  rw [h, Category.assoc, Category.assoc, Scheme.ΓSpecIso_naturality]

end

end

namespace Scheme

/-- The whole space is a nonempty open subset of a nonempty scheme. -/
public instance instNonemptyTop {X : Scheme.{u}} [Nonempty X] :
    Nonempty ((⊤ : X.Opens) : Type u) :=
  let ⟨x⟩ := ‹Nonempty X›
  ⟨⟨x, trivial⟩⟩

end Scheme

end AlgebraicGeometry

end TauCeti

end CartierSource02

/-! ## Unchanged proof bodies from `TauCeti.AlgebraicGeometry.Modules.RationalFunctions`

Upstream commit: 6b896c7c411221eb78639e4be8ead6e479a62893.
Original SHA256: 437cfc0d764b25c0500b464eaee4897bd7ef36942fffe3d5de8c83bb4900558e.
Module/import commands alone are relocated; EOF scopes are closed explicitly.
-/
section CartierSource03
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/


/-!
# The sheaf of rational functions on an integral scheme

Mathlib defines the function field `X.functionField` of an irreducible scheme as the stalk of
its structure sheaf at the generic point, but it does not organize the rational functions into a
sheaf on `X`. On an integral scheme the sheaf of total quotient rings is the constant sheaf with
value `K(X)`, and the constant sheaf with value the stalk at the generic point is the pushforward
of the structure sheaf along the canonical morphism `Spec K(X) ⟶ X`: that morphism hits exactly
the generic point, and on an irreducible space an open subset contains the generic point as soon
as it is nonempty. This file takes that pushforward as the definition, which makes the sheaf
condition and the `𝒪_X`-module structure automatic.

## Main declarations

* `TauCeti.AlgebraicGeometry.Scheme.genericPoint_mem`, the elementary fact that every nonempty open
  subset of an irreducible scheme contains the generic point, and
  `TauCeti.AlgebraicGeometry.Scheme.germ_smul_functionField`, which says that a function on such
  a subset acts on the function field through its germ at any of its points;
* `TauCeti.AlgebraicGeometry.Scheme.fromSpecFunctionField`, the canonical morphism
  `Spec K(X) ⟶ X` from the spectrum of the function field, and
  `TauCeti.AlgebraicGeometry.Scheme.fromSpecFunctionField_preimage`: it pulls a nonempty open
  subset back to everything;
* `TauCeti.AlgebraicGeometry.Scheme.rationalFunctionsRing`, the sheaf `𝒦_X` as a sheaf of
  commutative rings, `TauCeti.AlgebraicGeometry.Scheme.rationalFunctions`, its underlying
  `𝒪_X`-module sheaf, and `TauCeti.AlgebraicGeometry.Scheme.rationalFunctionsSectionsEquiv`,
  the canonical identification of their sections;
* `TauCeti.AlgebraicGeometry.Scheme.toRationalFunctionsRing` and
  `TauCeti.AlgebraicGeometry.Scheme.toRationalFunctions`, the canonical morphisms from `𝒪_X`
  as ring and module sheaves, respectively;
* `TauCeti.AlgebraicGeometry.Scheme.rationalFunctionsRingEquiv`, the identification of the
  ring of sections over a nonempty open subset with `K(X)`, compatible with restriction maps,
  together with the constant-sheaf statements it gives for the ring sheaf,
  `TauCeti.AlgebraicGeometry.Scheme.isIso_rationalFunctionsRing_map` and
  `TauCeti.AlgebraicGeometry.Scheme.subsingleton_rationalFunctionsRing`;
* `TauCeti.AlgebraicGeometry.Scheme.rationalFunctionsEquiv`, the identification
  `Γ(𝒦_X, U) ≃ₗ[Γ(X, U)] K(X)` of its sections over a nonempty open subset with the function
  field, `TauCeti.AlgebraicGeometry.Scheme.rationalFunctionsEquiv_map`, the compatibility of
  these identifications with the restriction maps, and the two statements which say that `𝒦_X`
  really is the constant sheaf: `TauCeti.AlgebraicGeometry.Scheme.isIso_rationalFunctions_map`,
  the restriction maps between nonempty open subsets are isomorphisms, and
  `TauCeti.AlgebraicGeometry.Scheme.subsingleton_rationalFunctions`, the sections over an empty
  open subset vanish; together these give
  `TauCeti.AlgebraicGeometry.Scheme.isFlasque_rationalFunctions`;
* `TauCeti.AlgebraicGeometry.Scheme.rationalFunctionsHom`, the morphism extending compatible
  linear maps on nonempty opens, with its computation rule `rationalFunctionsHom_app` and
  injectivity criterion `rationalFunctionsHom_app_injective`;
* `TauCeti.AlgebraicGeometry.Scheme.rationalFunctionsMul`, multiplication by a rational function
  as an endomorphism of `𝒦_X`, obtained by pushing forward multiplication by the corresponding
  global function on `Spec K(X)`; `rationalFunctionsEquiv_rationalFunctionsMul_app` identifies it
  with multiplication on sections, and `rationalFunctionsMul_mul` and `rationalFunctionsMul_one`
  make it multiplicative, so that multiplying by a unit is an automorphism of `𝒦_X`
  (`rationalFunctionsMul_comp_inv` and `rationalFunctionsMul_inv_comp`);
* the module morphism `TauCeti.AlgebraicGeometry.Scheme.toRationalFunctions` is
  `X.germToFunctionField` on sections
  (`TauCeti.AlgebraicGeometry.Scheme.rationalFunctionsEquiv_toRationalFunctions_app`), is
  injective on sections over every open subset of an integral scheme
  (`TauCeti.AlgebraicGeometry.Scheme.toRationalFunctions_app_injective`), and is therefore a
  monomorphism;
* `TauCeti.AlgebraicGeometry.Scheme.exists_germToFunctionField_eq_of_forall_mem_range`: a
  rational function lying in the local ring at every point of a nonempty open subset `U` is
  regular on `U`.

The sheaf `𝒪_X(D)` attached to a Weil divisor is the submodule of `𝒦_X` cut out by an order
bound; it is built in `TauCeti/AlgebraicGeometry/WeilDivisor/Scheme/Sheaf.lean`, and the
multiplication endomorphisms above are what make it depend only on the divisor class of `D`.

Cartier divisors are the global sections of `𝒦_X^*/𝒪_X^*`, and the line bundle `𝒪_X(D)` attached
to a divisor is a subsheaf of `𝒦_X`; both need the sheaf `𝒦_X` and the inclusion `𝒪_X ⟶ 𝒦_X`
built here. On an integral scheme the sheaf of total quotient rings agrees
with this constant sheaf, so no generality is lost at that stage.

No formalization is vendored. The construction reuses Mathlib's `Scheme.functionField`,
`Scheme.germToFunctionField`, `Scheme.fromSpecStalk` with its computation of the closed point, of
the range and of the maps on sections, `Scheme.ΓSpecIso`, `Scheme.Modules.pushforward` and
`SheafOfModules.unitToPushforwardObjUnit`.
-/

public section

open CategoryTheory Limits TopologicalSpace AlgebraicGeometry Opposite

namespace TauCeti

namespace AlgebraicGeometry

universe u

noncomputable section

namespace Scheme

variable (X : Scheme.{u}) [IrreducibleSpace X]

/-- The canonical morphism `Spec K(X) ⟶ X` from the spectrum of the function field of an
irreducible scheme, that is, the morphism from the spectrum of the stalk at the generic point. -/
def fromSpecFunctionField : Spec X.functionField ⟶ X :=
  X.fromSpecStalk (genericPoint X)

variable {X}

/-- The generic point of an irreducible scheme lies in every nonempty open subset. -/
theorem genericPoint_mem (U : X.Opens) [Nonempty U] : genericPoint X ∈ U :=
  ((genericPoint_spec X).mem_open_set_iff U.isOpen).mpr (by simpa using ‹Nonempty U›)

/-- A function on a nonempty open subset `U` acts on the function field through its germ at any
point of `U`. -/
theorem germ_smul_functionField {U : X.Opens} [Nonempty U] {x : X} (hx : x ∈ U) (r : Γ(X, U))
    (f : X.functionField) : X.presheaf.germ U x hx r • f = r • f := by
  rw [Algebra.smul_def, Algebra.smul_def, Scheme.algebraMap_germ_eq_germToFunctionField,
    RingHom.algebraMap_toAlgebra]

instance instUniqueSpecFunctionField (X : Scheme.{u}) [IrreducibleSpace X] :
    Unique (Spec X.functionField) where
  default := IsLocalRing.closedPoint X.functionField
  uniq p := by
    -- The morphism `Spec 𝒪_{X, x} ⟶ X` is a preimmersion, hence injective on points, and its
    -- range consists of the points specializing to `x`. Only the generic point of an irreducible
    -- space specializes to the generic point, so the source has a single point.
    refine (X.fromSpecStalk (genericPoint X)).isEmbedding.injective ?_
    refine Eq.trans ?_ Scheme.fromSpecStalk_closedPoint.symm
    have hmem : X.fromSpecStalk (genericPoint X) p ∈
        Set.range (X.fromSpecStalk (genericPoint X)) := ⟨p, rfl⟩
    rw [Scheme.range_fromSpecStalk] at hmem
    have hclosure : closure ({genericPoint X} : Set X) ⊆
        closure ({X.fromSpecStalk (genericPoint X) p} : Set X) :=
      specializes_iff_closure_subset.mp hmem
    rw [genericPoint_closure] at hclosure
    exact ((genericPoint_spec X).eq (Set.univ_subset_iff.mp hclosure)).symm

/-- The sheaf of commutative rings underlying the rational-function sheaf: the pushforward of
the structure sheaf of `Spec K(X)` along `fromSpecFunctionField`. -/
def rationalFunctionsRing (X : Scheme.{u}) [IrreducibleSpace X] :
    TopCat.Sheaf CommRingCat X :=
  (TopCat.Sheaf.pushforward CommRingCat (fromSpecFunctionField X).base).obj
    (Spec X.functionField).sheaf

/-- The canonical morphism of sheaves of rings `𝒪_X ⟶ 𝒦_X`. -/
def toRationalFunctionsRing (X : Scheme.{u}) [IrreducibleSpace X] :
    X.sheaf ⟶ rationalFunctionsRing X where
  hom := (fromSpecFunctionField X).c

/-- The sheaf `𝒦_X` of rational functions on an integral scheme `X`: the constant sheaf with
value the function field, realized as the pushforward of the structure sheaf of `Spec K(X)`
along `TauCeti.AlgebraicGeometry.Scheme.fromSpecFunctionField`. -/
def rationalFunctions (X : Scheme.{u}) [IrreducibleSpace X] : X.Modules :=
  (Scheme.Modules.pushforward (fromSpecFunctionField X)).obj (SheafOfModules.unit _)

/-- The module sheaf and ring sheaf constructions of `𝒦_X` have canonically identified
sections. Their underlying additive presheaves are definitionally equal because both constructions
use Mathlib's pushforward of the structure sheaf. -/
def rationalFunctionsSectionsEquiv (X : Scheme.{u}) [IrreducibleSpace X] (U : X.Opens) :
    (Γ(rationalFunctions X, U) : Type u) ≃+
      ((rationalFunctionsRing X).presheaf.obj (.op U) : Type u) :=
  AddEquiv.refl _

/-- The identification between module-sheaf and ring-sheaf sections commutes with restriction
maps. -/
@[simp]
theorem rationalFunctionsSectionsEquiv_map {U V : X.Opens} (i : U ⟶ V)
    (s : Γ(rationalFunctions X, V)) :
    rationalFunctionsSectionsEquiv X U ((rationalFunctions X).presheaf.map i.op s) =
      (rationalFunctionsRing X).presheaf.map i.op (rationalFunctionsSectionsEquiv X V s) :=
  by
    unfold rationalFunctionsSectionsEquiv rationalFunctions rationalFunctionsRing
    rfl

/-- On a nonempty open subset, the morphism `Spec K(X) ⟶ X` acts on sections by the germ map to
the function field. -/
theorem fromSpecFunctionField_app (U : X.Opens) [Nonempty U] :
    (fromSpecFunctionField X).app U =
      X.germToFunctionField U ≫ (Scheme.ΓSpecIso X.functionField).inv ≫
        (Spec X.functionField).presheaf.map (homOfLE le_top).op :=
  Scheme.fromSpecStalk_app (genericPoint_mem U)

/-- The morphism `Spec K(X) ⟶ X` pulls every nonempty open subset back to the whole of
`Spec K(X)`, its source having a single point, which maps to the generic point. -/
@[simp]
theorem fromSpecFunctionField_preimage (U : X.Opens) [Nonempty U] :
    (fromSpecFunctionField X) ⁻¹ᵁ U = ⊤ := by
  apply top_unique
  intro p _
  apply TopologicalSpace.Opens.mem_map.mpr
  rw [Subsingleton.elim p (IsLocalRing.closedPoint X.functionField),
    fromSpecFunctionField, Scheme.fromSpecStalk_closedPoint]
  exact genericPoint_mem U

private def functionFieldSectionsIso (U : X.Opens) [Nonempty U] :
    Γ(Spec X.functionField, (fromSpecFunctionField X) ⁻¹ᵁ U) ≅ X.functionField :=
  ((Spec X.functionField).presheaf.mapIso
    (eqToIso (fromSpecFunctionField_preimage U)).op).symm ≪≫ Scheme.ΓSpecIso X.functionField

/-- The sections of the ring sheaf `𝒦_X` over a nonempty open subset are the function field,
as commutative rings. -/
def rationalFunctionsRingEquiv (U : X.Opens) [Nonempty U] :
    ((rationalFunctionsRing X).presheaf.obj (.op U) : Type u) ≃+* X.functionField :=
  (functionFieldSectionsIso U).commRingCatIsoToRingEquiv

private theorem app_comp_functionFieldSectionsIso (U : X.Opens) [Nonempty U] :
    (fromSpecFunctionField X).app U ≫ (functionFieldSectionsIso U).hom =
      X.germToFunctionField U := by
  rw [fromSpecFunctionField_app, functionFieldSectionsIso]
  simp only [Iso.trans_hom, Iso.symm_hom, Functor.mapIso_inv, Category.assoc]
  rw [← Functor.map_comp_assoc,
    Subsingleton.elim ((homOfLE le_top).op ≫
      (eqToIso (fromSpecFunctionField_preimage U)).op.inv) (𝟙 _)]
  simp

private theorem map_comp_functionFieldSectionsIso {U V : X.Opens} [Nonempty U] [Nonempty V]
    (i : U ⟶ V) :
    (Spec X.functionField).presheaf.map
        ((Opens.map (fromSpecFunctionField X).base).map i).op ≫
      (functionFieldSectionsIso U).hom = (functionFieldSectionsIso V).hom := by
  rw [functionFieldSectionsIso, functionFieldSectionsIso]
  simp only [Iso.trans_hom, Iso.symm_hom, Functor.mapIso_inv]
  rw [← Functor.map_comp_assoc,
    Subsingleton.elim (((Opens.map (fromSpecFunctionField X).base).map i).op ≫
      (eqToIso (fromSpecFunctionField_preimage U)).op.inv)
      (eqToIso (fromSpecFunctionField_preimage V)).op.inv]

/-- The ring equivalences identifying sections of `𝒦_X` with the function field commute with
restriction maps. -/
@[simp]
theorem rationalFunctionsRingEquiv_map {U V : X.Opens} [Nonempty U] [Nonempty V] (i : U ⟶ V)
    (s : (rationalFunctionsRing X).presheaf.obj (.op V)) :
    rationalFunctionsRingEquiv U ((rationalFunctionsRing X).presheaf.map i.op s) =
      rationalFunctionsRingEquiv V s := by
  unfold rationalFunctionsRing at s ⊢
  -- The presheaf of a pushforward evaluates on `U` as the source presheaf evaluates on its
  -- preimage. This normalization exposes that documented pushforward computation so that
  -- `map_comp_functionFieldSectionsIso` applies.
  change (functionFieldSectionsIso U).hom
    ((Spec X.functionField).presheaf.map
      ((Opens.map (fromSpecFunctionField X).base).map i).op
        (id s : Γ(Spec X.functionField, (fromSpecFunctionField X) ⁻¹ᵁ V))) =
          (functionFieldSectionsIso V).hom s
  rw [← CategoryTheory.ConcreteCategory.comp_apply, map_comp_functionFieldSectionsIso]
  rfl

/-- The sections of `𝒦_X` over a nonempty open subset `U` are the function field, as a module
over the functions on `U`. -/
def rationalFunctionsEquiv (U : X.Opens) [Nonempty U] :
    Γ(rationalFunctions X, U) ≃ₗ[Γ(X, U)] X.functionField :=
  { rationalFunctionsRingEquiv U with
    map_smul' r s := by
      -- The action of `Γ(X, U)` on the pushforward is multiplication after applying the map on
      -- sections, so multiplicativity of the identification reduces this to
      -- `app_comp_functionFieldSectionsIso`.
      -- The module-sheaf section type is definitionally the carrier of the corresponding
      -- pushforward ring section, which is the form used by that comparison lemma.
      change (functionFieldSectionsIso U).hom (r • s) =
        r • (functionFieldSectionsIso U).hom s
      have h : (functionFieldSectionsIso U).hom (r • s) =
          (functionFieldSectionsIso U).hom ((fromSpecFunctionField X).app U r *
            (id s : Γ(Spec X.functionField, (fromSpecFunctionField X) ⁻¹ᵁ U))) := rfl
      rw [h, map_mul, ← CategoryTheory.ConcreteCategory.comp_apply,
        app_comp_functionFieldSectionsIso, Algebra.smul_def]
      rfl
  }

/-- The module-sheaf identification with the function field is the ring-sheaf identification
transported across `rationalFunctionsSectionsEquiv`. -/
theorem rationalFunctionsEquiv_apply (U : X.Opens) [Nonempty U]
    (s : Γ(rationalFunctions X, U)) :
    rationalFunctionsEquiv U s =
      rationalFunctionsRingEquiv U (rationalFunctionsSectionsEquiv X U s) :=
  by
    unfold rationalFunctionsEquiv rationalFunctionsSectionsEquiv
    rfl

/-- The identifications of the sections of `𝒦_X` with the function field are compatible with the
restriction maps: `𝒦_X` is the constant sheaf. -/
@[simp]
theorem rationalFunctionsEquiv_map {U V : X.Opens} [Nonempty U] [Nonempty V] (i : U ⟶ V)
    (s : Γ(rationalFunctions X, V)) :
    rationalFunctionsEquiv U ((rationalFunctions X).presheaf.map i.op s) =
      rationalFunctionsEquiv V s := by
  rw [rationalFunctionsEquiv_apply, rationalFunctionsSectionsEquiv_map,
    rationalFunctionsRingEquiv_map, rationalFunctionsEquiv_apply]

section Hom

variable (M : X.Modules)
  (app : ∀ (U : X.Opens) [Nonempty U],
    M.val.obj (op U) ⟶ (rationalFunctions X).val.obj (op U))
  (happ : ∀ {U V : X.Opens} [Nonempty U] [Nonempty V] (i : V ⟶ U) (s : Γ(M, U)),
    app V (M.presheaf.map i.op s) = (rationalFunctions X).presheaf.map i.op (app U s))

/-- Compatible linear maps to rational functions on nonempty opens extend to a morphism of
module sheaves. On the empty open the component is the unique map to the zero module. -/
def rationalFunctionsHom : M ⟶ rationalFunctions X := by
  classical
  refine
    { val :=
      { app := fun U ↦ if hU : Nonempty U.unop then
          letI := hU
          app U.unop
        else 0
        naturality := ?_ } }
  intro U V i
  by_cases hV : Nonempty V.unop
  · let := hV
    have hU : Nonempty U.unop := ⟨⟨(Classical.choice hV).1,
      i.unop.le (Classical.choice hV).2⟩⟩
    let := hU
    simp only [dite_eq_left hU, dite_eq_left hV]
    ext s
    exact happ i.unop s
  · ext s
    exact TopCat.Presheaf.section_ext
      ⟨(rationalFunctions X).presheaf, (rationalFunctions X).isSheaf⟩
      V.unop _ _ fun x hx ↦ (hV ⟨⟨x, hx⟩⟩).elim

/-- The extension agrees with the supplied linear map on every nonempty open. -/
@[simp]
theorem rationalFunctionsHom_app (U : X.Opens) [Nonempty U] (s : Γ(M, U)) :
    (rationalFunctionsHom M app happ).app U s = app U s := by
  simp only [rationalFunctionsHom, Scheme.Modules.Hom.app,
    dite_eq_left (inferInstance : Nonempty U)]
  rfl

/-- Injectivity on nonempty opens implies injectivity of the extended morphism on all opens. -/
theorem rationalFunctionsHom_app_injective
    (hinj : ∀ (U : X.Opens) [Nonempty U], Function.Injective (app U)) (U : X.Opens) :
    Function.Injective ((rationalFunctionsHom M app happ).app U) := by
  intro s s' h
  by_cases hU : Nonempty U
  · let := hU
    rw [rationalFunctionsHom_app, rationalFunctionsHom_app] at h
    exact hinj U h
  · exact TopCat.Presheaf.section_ext ⟨M.presheaf, M.isSheaf⟩
      U s s' fun x hx ↦ (hU ⟨⟨x, hx⟩⟩).elim

end Hom

/-- The restriction maps of `𝒦_X` between nonempty open subsets are bijective. -/
theorem rationalFunctions_map_bijective {U V : X.Opens} [Nonempty U] [Nonempty V] (i : U ⟶ V) :
    Function.Bijective ((rationalFunctions X).presheaf.map i.op) := by
  constructor
  · intro a b hab
    refine (rationalFunctionsEquiv V).injective ?_
    rw [← rationalFunctionsEquiv_map i a, ← rationalFunctionsEquiv_map i b, hab]
  · intro t
    refine ⟨(rationalFunctionsEquiv V).symm (rationalFunctionsEquiv U t), ?_⟩
    refine (rationalFunctionsEquiv U).injective ?_
    rw [rationalFunctionsEquiv_map, LinearEquiv.apply_symm_apply]

/-- The restriction maps of `𝒦_X` between nonempty open subsets are isomorphisms. -/
instance isIso_rationalFunctions_map {U V : X.Opens} [Nonempty U] [Nonempty V] (i : U ⟶ V) :
    IsIso ((rationalFunctions X).presheaf.map i.op) :=
  (ConcreteCategory.isIso_iff_bijective _).mpr (rationalFunctions_map_bijective i)

/-- The restriction maps of the ring sheaf `𝒦_X` between nonempty open subsets are bijective. -/
theorem rationalFunctionsRing_map_bijective {U V : X.Opens} [Nonempty U] [Nonempty V]
    (i : U ⟶ V) :
    Function.Bijective ((rationalFunctionsRing X).presheaf.map i.op) := by
  have h : ⇑((rationalFunctionsRing X).presheaf.map i.op) =
      rationalFunctionsSectionsEquiv X U ∘ (rationalFunctions X).presheaf.map i.op ∘
        (rationalFunctionsSectionsEquiv X V).symm := by
    funext s
    rw [Function.comp_apply, Function.comp_apply, rationalFunctionsSectionsEquiv_map,
      AddEquiv.apply_symm_apply]
  rw [h]
  exact (rationalFunctionsSectionsEquiv X U).bijective.comp
    ((rationalFunctions_map_bijective i).comp (rationalFunctionsSectionsEquiv X V).symm.bijective)

/-- The restriction maps of the ring sheaf `𝒦_X` between nonempty open subsets are
isomorphisms. -/
instance isIso_rationalFunctionsRing_map {U V : X.Opens} [Nonempty U] [Nonempty V] (i : U ⟶ V) :
    IsIso ((rationalFunctionsRing X).presheaf.map i.op) :=
  (ConcreteCategory.isIso_iff_bijective _).mpr (rationalFunctionsRing_map_bijective i)

/-- The sheaf `𝒦_X` has no nonzero sections over an empty open subset. -/
theorem subsingleton_rationalFunctions (U : X.Opens) (hU : U = ⊥) :
    Subsingleton Γ(rationalFunctions X, U) := by
  subst hU
  have h : (fromSpecFunctionField X) ⁻¹ᵁ (⊥ : X.Opens) = ⊥ := by simp
  have : Subsingleton Γ(Spec X.functionField,
      (fromSpecFunctionField X) ⁻¹ᵁ (⊥ : X.Opens)) := by rw [h]; infer_instance
  exact this

/-- The ring sheaf `𝒦_X` has no nonzero sections over an empty open subset. -/
theorem subsingleton_rationalFunctionsRing (U : X.Opens) (hU : U = ⊥) :
    Subsingleton ((rationalFunctionsRing X).presheaf.obj (.op U)) :=
  haveI := subsingleton_rationalFunctions U hU
  (rationalFunctionsSectionsEquiv X U).symm.injective.subsingleton

/-- The sheaf `𝒦_X` of rational functions on an irreducible scheme is flasque: its restriction
maps between nonempty open subsets are bijective, and its sections over the empty open subset
vanish. -/
instance isFlasque_rationalFunctions : (rationalFunctions X).presheaf.IsFlasque where
  epi {U V} i := by
    rw [AddCommGrpCat.epi_iff_surjective]
    by_cases hV : V.unop = ⊥
    · have := subsingleton_rationalFunctions (X := X) V.unop hV
      exact fun t ↦ ⟨0, Subsingleton.elim _ _⟩
    · have hV := (Opens.ne_bot_iff_nonempty _).mp hV
      have : Nonempty V.unop := hV.to_subtype
      have : Nonempty U.unop := (hV.mono (leOfHom i.unop)).to_subtype
      exact (rationalFunctions_map_bijective (X := X) i.unop).surjective

/-- The canonical morphism `𝒪_X ⟶ 𝒦_X`; it is an inclusion when `X` is integral, by
`toRationalFunctions_app_injective`. -/
def toRationalFunctions (X : Scheme.{u}) [IrreducibleSpace X] :
    @Quiver.Hom X.Modules _ (SheafOfModules.unit X.ringCatSheaf) (rationalFunctions X) :=
  SheafOfModules.unitToPushforwardObjUnit (fromSpecFunctionField X).toRingCatSheafHom

/-- The morphisms of ring sheaves and module sheaves `𝒪_X ⟶ 𝒦_X` agree on sections. -/
@[simp]
theorem toRationalFunctionsRing_app (U : X.Opens) (r : Γ(X, U)) :
    rationalFunctionsSectionsEquiv X U (Scheme.Modules.Hom.app (toRationalFunctions X) U r) =
      (toRationalFunctionsRing X).hom.app (.op U) r := by
  exact SheafOfModules.unitToPushforwardObjUnit_val_app_apply
    (fromSpecFunctionField X).toRingCatSheafHom (X := .op U) r

/-- On a nonempty open subset, the inclusion `𝒪_X ⟶ 𝒦_X` is the germ map to the function
field. -/
@[simp]
theorem rationalFunctionsEquiv_toRationalFunctions_app (U : X.Opens) [Nonempty U]
    (r : Γ(X, U)) :
    rationalFunctionsEquiv U (Scheme.Modules.Hom.app (toRationalFunctions X) U r) =
      X.germToFunctionField U r := by
  exact ConcreteCategory.congr_hom (app_comp_functionFieldSectionsIso U) r

/-- A morphism from the structure sheaf to rational functions is multiplication by the
rational function obtained by evaluating the global section `1`. -/
theorem _root_.AlgebraicGeometry.Scheme.Modules.Hom.rationalFunctionsEquiv_app_unit
    (φ : @Quiver.Hom X.Modules _ (SheafOfModules.unit X.ringCatSheaf) (rationalFunctions X))
    (U : X.Opens) [Nonempty U] (a : Γ(X, U)) :
    rationalFunctionsEquiv U (Scheme.Modules.Hom.app φ U a) =
      X.germToFunctionField U a *
        rationalFunctionsEquiv ⊤ (Scheme.Modules.Hom.app φ ⊤ (1 : Γ(X, ⊤))) := by
  have hnat := φ.mapPresheaf.naturality_apply (homOfLE (le_top : U ≤ ⊤)).op (1 : Γ(X, ⊤))
  -- The unit module's restrictions and scalar action are those of the structure sheaf.
  have hres : Scheme.Modules.Hom.app φ U (1 : Γ(X, U)) =
      (rationalFunctions X).presheaf.map (homOfLE (le_top : U ≤ ⊤)).op
        (Scheme.Modules.Hom.app φ ⊤ (1 : Γ(X, ⊤))) := by
    change Scheme.Modules.Hom.app φ U (X.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op 1) =
      (rationalFunctions X).presheaf.map (homOfLE (le_top : U ≤ ⊤)).op
        (Scheme.Modules.Hom.app φ ⊤ (1 : Γ(X, ⊤))) at hnat
    simpa only [map_one] using hnat
  calc
    _ = rationalFunctionsEquiv U (a • Scheme.Modules.Hom.app φ U (1 : Γ(X, U))) := by
      have h := Scheme.Modules.Hom.app_smul φ a (1 : Γ(X, U))
      -- Scalar multiplication on the unit module is multiplication of regular functions.
      change Scheme.Modules.Hom.app φ U (a * (1 : Γ(X, U)) : Γ(X, U)) =
        a • Scheme.Modules.Hom.app φ U (1 : Γ(X, U)) at h
      rw [mul_one] at h
      exact congrArg (rationalFunctionsEquiv U) h
    _ = _ := by
      rw [map_smul, hres, rationalFunctionsEquiv_map, Algebra.smul_def,
        RingHom.algebraMap_toAlgebra]

section SectionsMul

/-- The action of a regular function on a section of `𝒦_X` is multiplication in the ring of
sections of `𝒦_X` by the image of that function. -/
theorem rationalFunctionsSectionsEquiv_smul (U : X.Opens) (r : Γ(X, U))
    (s : Γ(rationalFunctions X, U)) :
    rationalFunctionsSectionsEquiv X U (r • s) =
      (toRationalFunctionsRing X).hom.app (.op U) r * rationalFunctionsSectionsEquiv X U s :=
  (rfl)

variable (X) in
/-- Multiplication of two sections of `𝒦_X` over an open subset, as a bilinear map over the
regular functions there.

The product is computed in the ring of sections of the sheaf of rings underlying `𝒦_X`; over a
nonempty open subset it is multiplication in the function field, by
`rationalFunctionsEquiv_mulBilin`. -/
def rationalFunctionsMulBilin (U : X.Opens) :
    Γ(rationalFunctions X, U) →ₗ[Γ(X, U)] Γ(rationalFunctions X, U) →ₗ[Γ(X, U)]
      Γ(rationalFunctions X, U) :=
  LinearMap.mk₂ Γ(X, U)
    (fun s t ↦ (rationalFunctionsSectionsEquiv X U).symm
      (rationalFunctionsSectionsEquiv X U s * rationalFunctionsSectionsEquiv X U t))
    (fun s s' t ↦ (rationalFunctionsSectionsEquiv X U).injective (by simp [add_mul]))
    (fun r s t ↦ (rationalFunctionsSectionsEquiv X U).injective (by
      simp [rationalFunctionsSectionsEquiv_smul, mul_assoc]))
    (fun s t t' ↦ (rationalFunctionsSectionsEquiv X U).injective (by simp [mul_add]))
    (fun r s t ↦ (rationalFunctionsSectionsEquiv X U).injective (by
      simp [rationalFunctionsSectionsEquiv_smul, mul_left_comm]))

/-- The product of two sections of `𝒦_X` is their product in the ring of sections. -/
@[simp]
theorem rationalFunctionsSectionsEquiv_mulBilin (U : X.Opens)
    (s t : Γ(rationalFunctions X, U)) :
    rationalFunctionsSectionsEquiv X U (rationalFunctionsMulBilin X U s t) =
      rationalFunctionsSectionsEquiv X U s * rationalFunctionsSectionsEquiv X U t := by
  simp [rationalFunctionsMulBilin]

/-- Over a nonempty open subset, the product of two sections of `𝒦_X` is their product in the
function field. -/
@[simp]
theorem rationalFunctionsEquiv_mulBilin (U : X.Opens) [Nonempty U]
    (s t : Γ(rationalFunctions X, U)) :
    rationalFunctionsEquiv U (rationalFunctionsMulBilin X U s t) =
      rationalFunctionsEquiv U s * rationalFunctionsEquiv U t := by
  rw [rationalFunctionsEquiv_apply, rationalFunctionsSectionsEquiv_mulBilin, map_mul,
    rationalFunctionsEquiv_apply, rationalFunctionsEquiv_apply]

/-- Multiplying a section of `𝒦_X` by the image of a regular function is the action of that
function on the section. -/
@[simp]
theorem rationalFunctionsMulBilin_toRationalFunctions_app (U : X.Opens) (r : Γ(X, U))
    (s : Γ(rationalFunctions X, U)) :
    rationalFunctionsMulBilin X U
        (Scheme.Modules.Hom.app (toRationalFunctions X) U r) s = r • s := by
  apply (rationalFunctionsSectionsEquiv X U).injective
  rw [rationalFunctionsSectionsEquiv_mulBilin, toRationalFunctionsRing_app,
    rationalFunctionsSectionsEquiv_smul]

/-- Multiplication of sections of `𝒦_X` commutes with the restriction maps. -/
@[simp]
theorem rationalFunctionsMulBilin_map {U V : X.Opens} (i : V ⟶ U)
    (s t : Γ(rationalFunctions X, U)) :
    (rationalFunctions X).presheaf.map i.op (rationalFunctionsMulBilin X U s t) =
      rationalFunctionsMulBilin X V ((rationalFunctions X).presheaf.map i.op s)
        ((rationalFunctions X).presheaf.map i.op t) := by
  apply (rationalFunctionsSectionsEquiv X V).injective
  rw [rationalFunctionsSectionsEquiv_map, rationalFunctionsSectionsEquiv_mulBilin,
    rationalFunctionsSectionsEquiv_mulBilin, rationalFunctionsSectionsEquiv_map,
    rationalFunctionsSectionsEquiv_map, map_mul]

end SectionsMul

section Mul

variable (X)

/-- Multiplication by a rational function, as an endomorphism of `𝒦_X`.

It is the pushforward along `Spec K(X) ⟶ X` of multiplication by the corresponding global
function on `Spec K(X)`, so no sheaf-theoretic gluing is needed to build it. -/
def rationalFunctionsMul (f : X.functionField) :
    rationalFunctions X ⟶ rationalFunctions X := by
  let _ : Nonempty ((⊤ : X.Opens) : Type u) := instNonemptyTop
  exact (Scheme.Modules.pushforward (fromSpecFunctionField X)).map
    (Scheme.Modules.globalSectionsSmul (SheafOfModules.unit _)
      ((rationalFunctionsRingEquiv (X := X) ⊤).symm f))

variable {X}

/-- Multiplication by `f` really is multiplication by `f` on sections. -/
@[simp]
theorem rationalFunctionsEquiv_rationalFunctionsMul_app (f : X.functionField) (U : X.Opens)
    [Nonempty U] (s : Γ(rationalFunctions X, U)) :
    rationalFunctionsEquiv U (Scheme.Modules.Hom.app (rationalFunctionsMul X f) U s) =
      f * rationalFunctionsEquiv U s := by
  let _ : Nonempty ((⊤ : X.Opens) : Type u) := instNonemptyTop
  -- The pushforward of a scalar multiplication acts on sections over `U` as the scalar
  -- multiplication over the preimage of `U`, which is multiplication in the ring of sections.
  have hval : rationalFunctionsSectionsEquiv X U
      (Scheme.Modules.Hom.app (rationalFunctionsMul X f) U s) =
      (rationalFunctionsRing X).presheaf.map (homOfLE le_top).op
          (rationalFunctionsSectionsEquiv X ⊤ ((rationalFunctionsRingEquiv (X := X) ⊤).symm f)) *
        rationalFunctionsSectionsEquiv X U s :=
    congrArg (rationalFunctionsSectionsEquiv X U)
      (ConcreteCategory.congr_hom (Scheme.Modules.globalSectionsSmul_app
        (SheafOfModules.unit (Spec X.functionField).ringCatSheaf)
        ((rationalFunctionsRingEquiv (X := X) ⊤).symm f) (fromSpecFunctionField X ⁻¹ᵁ U)) s)
  rw [rationalFunctionsEquiv_apply, hval, map_mul, rationalFunctionsRingEquiv_map,
    ← rationalFunctionsEquiv_apply]
  congr 1
  exact (rationalFunctionsRingEquiv (X := X) ⊤).apply_symm_apply f

/-- Multiplication by a product is the composite of the two multiplications. -/
@[simp]
theorem rationalFunctionsMul_mul (f g : X.functionField) :
    rationalFunctionsMul X (f * g) = rationalFunctionsMul X g ≫ rationalFunctionsMul X f := by
  let _ : Nonempty ((⊤ : X.Opens) : Type u) := instNonemptyTop
  simp only [rationalFunctionsMul, map_mul]
  let M : (Spec X.functionField).Modules :=
    SheafOfModules.unit (Spec X.functionField).ringCatSheaf
  let F := Scheme.Modules.pushforward (fromSpecFunctionField X)
  let f' : Γ(Spec X.functionField, ⊤) := (rationalFunctionsRingEquiv (X := X) ⊤).symm f
  let g' : Γ(Spec X.functionField, ⊤) := (rationalFunctionsRingEquiv (X := X) ⊤).symm g
  -- Unfolding the local names here exposes the pushforward and scalar-multiplication wrappers;
  -- their laws can then be applied without reasoning sectionwise.
  change F.map (Scheme.Modules.globalSectionsSmul M (f' * g')) =
    F.map (Scheme.Modules.globalSectionsSmul M g') ≫
      F.map (Scheme.Modules.globalSectionsSmul M f')
  rw [Scheme.Modules.globalSectionsSmul_mul, Functor.map_comp]

/-- Multiplication by `1` is the identity. -/
@[simp]
theorem rationalFunctionsMul_one : rationalFunctionsMul X 1 = 𝟙 _ := by
  let _ : Nonempty ((⊤ : X.Opens) : Type u) := instNonemptyTop
  simp only [rationalFunctionsMul, map_one]
  let M : (Spec X.functionField).Modules :=
    SheafOfModules.unit (Spec X.functionField).ringCatSheaf
  let F := Scheme.Modules.pushforward (fromSpecFunctionField X)
  -- As above, this definitional change only exposes the pushforward and scalar-multiplication
  -- wrappers so their identity laws apply directly.
  change F.map (Scheme.Modules.globalSectionsSmul M 1) = 𝟙 _
  rw [Scheme.Modules.globalSectionsSmul_one]
  exact F.map_id M

/-- Multiplying by a unit `g` and then by `g⁻¹` is the identity on `𝒦_X`. -/
@[simp]
theorem rationalFunctionsMul_comp_inv (g : X.functionFieldˣ) :
    rationalFunctionsMul X (g : X.functionField) ≫
        rationalFunctionsMul X ((g⁻¹ : X.functionFieldˣ) : X.functionField) = 𝟙 _ := by
  rw [← rationalFunctionsMul_mul, g.inv_mul, rationalFunctionsMul_one]

/-- Multiplying by the inverse of a unit `g` and then by `g` is the identity on `𝒦_X`. -/
@[simp]
theorem rationalFunctionsMul_inv_comp (g : X.functionFieldˣ) :
    rationalFunctionsMul X ((g⁻¹ : X.functionFieldˣ) : X.functionField) ≫
        rationalFunctionsMul X (g : X.functionField) = 𝟙 _ := by
  rw [← rationalFunctionsMul_mul, g.mul_inv, rationalFunctionsMul_one]

/-- Multiplication by `g⁻¹` then `g` cancels on sections. -/
@[simp]
lemma rationalFunctionsMul_app_rationalFunctionsMul_inv_app (g : X.functionFieldˣ)
    (U : X.Opens) (s : Γ(rationalFunctions X, U)) :
    Scheme.Modules.Hom.app (rationalFunctionsMul X (g : X.functionField)) U
        (Scheme.Modules.Hom.app (rationalFunctionsMul X
          ((g⁻¹ : X.functionFieldˣ) : X.functionField)) U s) = s := by
  simpa only [Scheme.Modules.Hom.comp_app, ConcreteCategory.comp_apply,
    Scheme.Modules.Hom.id_app, ConcreteCategory.id_apply] using
    ConcreteCategory.congr_hom
      (congrArg (fun φ ↦ Scheme.Modules.Hom.app φ U) (rationalFunctionsMul_inv_comp g)) s

/-- Multiplication by `g` then `g⁻¹` cancels on sections. -/
@[simp]
lemma rationalFunctionsMul_inv_app_rationalFunctionsMul_app (g : X.functionFieldˣ)
    (U : X.Opens) (s : Γ(rationalFunctions X, U)) :
    Scheme.Modules.Hom.app (rationalFunctionsMul X
        ((g⁻¹ : X.functionFieldˣ) : X.functionField)) U
        (Scheme.Modules.Hom.app (rationalFunctionsMul X (g : X.functionField)) U s) = s := by
  simpa only [Scheme.Modules.Hom.comp_app, ConcreteCategory.comp_apply,
    Scheme.Modules.Hom.id_app, ConcreteCategory.id_apply] using
    ConcreteCategory.congr_hom
      (congrArg (fun φ ↦ Scheme.Modules.Hom.app φ U) (rationalFunctionsMul_comp_inv g)) s

end Mul

variable [IsIntegral X]

/-- The inclusion `𝒪_X ⟶ 𝒦_X` is injective on sections over every open subset: over a nonempty
one because the germ map to the function field of an integral scheme is injective, and over an
empty one because there are no nonzero functions there. -/
theorem toRationalFunctions_app_injective (U : X.Opens) :
    Function.Injective (Scheme.Modules.Hom.app (toRationalFunctions X) U) := by
  rcases U.1.eq_empty_or_nonempty with h | h
  · have hU : U = ⊥ := SetLike.ext' h
    have hsub : Subsingleton Γ(X, U) :=
      CommRingCat.subsingleton_of_isTerminal (X.sheaf.isTerminalOfEqEmpty hU)
    exact fun a b _ => Subsingleton.elim (id a : Γ(X, U)) (id b : Γ(X, U))
  · have : Nonempty U := by simpa using h
    intro a b hab
    have key : X.germToFunctionField U (id a : Γ(X, U)) =
        X.germToFunctionField U (id b : Γ(X, U)) := by
      rw [← rationalFunctionsEquiv_toRationalFunctions_app,
        ← rationalFunctionsEquiv_toRationalFunctions_app]
      exact congrArg _ hab
    exact X.germToFunctionField_injective U key

/-- **A locally regular rational function is regular.** On an integral scheme, a rational function
lying in the local ring `𝒪_{X,y}` at every point `y` of a nonempty open subset `U` is the germ of a
section of `𝒪_X` over `U`: inside the function field, `Γ(X, U)` is the intersection of the local
rings at the points of `U`. -/
theorem exists_germToFunctionField_eq_of_forall_mem_range {U : X.Opens} [Nonempty U]
    {f : X.functionField}
    (hf : ∀ y ∈ U, f ∈ (algebraMap (X.presheaf.stalk y) X.functionField).range) :
    ∃ a : Γ(X, U), X.germToFunctionField U a = f := by
  -- The generic point lies in every nonempty open subset, so germs there see every overlap.
  have hgen : ∀ V : X.Opens, Nonempty V → genericPoint X ∈ V := fun V _ ↦ genericPoint_mem V
  -- Every point of `U` has a neighbourhood inside `U` on which `f` is regular.
  have key : ∀ y : U, ∃ V : X.Opens, ∃ _ : (y : X) ∈ V, ∃ _ : V ≤ U,
      ∃ s : Γ(X, V), X.presheaf.germ V (genericPoint X) (hgen V ⟨⟨(y : X), ‹_›⟩⟩) s = f := by
    intro y
    obtain ⟨g, hgf⟩ := hf y y.2
    obtain ⟨W, hyW, s, hs⟩ := X.presheaf.exists_germ_eq g
    have hmem : (y : X) ∈ (W ⊓ U : X.Opens) := ⟨hyW, y.2⟩
    have hWU : Nonempty (W ⊓ U : X.Opens) := ⟨⟨(y : X), hmem⟩⟩
    -- Only needed as an instance, so that `algebraMap_germ_eq_germToFunctionField` applies at `W`.
    have : Nonempty W := ⟨⟨(y : X), hyW⟩⟩
    refine ⟨W ⊓ U, hmem, inf_le_right, X.presheaf.map (homOfLE inf_le_left).op s, ?_⟩
    rw [X.presheaf.germ_res_apply (homOfLE (inf_le_left : W ⊓ U ≤ W)) (genericPoint X)
      (hgen _ hWU) s, ← hgf, ← hs]
    exact (_root_.AlgebraicGeometry.Scheme.algebraMap_germ_eq_germToFunctionField X hyW s).symm
  choose V hyV hVU s hs using key
  -- The chosen local regular functions agree on overlaps, since they all have germ `f`.
  have hne : ∀ y : U, Nonempty (V y) := fun y ↦ ⟨⟨(y : X), hyV y⟩⟩
  have hcompat : TopCat.Presheaf.IsCompatible X.presheaf V s := by
    intro y z
    have hyz : Nonempty (V y ⊓ V z : X.Opens) :=
      ⟨⟨genericPoint X, hgen _ (hne y), hgen _ (hne z)⟩⟩
    refine X.germToFunctionField_injective (V y ⊓ V z) ?_
    rw [X.presheaf.germ_res_apply (Opens.infLELeft (V y) (V z)) (genericPoint X)
        (hgen _ hyz) (s y),
      X.presheaf.germ_res_apply (Opens.infLERight (V y) (V z)) (genericPoint X)
        (hgen _ hyz) (s z)]
    exact (hs y).trans (hs z).symm
  obtain ⟨a, ha, -⟩ := X.sheaf.existsUnique_gluing' V U (fun y ↦ homOfLE (hVU y))
    (fun y hy ↦ Opens.mem_iSup.mpr ⟨⟨y, hy⟩, hyV ⟨y, hy⟩⟩) s hcompat
  obtain ⟨y⟩ := ‹Nonempty U›
  refine ⟨a, ?_⟩
  -- `ha` is phrased through `X.sheaf`, whose underlying presheaf is `X.presheaf`; naming the
  -- restriction identity with its `X.presheaf` type keeps the rewrites below type-correct.
  have hres : X.presheaf.map (homOfLE (hVU y)).op a = s y := ha y
  rw [← hs y, ← hres,
    X.presheaf.germ_res_apply (homOfLE (hVU y)) (genericPoint X) (hgen _ (hne y)) a]

/-- The morphism `𝒪_X ⟶ 𝒦_X` of ring sheaves is injective on sections over every open
subset of an integral scheme. -/
theorem toRationalFunctionsRing_app_injective (U : X.Opens) :
    Function.Injective ((toRationalFunctionsRing X).hom.app (.op U)) := by
  intro r s hrs
  apply toRationalFunctions_app_injective U
  apply (rationalFunctionsSectionsEquiv X U).injective
  exact (toRationalFunctionsRing_app U r).trans
    (hrs.trans (toRationalFunctionsRing_app U s).symm)

instance : Mono (toRationalFunctionsRing X).hom := by
  have hU : ∀ U : (Opens X)ᵒᵖ, Mono ((toRationalFunctionsRing X).hom.app U) := fun U =>
    ConcreteCategory.mono_of_injective _ (toRationalFunctionsRing_app_injective U.unop)
  exact NatTrans.mono_of_mono_app _

instance : Mono (toRationalFunctions X) := by
  have hU : ∀ U : (Opens X)ᵒᵖ,
      Mono (((Scheme.Modules.toPresheaf X).map (toRationalFunctions X)).app U) := fun U =>
    ConcreteCategory.mono_of_injective _ (toRationalFunctions_app_injective U.unop)
  exact (Scheme.Modules.toPresheaf X).mono_of_mono_map (NatTrans.mono_of_mono_app _)

end Scheme

end

end AlgebraicGeometry

end TauCeti

end
end CartierSource03

/-! ## Unchanged proof bodies from `TauCeti.CategoryTheory.Sites.Units`

Upstream commit: 6b896c7c411221eb78639e4be8ead6e479a62893.
Original SHA256: 602030b51354a002aec36d05301e0d2fbd111fda87fc6766618c52e322e292e2.
Module/import commands alone are relocated; EOF scopes are closed explicitly.
-/
section CartierSource04
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/


/-!
# The sheaf of units

This file constructs the sheaf of units of a sheaf of commutative rings. We regard the
multiplicative group of units additively, so that the result takes values in `AddCommGrpCat` and
can be used with kernels and cokernels in the abelian category of sheaves of abelian groups.

The construction is pointwise: the units functor is a right adjoint and therefore preserves the
limits in the sheaf condition. Thus a sheaf of commutative rings `F` gives a sheaf whose sections
over `U` are `Additive (F(U)ˣ)`.

The sections and the restriction maps of the resulting sheaf are computed by
`additiveUnitsFunctor_obj_obj` and `additiveUnitsFunctor_obj_map_apply`.

This is the categorical input for the Cartier-divisor sheaf
`𝒦_X^× / 𝒪_X^×` in `TauCeti/AlgebraicGeometry/CartierDivisor/Basic.lean`. No formalization is
vendored; the construction composes Mathlib's `CommMonCat.units`, the multiplicative-to-additive
equivalence, and `CategoryTheory.sheafCompose`.
-/

public section

open CategoryTheory

universe u v

namespace CommRingCat

/-- The functor from commutative rings to their groups of units, written additively. -/
abbrev additiveUnits : CommRingCat.{u} ⥤ AddCommGrpCat.{u} :=
  forget₂ CommRingCat CommMonCat ⋙ CommMonCat.units ⋙ commGroupAddCommGroupEquivalence.functor

end CommRingCat

namespace CategoryTheory.Sheaf

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)

/-- Taking the units of a sheaf of commutative rings, written additively. -/
noncomputable abbrev additiveUnitsFunctor :
    Sheaf J CommRingCat.{u} ⥤ Sheaf J AddCommGrpCat.{u} :=
  sheafCompose J CommRingCat.additiveUnits

/-- The sections of the additive units sheaf are the units of the original ring of sections. -/
@[simp]
lemma additiveUnitsFunctor_obj_obj (F : Sheaf J CommRingCat.{u}) (U : Cᵒᵖ) :
    ((additiveUnitsFunctor J).obj F).obj.obj U =
      AddCommGrpCat.of (Additive ((F.obj.obj U : CommRingCat.{u})ˣ)) :=
  rfl

/-- A morphism of additive units sheaves acts by applying the original ring morphism to a unit. -/
@[simp]
lemma additiveUnitsFunctor_map_app_apply {F G : Sheaf J CommRingCat.{u}} (f : F ⟶ G)
    (U : Cᵒᵖ) (x : Additive ((F.obj.obj U : CommRingCat.{u})ˣ)) :
    (@AddCommGrpCat.Hom.hom
      (AddCommGrpCat.of (Additive ((F.obj.obj U : CommRingCat.{u})ˣ)))
      (AddCommGrpCat.of (Additive ((G.obj.obj U : CommRingCat.{u})ˣ)))
      (((additiveUnitsFunctor J).map f).hom.app U)) x =
      Additive.ofMul (Units.map (f.hom.app U).hom.toMonoidHom (Additive.toMul x)) :=
  rfl

/-- Restricting a section of the additive units sheaf applies the restriction map of the
underlying sheaf of rings to the underlying unit. -/
@[simp]
lemma additiveUnitsFunctor_obj_map_apply (F : Sheaf J CommRingCat.{u}) {U V : Cᵒᵖ} (i : U ⟶ V)
    (x : Additive ((F.obj.obj U : CommRingCat.{u})ˣ)) :
    (@AddCommGrpCat.Hom.hom
      (AddCommGrpCat.of (Additive ((F.obj.obj U : CommRingCat.{u})ˣ)))
      (AddCommGrpCat.of (Additive ((F.obj.obj V : CommRingCat.{u})ˣ)))
      (((additiveUnitsFunctor J).obj F).obj.map i)) x =
      Additive.ofMul (Units.map (F.obj.map i).hom.toMonoidHom (Additive.toMul x)) :=
  rfl

end CategoryTheory.Sheaf

end
end CartierSource04

/-! ## Upstream proof bodies from `TauCeti.AlgebraicGeometry.CartierDivisor.Basic` (compatibility edits recorded)

Upstream commit: 6b896c7c411221eb78639e4be8ead6e479a62893.
Original SHA256: 8c6f1661a286312a25949ba634941736f94ea89ba40d02d3fd7ee15905a8b25d.
Module/import commands are relocated; EOF scopes are closed explicitly.
Target-version compatibility edits are recorded in
`audit/toric_power/scheme_pass1_repairs.json`; these bodies are not yet verified.
-/
section CartierSource05
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/


/-!
# Cartier divisors on an integral scheme

Let `X` be an integral scheme and let `𝒦_X` be its sheaf of rational functions. The Cartier
divisor sheaf is the quotient

`𝒦_X^× / 𝒪_X^×`,

and a Cartier divisor is a global section of this quotient sheaf. The quotient is a sheaf
quotient, not the pointwise quotient of groups of sections: its sections are represented locally
by nonzero rational functions, with two representatives identified when their ratio is a regular
unit.

## Main declarations

* `Scheme.regularUnitSheaf` and `Scheme.rationalUnitSheaf` are the sheaves of units of `𝒪_X` and
  `𝒦_X`, written additively;
* `Scheme.toRationalUnitSheaf` is the monomorphism `𝒪_X^× ⟶ 𝒦_X^×`;
* `Scheme.cartierDivisorSheaf` is its cokernel in sheaves of abelian groups;
* `Scheme.CartierDivisor` is the additive group of global sections of that cokernel;
* `Scheme.rationalUnitClass` sends a nonzero rational function to its class in the
  Cartier-divisor sheaf over a nonempty open subset, its *local equation* there;
* `Scheme.principalCartierDivisor` sends a nonzero rational function to its principal Cartier
  divisor, the case of the whole space.

The rational-function sheaf is constructed in
`TauCeti/AlgebraicGeometry/Modules/RationalFunctions.lean`; the line bundle `𝒪_X(D)` of a Cartier
divisor is constructed in `TauCeti/AlgebraicGeometry/CartierDivisor/Sheaf.lean`.

The definition follows the Stacks Project, *Divisors* (Tag 02AR). No formalization is vendored.
The sheaf quotient is Mathlib's categorical cokernel in the abelian category of sheaves of
abelian groups.
-/

@[expose] public section

open CategoryTheory Limits TopologicalSpace AlgebraicGeometry Opposite

namespace TauCeti

namespace AlgebraicGeometry

universe u

noncomputable section

namespace Scheme

variable (X : Scheme.{u}) [IsIntegral X]

/-- The sheaf `𝒪_X^×` of regular units, regarded as a sheaf of additive commutative groups. -/
noncomputable abbrev regularUnitSheaf : TopCat.Sheaf AddCommGrpCat.{u} X :=
  (CategoryTheory.Sheaf.additiveUnitsFunctor (Opens.grothendieckTopology X)).obj X.sheaf

/-- The sheaf `𝒦_X^×` of nonzero rational functions, regarded as a sheaf of additive
commutative groups. -/
noncomputable abbrev rationalUnitSheaf : TopCat.Sheaf AddCommGrpCat.{u} X :=
  (CategoryTheory.Sheaf.additiveUnitsFunctor (Opens.grothendieckTopology X)).obj
    (rationalFunctionsRing X)

/-- The inclusion `𝒪_X^× ⟶ 𝒦_X^×` of regular units into nonzero rational functions. -/
def toRationalUnitSheaf : regularUnitSheaf X ⟶ rationalUnitSheaf X :=
  (CategoryTheory.Sheaf.additiveUnitsFunctor (Opens.grothendieckTopology X)).map
    (toRationalFunctionsRing X)

/-- The inclusion of regular units into rational units is injective on sections over every open
subset of an integral scheme. -/
theorem toRationalUnitSheaf_app_injective (U : X.Opens) :
    Function.Injective ((toRationalUnitSheaf X).hom.app (op U)) := by
  intro f g h
  apply Additive.toMul.injective
  apply Units.map_injective (toRationalFunctionsRing_app_injective U)
  exact congrArg Additive.toMul h

/-- The inclusion `𝒪_X^× ⟶ 𝒦_X^×` of regular units into rational units is a
monomorphism. -/
instance : Mono (toRationalUnitSheaf X) := by
  have hU : ∀ U : (Opens X)ᵒᵖ, Mono ((toRationalUnitSheaf X).hom.app U) := fun U ↦
    ConcreteCategory.mono_of_injective _ (toRationalUnitSheaf_app_injective X U.unop)
  have : Mono (toRationalUnitSheaf X).hom := NatTrans.mono_of_mono_app _
  exact Sheaf.Hom.mono_of_presheaf_mono _ _ (toRationalUnitSheaf X)

/-- The Cartier-divisor sheaf `𝒦_X^× / 𝒪_X^×`. This is the cokernel in the category of sheaves
of abelian groups, and hence is the sheafification of the pointwise quotient presheaf.

Use Mathlib's generic `cokernel.desc`, `cokernel.π_desc`, and cancellation through
`cokernel.π` for its universal property. -/
def cartierDivisorSheaf : TopCat.Sheaf AddCommGrpCat.{u} X :=
  cokernel (toRationalUnitSheaf X)

/-- The quotient projection `𝒦_X^× ⟶ 𝒦_X^× / 𝒪_X^×`. -/
def toCartierDivisorSheaf : rationalUnitSheaf X ⟶ cartierDivisorSheaf X :=
  cokernel.π (toRationalUnitSheaf X)

/-- The quotient projection to the Cartier-divisor sheaf is an epimorphism. -/
instance : Epi (toCartierDivisorSheaf X) := by
  dsimp only [toCartierDivisorSheaf]
  exact Cofork.IsColimit.epi (colimit.isColimit _)

/-- A regular unit has zero class in the Cartier-divisor sheaf. -/
@[reassoc (attr := simp)]
lemma toRationalUnitSheaf_comp_toCartierDivisorSheaf :
    toRationalUnitSheaf X ≫ toCartierDivisorSheaf X = 0 :=
  cokernel.condition (toRationalUnitSheaf X)

/-- The sequence from regular units to rational units and then to Cartier divisors is exact. -/
theorem exact_toRationalUnitSheaf_toCartierDivisorSheaf :
    (ShortComplex.mk (toRationalUnitSheaf X) (toCartierDivisorSheaf X)
      (toRationalUnitSheaf_comp_toCartierDivisorSheaf X)).Exact :=
  ShortComplex.exact_cokernel (toRationalUnitSheaf X)

/-- The group of Cartier divisors on `X`, defined as the global sections of
`𝒦_X^× / 𝒪_X^×`. -/
abbrev CartierDivisor : Type u :=
  ((cartierDivisorSheaf X).obj.obj (op (⊤ : X.Opens)) : Type u)

/-- The map on global sections induced by the quotient projection from `𝒦_X^×` to the
Cartier-divisor sheaf. Its source is the group of units of `Γ(X, 𝒦_X)`, written additively. -/
def toCartierDivisor :
    Additive (((rationalFunctionsRing X).presheaf.obj (op (⊤ : X.Opens)))ˣ) →+
      CartierDivisor X :=
  ((toCartierDivisorSheaf X).hom.app (op (⊤ : X.Opens))).hom

/-- A global regular unit maps to zero under the quotient map to Cartier divisors. -/
@[simp]
lemma toRationalUnitSheaf_app_comp_toCartierDivisor :
    (toCartierDivisor X).comp
        ((toRationalUnitSheaf X).hom.app (op (⊤ : X.Opens))).hom = 0 := by
  have h :
      (toRationalUnitSheaf X).hom ≫ (toCartierDivisorSheaf X).hom = 0 :=
    congrArg (fun f => f.hom) (toRationalUnitSheaf_comp_toCartierDivisorSheaf X)
  have h :
      (toRationalUnitSheaf X).hom.app (op (⊤ : X.Opens)) ≫
          (toCartierDivisorSheaf X).hom.app (op (⊤ : X.Opens)) = 0 :=
    congrArg (fun f => f.app (op (⊤ : X.Opens))) h
  have h := congrArg (fun f => f.hom) h
  exact h

local instance : Nonempty (⊤ : X.Opens) :=
  ⟨⟨Classical.choice (inferInstanceAs (Nonempty X)), by simp⟩⟩

/-- Over a nonempty open subset, the units of the rational-function sheaf are the units of the
function field. -/
def rationalUnitSectionsEquiv (U : X.Opens) [Nonempty U] :
    Additive (((rationalFunctionsRing X).presheaf.obj (op U))ˣ) ≃+
      Additive X.functionFieldˣ := by
  exact (Units.mapEquiv (rationalFunctionsRingEquiv U).toMulEquiv).toAdditive

/-- The rational-unit equivalence applies the rational-functions equivalence to a unit. -/
@[simp]
lemma rationalUnitSectionsEquiv_apply (U : X.Opens) [Nonempty U]
    (f : ((rationalFunctionsRing X).presheaf.obj (op U))ˣ) :
    rationalUnitSectionsEquiv X U (Additive.ofMul f) =
      Additive.ofMul (Units.map
        (rationalFunctionsRingEquiv U).toMonoidHom f) := by
  rfl

/-- The homomorphism from regular units on `U` to units of the function field induced by the
germ map at the generic point. -/
noncomputable def regularUnitToFunctionField (U : X.Opens) [Nonempty U] :
    ((X.presheaf.obj (op U)) : Type u)ˣ →* X.functionFieldˣ := by
  exact Units.map (X.germToFunctionField U).hom.toMonoidHom

/-- The map on regular units applies the germ map to the underlying section. -/
@[simp]
lemma regularUnitToFunctionField_apply (U : X.Opens) [Nonempty U]
    (f : ((X.presheaf.obj (op U)) : Type u)ˣ) :
    regularUnitToFunctionField X U f =
      Units.map (X.germToFunctionField U).hom.toMonoidHom f := by
  rfl

/-- The equivalence from rational units to function-field units carries the image of a regular
unit to the unit induced by its germ in the function field. -/
lemma rationalUnitSectionsEquiv_toRationalUnitSheaf_app (U : X.Opens) [Nonempty U]
    (f : ((X.presheaf.obj (op U)) : Type u)ˣ) :
    rationalUnitSectionsEquiv X U
        (((toRationalUnitSheaf X).hom.app (op U)).hom (Additive.ofMul f)) =
      Additive.ofMul (regularUnitToFunctionField X U f) := by
  have hunit :
      ((toRationalUnitSheaf X).hom.app (op U)).hom (Additive.ofMul f) =
        Additive.ofMul (Units.map
          ((toRationalFunctionsRing X).hom.app
            (op U)).hom.toMonoidHom f) :=
    CategoryTheory.Sheaf.additiveUnitsFunctor_map_app_apply
      (Opens.grothendieckTopology X) (toRationalFunctionsRing X)
        (op U) (Additive.ofMul f)
  rw [hunit, rationalUnitSectionsEquiv_apply, regularUnitToFunctionField_apply]
  apply congrArg Additive.ofMul
  apply Units.ext
  simp only [Units.coe_map]
  -- The units API exposes underlying values, while the rational-functions comparison
  -- theorems use the definitionally equal module-sheaf section type.
  change rationalFunctionsRingEquiv U
      ((toRationalFunctionsRing X).hom.app (op U) (f : Γ(X, U))) =
    X.germToFunctionField U f
  rw [← toRationalFunctionsRing_app, ← rationalFunctionsEquiv_apply,
    rationalFunctionsEquiv_toRationalFunctions_app]

/-- The class in the Cartier-divisor sheaf over a nonempty open subset `U` of a nonzero rational
function, regarded as a local equation there. The multiplicative group of the function field is
written additively in the domain. -/
def rationalUnitClass (U : X.Opens) [Nonempty U] :
    Additive X.functionFieldˣ →+ ((cartierDivisorSheaf X).obj.obj (op U) : Type u) :=
  (((toCartierDivisorSheaf X).hom.app (op U)).hom).comp
    (rationalUnitSectionsEquiv X U).symm.toAddMonoidHom

/-- Evaluating the rational-unit class applies the quotient map to the corresponding rational
unit section. -/
lemma rationalUnitClass_apply (U : X.Opens) [Nonempty U] (g : Additive X.functionFieldˣ) :
    rationalUnitClass X U g = ((toCartierDivisorSheaf X).hom.app (op U)).hom
      ((rationalUnitSectionsEquiv X U).symm g) :=
  AddMonoidHom.comp_apply _ _ _

/-- Restricting a rational unit to a smaller nonempty open subset does not change the underlying
nonzero rational function. -/
@[simp]
lemma rationalUnitSectionsEquiv_symm_restrict {U V : X.Opens} [Nonempty U] [Nonempty V]
    (h : V ≤ U) (g : Additive X.functionFieldˣ) :
    TopCat.Presheaf.restrictOpen (F := (rationalUnitSheaf X).obj)
        ((rationalUnitSectionsEquiv X U).symm g) V h =
      (rationalUnitSectionsEquiv X V).symm g := by
  apply (rationalUnitSectionsEquiv X V).injective
  rw [AddEquiv.apply_symm_apply]
  set t := (rationalUnitSectionsEquiv X U).symm g with ht
  have hgt : rationalUnitSectionsEquiv X U t = g := by
    rw [ht, AddEquiv.apply_symm_apply]
  have hgt' : g = Additive.ofMul (Units.map
      (rationalFunctionsRingEquiv U).toMonoidHom (Additive.toMul t)) := by
    rw [← hgt]
    exact rationalUnitSectionsEquiv_apply X U (Additive.toMul t)
  -- Restricting a unit of the rational-function sheaf restricts its underlying section.
  have hrestrict :
      TopCat.Presheaf.restrictOpen (F := (rationalUnitSheaf X).obj) t V h =
        Additive.ofMul (Units.map
          ((rationalFunctionsRing X).presheaf.map (homOfLE h).op).hom.toMonoidHom
            (Additive.toMul t)) :=
    CategoryTheory.Sheaf.additiveUnitsFunctor_obj_map_apply
      (Opens.grothendieckTopology X) (rationalFunctionsRing X) (homOfLE h).op t
  rw [hrestrict, hgt', rationalUnitSectionsEquiv_apply]
  refine congrArg Additive.ofMul (Units.ext ?_)
  simp

/-- The class of a nonzero rational function commutes with restriction to a smaller nonempty
open subset: a local equation stays a local equation. -/
@[simp]
lemma rationalUnitClass_restrict {U V : X.Opens} [Nonempty U] [Nonempty V] (h : V ≤ U)
    (g : Additive X.functionFieldˣ) :
    rationalUnitClass X U g |_ V = rationalUnitClass X V g := by
  rw [rationalUnitClass_apply]
  calc
    _ = ((toCartierDivisorSheaf X).hom.app (op V)).hom
          (TopCat.Presheaf.restrictOpen (F := (rationalUnitSheaf X).obj)
            ((rationalUnitSectionsEquiv X U).symm g) V h) :=
      (TopCat.Presheaf.map_restrict (toCartierDivisorSheaf X).hom h _).symm
    _ = _ := by rw [rationalUnitSectionsEquiv_symm_restrict, ← rationalUnitClass_apply]

set_option maxHeartbeats 800000 in
/-- A regular unit on `U` has zero Cartier-divisor class over `U`. -/
@[simp]
lemma rationalUnitClass_germToFunctionField_eq_zero (U : X.Opens) [Nonempty U]
    (f : ((X.presheaf.obj (op U)) : Type u)ˣ) :
    rationalUnitClass X U
      (Additive.ofMul (Units.map (X.germToFunctionField U).hom f)) = 0 := by
  have hsymm :
      (rationalUnitSectionsEquiv X U).symm
          (Additive.ofMul (regularUnitToFunctionField X U f)) =
        ((toRationalUnitSheaf X).hom.app (op U)).hom (Additive.ofMul f) := by
    apply (rationalUnitSectionsEquiv X U).injective
    rw [AddEquiv.apply_symm_apply]
    exact (rationalUnitSectionsEquiv_toRationalUnitSheaf_app X U f).symm
  have hzero :
      ((toCartierDivisorSheaf X).hom.app (op U)).hom
        (((toRationalUnitSheaf X).hom.app (op U)).hom (Additive.ofMul f)) = 0 := by
    have h :
        (toRationalUnitSheaf X).hom ≫ (toCartierDivisorSheaf X).hom = 0 :=
      congrArg (fun k => k.hom) (toRationalUnitSheaf_comp_toCartierDivisorSheaf X)
    have h :
        (toRationalUnitSheaf X).hom.app (op U) ≫
          (toCartierDivisorSheaf X).hom.app (op U) = 0 :=
      congrArg (fun k => k.app (op U)) h
    have h := congrArg (fun k => k.hom) h
    exact DFunLike.congr_fun h (Additive.ofMul f)
  change rationalUnitClass X U (Additive.ofMul (regularUnitToFunctionField X U f)) = 0
  rw [rationalUnitClass_apply, hsymm]
  exact hzero

/-- A nonzero rational function determines its principal Cartier divisor. The multiplicative
group of the function field is written additively in the domain. -/
def principalCartierDivisorAddHom : Additive X.functionFieldˣ →+ CartierDivisor X :=
  rationalUnitClass X ⊤

/-- The principal Cartier divisor of a nonzero rational function. -/
def principalCartierDivisor (f : X.functionFieldˣ) : CartierDivisor X :=
  principalCartierDivisorAddHom X (Additive.ofMul f)

/-- The principal-divisor homomorphism sends an additively written rational unit to its
principal Cartier divisor. -/
@[simp]
lemma principalCartierDivisorAddHom_apply (f : Additive X.functionFieldˣ) :
    principalCartierDivisorAddHom X f = principalCartierDivisor X f.toMul :=
  (rfl)

/-- The principal Cartier divisor of one is zero. -/
@[simp]
lemma principalCartierDivisor_one : principalCartierDivisor X 1 = 0 :=
  map_zero (principalCartierDivisorAddHom X)

/-- The principal Cartier divisor of a product is the sum of the principal Cartier divisors. -/
@[simp]
lemma principalCartierDivisor_mul (f g : X.functionFieldˣ) :
    principalCartierDivisor X (f * g) =
      principalCartierDivisor X f + principalCartierDivisor X g :=
  map_add (principalCartierDivisorAddHom X) (Additive.ofMul f) (Additive.ofMul g)

/-- The principal Cartier divisor of an inverse is the negation of the principal Cartier
divisor. -/
@[simp]
lemma principalCartierDivisor_inv (f : X.functionFieldˣ) :
    principalCartierDivisor X f⁻¹ = -principalCartierDivisor X f :=
  map_neg (principalCartierDivisorAddHom X) (Additive.ofMul f)

/-- A global regular unit has zero principal Cartier divisor. -/
@[simp]
lemma principalCartierDivisor_regularUnitToFunctionField
    (f : ((X.presheaf.obj (op (⊤ : X.Opens))) : Type u)ˣ) :
    principalCartierDivisor X
      (Units.map (X.germToFunctionField (⊤ : X.Opens)).hom f) = 0 :=
  rationalUnitClass_germToFunctionField_eq_zero X ⊤ f

/-- Restricting a principal Cartier divisor to a nonempty open subset gives the class of the same
rational function there: a principal divisor has a global equation. -/
lemma principalCartierDivisorAddHom_restrict (g : Additive X.functionFieldˣ) (U : X.Opens)
    [Nonempty U] :
    (principalCartierDivisorAddHom X g) |_ U = rationalUnitClass X U g :=
  rationalUnitClass_restrict X le_top g

/-- Restricting a principal Cartier divisor to a nonempty open subset gives the class of the same
rational function there. -/
@[simp]
lemma principalCartierDivisor_restrict (f : X.functionFieldˣ) (U : X.Opens) [Nonempty U] :
    (principalCartierDivisor X f) |_ U = rationalUnitClass X U (Additive.ofMul f) :=
  principalCartierDivisorAddHom_restrict X (Additive.ofMul f) U

end Scheme

end

end AlgebraicGeometry

end TauCeti

end
end CartierSource05

/-! ## Unchanged proof bodies from `TauCeti.AlgebraicGeometry.CartierDivisor.LocalEquations`

Upstream commit: 6b896c7c411221eb78639e4be8ead6e479a62893.
Original SHA256: f16590ce1b9fc47b5a90e5db4b24bbdbb7dcd3f6cdcf68f5f88f2d6237353ce3.
Module/import commands alone are relocated; EOF scopes are closed explicitly.
-/
section CartierSource06
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/


/-!
# Local equations for Cartier divisors

A Cartier divisor on an integral scheme is a section of the quotient sheaf
`𝒦_X^× / 𝒪_X^×`. This file extracts the local-equation description from that quotient:
every section is locally represented by a nonzero rational function, and two representatives
differ by a unique regular unit.

## Main declarations

* `Scheme.exists_local_equation` lifts a Cartier-divisor section to a rational unit on a
  neighbourhood of any chosen point;
* `Scheme.CartierDivisor.exists_local_equation_cover` chooses local equations on an open cover
  indexed by the points of the scheme;
* `Scheme.toCartierDivisorSheaf_app_eq_iff` characterizes equality of two representatives by
  their difference coming from a regular unit;
* `Scheme.CartierDivisor.existsUnique_transitionUnit` applies that characterization on the
  overlap of two local equations of a global Cartier divisor;
* `Scheme.rationalUnitClass_eq_rationalUnitClass_iff` restates it for nonzero rational functions:
  two of them have the same class over a nonempty open subset `U` exactly when they differ by a
  unit of `Γ(X, U)`;
* `Scheme.CartierDivisor.IsLocalEquationAt D x f`: `f` is a local equation of `D` at the point
  `x`; every point has one (`Scheme.CartierDivisor.exists_isLocalEquationAt`), two of them differ
  by a unit of the local ring `𝒪_{X,x}`
  (`Scheme.CartierDivisor.IsLocalEquationAt.exists_unit_mul_eq`), and they only depend on the
  divisor near `x` (`Scheme.CartierDivisor.isLocalEquationAt_congr`).

The sheaf `𝒪_X(D)` is built in `TauCeti/AlgebraicGeometry/CartierDivisor/Sheaf.lean` as the
subsheaf of `𝒦_X` cut out by the local equations, through
`Scheme.CartierDivisor.IsLocalEquationAt`. The transition units record how two local equations of
`D` change into one another on an overlap. The construction follows Hartshorne, *Algebraic
Geometry*, II.6, and the Stacks Project, *Divisors*, Tag 02AR. No formalization is vendored: local
lifting is Mathlib's
characterization of epimorphisms of sheaves as locally surjective maps, while the transition-unit
criterion uses left exactness of sections and the cokernel exact sequence.
-/

public section

open CategoryTheory Limits TopologicalSpace AlgebraicGeometry Opposite

namespace TauCeti

namespace AlgebraicGeometry

universe u

noncomputable section

namespace Scheme

variable (X : Scheme.{u}) [IsIntegral X]

/-- Every local Cartier-divisor section has a rational equation near each point of its domain.

The representative is a section of `𝒦_X^×` on a smaller open neighbourhood, and its image in
`𝒦_X^× / 𝒪_X^×` is the restriction of the given Cartier-divisor section. -/
theorem exists_local_equation {U : X.Opens}
    (D : ((cartierDivisorSheaf X).obj.obj (op U) : Type u)) (x : X) (hx : x ∈ U) :
    ∃ (V : X.Opens) (hVU : V ≤ U), x ∈ V ∧
      ∃ f : Additive (((rationalFunctionsRing X).presheaf.obj (op V))ˣ),
        ((toCartierDivisorSheaf X).hom.app (op V)).hom f = D |_ V := by
  have hlocal : TopCat.Presheaf.IsLocallySurjective (toCartierDivisorSheaf X).hom :=
    (TopCat.Sheaf.isLocallySurjective_iff_epi (toCartierDivisorSheaf X)).mpr inferInstance
  obtain ⟨V, hVU, ⟨f, hf⟩, hxV⟩ :=
    (TopCat.Presheaf.isLocallySurjective_iff (toCartierDivisorSheaf X).hom).mp hlocal
      U D x hx
  exact ⟨V, hVU, hxV, f, hf⟩

/-- Two rational-unit sections have the same image in the Cartier-divisor sheaf exactly when
their difference is the image of a regular unit.

The unit is unique by `toRationalUnitSheaf_app_injective`; the explicit existence-and-uniqueness
form is `existsUnique_regularUnit_sub_of_toCartierDivisorSheaf_app_eq`. Multiplication and
division of units are written as addition and subtraction because the unit sheaves are regarded
as sheaves of additive commutative groups. -/
theorem toCartierDivisorSheaf_app_eq_iff {U : X.Opens}
    (f g : Additive (((rationalFunctionsRing X).presheaf.obj (op U))ˣ)) :
    ((toCartierDivisorSheaf X).hom.app (op U)).hom f =
        ((toCartierDivisorSheaf X).hom.app (op U)).hom g ↔
      ∃ r : Additive (((X.presheaf.obj (op U)) : Type u)ˣ),
        ((toRationalUnitSheaf X).hom.app (op U)).hom r = f - g := by
  constructor
  · intro h
    let S : ShortComplex (TopCat.Sheaf AddCommGrpCat X) :=
      ShortComplex.mk (toRationalUnitSheaf X) (toCartierDivisorSheaf X)
        (toRationalUnitSheaf_comp_toCartierDivisorSheaf X)
    have hS : S.Exact := exact_toRationalUnitSheaf_toCartierDivisorSheaf X
    have hzero : ((toCartierDivisorSheaf X).hom.app (op U)).hom (f - g) = 0 :=
      (map_sub _ f g).trans (sub_eq_zero.mpr h)
    exact _root_.TopCat.Sheaf.sections_exact_of_left_exact hS (inferInstance : Mono S.f)
      (f - g) hzero
  · rintro ⟨r, hr⟩
    have hcomp := toRationalUnitSheaf_comp_toCartierDivisorSheaf X
    have happ := congrArg (fun k ↦ k.hom.app (op U)) hcomp
    have hrzero := ConcreteCategory.congr_hom happ r
    have hq_sub : ((toCartierDivisorSheaf X).hom.app (op U)).hom (f - g) = 0 :=
      (congrArg ((toCartierDivisorSheaf X).hom.app (op U)).hom hr.symm).trans hrzero
    apply sub_eq_zero.mp
    exact (map_sub _ f g).symm.trans hq_sub

/-- If two rational-unit sections represent the same Cartier divisor, there is a unique regular
unit whose image is their difference. In multiplicative notation, this says their ratio is a
unique regular unit. -/
theorem existsUnique_regularUnit_sub_of_toCartierDivisorSheaf_app_eq {U : X.Opens}
    (f g : Additive (((rationalFunctionsRing X).presheaf.obj (op U))ˣ))
    (h : ((toCartierDivisorSheaf X).hom.app (op U)).hom f =
      ((toCartierDivisorSheaf X).hom.app (op U)).hom g) :
    ∃! r : Additive (((X.presheaf.obj (op U)) : Type u)ˣ),
      ((toRationalUnitSheaf X).hom.app (op U)).hom r = f - g := by
  obtain ⟨r, hr⟩ := (toCartierDivisorSheaf_app_eq_iff X f g).mp h
  exact ⟨r, hr, fun s hs ↦ toRationalUnitSheaf_app_injective X U (hs.trans hr.symm)⟩

/-- Two nonzero rational functions have the same class in the Cartier-divisor sheaf over a
nonempty open subset `U` exactly when they differ by a unit of `Γ(X, U)`. -/
theorem rationalUnitClass_eq_rationalUnitClass_iff (U : X.Opens) [Nonempty U]
    (f g : X.functionFieldˣ) :
    rationalUnitClass X U (Additive.ofMul f) = rationalUnitClass X U (Additive.ofMul g) ↔
      ∃ r : Γ(X, U)ˣ, regularUnitToFunctionField X U r * g = f := by
  rw [rationalUnitClass_apply, rationalUnitClass_apply, toCartierDivisorSheaf_app_eq_iff]
  constructor
  · rintro ⟨r, hr⟩
    refine ⟨Additive.toMul r, Additive.ofMul.injective ?_⟩
    have h := (rationalUnitSectionsEquiv_toRationalUnitSheaf_app X U (Additive.toMul r)).symm.trans
      (congrArg (rationalUnitSectionsEquiv X U) hr)
    rw [map_sub, AddEquiv.apply_symm_apply, AddEquiv.apply_symm_apply] at h
    rw [ofMul_mul, h, sub_add_cancel]
  · rintro ⟨r, hr⟩
    refine ⟨Additive.ofMul r, (rationalUnitSectionsEquiv X U).injective ?_⟩
    refine (rationalUnitSectionsEquiv_toRationalUnitSheaf_app X U r).trans ?_
    rw [map_sub, AddEquiv.apply_symm_apply, AddEquiv.apply_symm_apply, ← hr, ofMul_mul,
      add_sub_cancel_right]

namespace CartierDivisor

/-- A global Cartier divisor admits an open cover carrying rational local equations.

The cover is indexed by the points of `X`, with the open indexed by `x` chosen to contain `x`.
The displayed supremum records that these opens cover the whole scheme. -/
theorem exists_local_equation_cover (D : CartierDivisor X) :
    ∃ (U : X → X.Opens)
      (f : ∀ x, Additive (((rationalFunctionsRing X).presheaf.obj (op (U x)))ˣ)),
      (∀ x, x ∈ U x) ∧ (⨆ x, U x) = ⊤ ∧ ∀ x,
        ((toCartierDivisorSheaf X).hom.app (op (U x))).hom (f x) = D |_ (U x) := by
  choose U _ hxU f hf using fun x ↦ exists_local_equation X D x (by simp)
  refine ⟨U, f, hxU, ?_, hf⟩
  apply top_unique
  intro x _
  exact Opens.mem_iSup.mpr ⟨x, hxU x⟩

/-- Two local equations of a global Cartier divisor determine a unique regular transition unit
on their overlap.

In multiplicative notation the displayed difference is the ratio `f / g`: the transition unit is
the regular unit by which the equation `g` must be multiplied to give `f` on `U ⊓ V`. -/
theorem existsUnique_transitionUnit (D : CartierDivisor X) {U V : X.Opens}
    (f : Additive (((rationalFunctionsRing X).presheaf.obj (op U))ˣ))
    (g : Additive (((rationalFunctionsRing X).presheaf.obj (op V))ˣ))
    (hf : ((toCartierDivisorSheaf X).hom.app (op U)).hom f = D |_ U)
    (hg : ((toCartierDivisorSheaf X).hom.app (op V)).hom g = D |_ V) :
    ∃! r : Additive (((X.presheaf.obj (op (U ⊓ V))) : Type u)ˣ),
      ((toRationalUnitSheaf X).hom.app (op (U ⊓ V))).hom r =
        f |_ (U ⊓ V) - g |_ (U ⊓ V) := by
  apply existsUnique_regularUnit_sub_of_toCartierDivisorSheaf_app_eq X
  calc
    _ = (((toCartierDivisorSheaf X).hom.app (op U)).hom f) |_ (U ⊓ V) :=
      TopCat.Presheaf.map_restrict (toCartierDivisorSheaf X).hom inf_le_left f
    _ = (D |_ U) |_ (U ⊓ V) := congrArg (fun s ↦ s |_ (U ⊓ V)) hf
    _ = D |_ (U ⊓ V) := TopCat.Presheaf.restrict_restrict _ _ _
    _ = (D |_ V) |_ (U ⊓ V) := (TopCat.Presheaf.restrict_restrict _ _ _).symm
    _ = (((toCartierDivisorSheaf X).hom.app (op V)).hom g) |_ (U ⊓ V) :=
      congrArg (fun s ↦ s |_ (U ⊓ V)) hg.symm
    _ = _ := (TopCat.Presheaf.map_restrict
      (toCartierDivisorSheaf X).hom inf_le_right g).symm

variable {X}

/-- A local equation over `V` restricts to a local equation over every nonempty open `W ≤ V`. -/
lemma rationalUnitClass_eq_of_le {D : CartierDivisor X} {V W : X.Opens} [Nonempty V]
    [Nonempty W] (hWV : W ≤ V) {f : X.functionFieldˣ}
    (hf : rationalUnitClass X V (Additive.ofMul f) = D |_ V) :
    rationalUnitClass X W (Additive.ofMul f) = D |_ W := by
  rw [← rationalUnitClass_restrict X hWV, hf, TopCat.Presheaf.restrict_restrict]

/-- A nonzero rational function `f` is a *local equation* of the Cartier divisor `D` at the point
`x` when `D` is the class of `f` over some open neighbourhood of `x`. -/
def IsLocalEquationAt (D : CartierDivisor X) (x : X) (f : X.functionFieldˣ) : Prop :=
  ∃ (V : X.Opens) (hx : x ∈ V),
    haveI : Nonempty V := ⟨⟨x, hx⟩⟩
    rationalUnitClass X V (Additive.ofMul f) = D |_ V

/-- Unfolding `IsLocalEquationAt`: `f` is a local equation of `D` at `x` exactly when `D` is the
class of `f` over some open neighbourhood of `x`. -/
lemma isLocalEquationAt_iff {D : CartierDivisor X} {x : X} {f : X.functionFieldˣ} :
    D.IsLocalEquationAt x f ↔ ∃ (V : X.Opens) (hx : x ∈ V),
      haveI : Nonempty V := ⟨⟨x, hx⟩⟩
      rationalUnitClass X V (Additive.ofMul f) = D |_ V :=
  Iff.rfl

/-- An equation of `D` over an open subset is a local equation at each of its points. -/
lemma isLocalEquationAt_of_rationalUnitClass_eq {D : CartierDivisor X} {V : X.Opens} [Nonempty V]
    {f : X.functionFieldˣ} (hf : rationalUnitClass X V (Additive.ofMul f) = D |_ V) {x : X}
    (hx : x ∈ V) : D.IsLocalEquationAt x f :=
  ⟨V, hx, hf⟩

/-- The product of local equations is a local equation of the sum of Cartier divisors. -/
lemma IsLocalEquationAt.mul {D E : CartierDivisor X} {x : X} {f g : X.functionFieldˣ}
    (hf : D.IsLocalEquationAt x f) (hg : E.IsLocalEquationAt x g) :
    (D + E).IsLocalEquationAt x (f * g) := by
  obtain ⟨V, hxV, hV⟩ := hf
  obtain ⟨W, hxW, hW⟩ := hg
  have hx : x ∈ V ⊓ W := ⟨hxV, hxW⟩
  have : Nonempty V := ⟨⟨x, hxV⟩⟩
  have : Nonempty W := ⟨⟨x, hxW⟩⟩
  have : Nonempty (V ⊓ W : X.Opens) := ⟨⟨x, hx⟩⟩
  refine ⟨V ⊓ W, hx, ?_⟩
  rw [ofMul_mul, map_add, rationalUnitClass_eq_of_le inf_le_left hV,
    rationalUnitClass_eq_of_le inf_le_right hW]
  simp only [TopCat.Presheaf.restrictOpen, TopCat.Presheaf.restrict, map_add]

/-- The inverse of a local equation is a local equation of the negative divisor. -/
lemma IsLocalEquationAt.inv {D : CartierDivisor X} {x : X} {f : X.functionFieldˣ}
    (hf : D.IsLocalEquationAt x f) : (-D).IsLocalEquationAt x f⁻¹ := by
  obtain ⟨V, hx, hV⟩ := hf
  have : Nonempty V := ⟨⟨x, hx⟩⟩
  refine ⟨V, hx, ?_⟩
  rw [ofMul_inv, map_neg, hV]
  simp only [TopCat.Presheaf.restrictOpen, TopCat.Presheaf.restrict, map_neg]

/-- One is a local equation of the zero Cartier divisor at every point. -/
lemma isLocalEquationAt_zero (x : X) : (0 : CartierDivisor X).IsLocalEquationAt x 1 := by
  have : Nonempty (⊤ : X.Opens) := ⟨⟨x, Opens.mem_top x⟩⟩
  refine ⟨⊤, Opens.mem_top x, ?_⟩
  simp

/-- A principal Cartier divisor has its defining rational function as a local equation. -/
lemma isLocalEquationAt_principalCartierDivisor (x : X) (f : X.functionFieldˣ) :
    (principalCartierDivisor X f).IsLocalEquationAt x f := by
  have : Nonempty (⊤ : X.Opens) := ⟨⟨x, Opens.mem_top x⟩⟩
  exact isLocalEquationAt_of_rationalUnitClass_eq
    (principalCartierDivisor_restrict X f ⊤).symm (Opens.mem_top x)

/-- Every Cartier divisor has a local equation at every point. -/
theorem exists_isLocalEquationAt (D : CartierDivisor X) (x : X) :
    ∃ f : X.functionFieldˣ, D.IsLocalEquationAt x f := by
  obtain ⟨V, hVU, hx, f, hf⟩ := exists_local_equation X D x (Opens.mem_top x)
  have : Nonempty V := ⟨⟨x, hx⟩⟩
  refine ⟨Additive.toMul (rationalUnitSectionsEquiv X V f), V, hx, ?_⟩
  rw [rationalUnitClass_apply]
  exact ((congrArg _ ((rationalUnitSectionsEquiv X V).symm_apply_apply f)).trans hf)

/-- Every point of an open subset has a smaller open neighbourhood on which `D` has a single
Cartier equation. -/
theorem exists_localEquation_le (D : CartierDivisor X) (U : X.Opens) {x : X} (hx : x ∈ U) :
    ∃ (V : X.Opens) (_hVU : V ≤ U) (hxV : x ∈ V) (g : X.functionFieldˣ),
      haveI : Nonempty V := ⟨⟨x, hxV⟩⟩
      rationalUnitClass X V (Additive.ofMul g) = D |_ V := by
  obtain ⟨g, hg⟩ := D.exists_isLocalEquationAt x
  obtain ⟨W, hxW, hg⟩ := isLocalEquationAt_iff.mp hg
  have : Nonempty W := ⟨⟨x, hxW⟩⟩
  have : Nonempty (U ⊓ W : X.Opens) := ⟨⟨x, hx, hxW⟩⟩
  exact ⟨U ⊓ W, inf_le_left, ⟨hx, hxW⟩, g,
    rationalUnitClass_eq_of_le inf_le_right hg⟩

/-- Two local equations of `D` at `x` differ by a unit of the local ring `𝒪_{X,x}`. -/
theorem IsLocalEquationAt.exists_unit_mul_eq {D : CartierDivisor X} {x : X}
    {f g : X.functionFieldˣ} (hf : D.IsLocalEquationAt x f) (hg : D.IsLocalEquationAt x g) :
    ∃ u : (X.presheaf.stalk x)ˣ,
      algebraMap (X.presheaf.stalk x) X.functionField u * g = f := by
  obtain ⟨V, hxV, hV⟩ := hf
  obtain ⟨W, hxW, hW⟩ := hg
  have : Nonempty V := ⟨⟨x, hxV⟩⟩
  have : Nonempty W := ⟨⟨x, hxW⟩⟩
  have hx : x ∈ V ⊓ W := ⟨hxV, hxW⟩
  have : Nonempty (V ⊓ W : X.Opens) := ⟨⟨x, hx⟩⟩
  obtain ⟨r, hr⟩ := (rationalUnitClass_eq_rationalUnitClass_iff X (V ⊓ W) f g).mp
    ((rationalUnitClass_eq_of_le inf_le_left hV).trans
      (rationalUnitClass_eq_of_le inf_le_right hW).symm)
  refine ⟨Units.map (X.presheaf.germ (V ⊓ W) x hx).hom.toMonoidHom r, ?_⟩
  rw [← hr, Units.val_mul, regularUnitToFunctionField_apply]
  exact congrArg (· * (g : X.functionField))
    (_root_.AlgebraicGeometry.Scheme.algebraMap_germ_eq_germToFunctionField X hx (r : Γ(X, V ⊓ W)))

/-- Whether `f * c` lies in the local ring at `x` does not depend on the choice of the local
equation `f` of `D` at `x`. -/
lemma IsLocalEquationAt.mul_mem_range_iff {D : CartierDivisor X} {x : X}
    {f g : X.functionFieldˣ} (hf : D.IsLocalEquationAt x f) (hg : D.IsLocalEquationAt x g)
    (c : X.functionField) :
    (f : X.functionField) * c ∈ (algebraMap (X.presheaf.stalk x) X.functionField).range ↔
      (g : X.functionField) * c ∈ (algebraMap (X.presheaf.stalk x) X.functionField).range := by
  obtain ⟨u, hu⟩ := hf.exists_unit_mul_eq hg
  have hu' : algebraMap (X.presheaf.stalk x) X.functionField ↑u⁻¹ * f = g := by
    rw [← hu, ← mul_assoc, ← map_mul, Units.inv_mul, map_one, one_mul]
  constructor
  · intro h
    rw [← hu', mul_assoc]
    exact Subring.mul_mem _ (RingHom.mem_range_self _ _) h
  · intro h
    rw [← hu, mul_assoc]
    exact Subring.mul_mem _ (RingHom.mem_range_self _ _) h

/-- Local equations only depend on the restriction of the divisor: divisors that agree on an open
subset `V` have the same local equations at the points of `V`. -/
lemma isLocalEquationAt_congr {D E : CartierDivisor X} {V : X.Opens} (h : D |_ V = E |_ V)
    {x : X} (hx : x ∈ V) (f : X.functionFieldˣ) :
    D.IsLocalEquationAt x f ↔ E.IsLocalEquationAt x f := by
  suffices key : ∀ {D E : CartierDivisor X}, D |_ V = E |_ V →
      D.IsLocalEquationAt x f → E.IsLocalEquationAt x f from ⟨key h, key h.symm⟩
  intro D E h ⟨W, hxW, hW⟩
  have : Nonempty W := ⟨⟨x, hxW⟩⟩
  have : Nonempty (W ⊓ V : X.Opens) := ⟨⟨x, hxW, hx⟩⟩
  refine isLocalEquationAt_of_rationalUnitClass_eq (V := W ⊓ V) ?_ ⟨hxW, hx⟩
  rw [rationalUnitClass_eq_of_le inf_le_left hW,
    ← TopCat.Presheaf.restrict_restrict (inf_le_right : W ⊓ V ≤ V) le_top D, h,
    TopCat.Presheaf.restrict_restrict]

end CartierDivisor

end Scheme

end

end AlgebraicGeometry

end TauCeti

end
end CartierSource06

/-! ## Recovered file CartierTensor

Source SHA256: 51dcd69113611a02a7346ed9b1a21703abcb4be6c3d96bdce337f87757587f61.
The original named source sections and every proof body follow unchanged.
-/

/-! Exact proof bodies split from the uncompiled SchemeCore candidate.
No proof is replaced by an assumption. See `third_party/TauCeti/scheme_split.json`.
Verification requires an ordinary successful compiler record for this exact file. -/

/-! ## Upstream proof bodies from `TauCeti.Algebra.Category.ModuleCat.Sheaf.Biproducts` (compatibility edits recorded)

Upstream commit: 6b896c7c411221eb78639e4be8ead6e479a62893.
Original SHA256: 96514bf80a21ff076bb5e7b7b65fb35293eef9fbbc9945e9877cd001f628dd5c.
Module/import commands are relocated; EOF scopes are closed explicitly.
Target-version compatibility edits are recorded in
`audit/toric_power/scheme_pass1_repairs.json`; these bodies are not yet verified.
-/
section CartierSource07
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/


/-!
# Finite biproducts of sheaves of modules

Sheaves of modules over a sheaf of rings form a preadditive category with finite coproducts, so
they have finite biproducts. These biproducts provide the finite direct sums used to construct
finite free sheaves and their monoidal duality.

## Main declaration

* `TauCeti.SheafOfModules.hasFiniteBiproducts`.
-/

public section

open CategoryTheory Limits

namespace TauCeti

universe u v₁ u₁

namespace SheafOfModules

variable {C : Type u₁} [Category.{v₁} C] {J : GrothendieckTopology C} (R : Sheaf J RingCat.{u})
  [HasWeakSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]

set_option synthInstance.maxHeartbeats 200000 in
/-- Sheaves of modules have finite biproducts, since they form a preadditive category with finite
coproducts. -/
instance hasFiniteBiproducts : HasFiniteBiproducts (SheafOfModules.{u} R) :=
  .of_hasFiniteCoproducts

end SheafOfModules

end TauCeti

end
end CartierSource07

/-! ## Unchanged proof bodies from `TauCeti.Algebra.Category.ModuleCat.Sheaf.Defs`

Upstream commit: 6b896c7c411221eb78639e4be8ead6e479a62893.
Original SHA256: 55bbe35d294c4307c3cde001f7745f301e024947ed8f0f15aa0595005e5e11fb.
Module/import commands alone are relocated; EOF scopes are closed explicitly.
-/
section CartierSource08
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/


/-!
# Basic definitions for sheaves of modules

This file collects the coefficient sheaf obtained by forgetting commutativity, the original
commutative-ring actions on its section modules, the counit
identifying the sheafification of the underlying presheaf of a sheaf of modules with that sheaf,
and the vanishing of every sheaf of modules over a sheaf of rings whose sections are trivial.

## Main declarations

* `SheafOfModules.ringCatSheaf` forgets commutativity in a sheaf of commutative rings;
* `SheafOfModules.isZero_of_forall_subsingleton`: sheaves of modules over a sheaf of rings all of
  whose rings of sections are trivial are zero objects;
* `SheafOfModules.sheafificationIso` identifies a sheaf of modules with the sheafification of its
  underlying presheaf, naturally (`SheafOfModules.sheafificationIso_inv_naturality`).

This supports `TauCetiRoadmap/JacobianChallenge/README.md`, Layer A, item "Invertible sheaves on a
scheme; the Picard group `Pic X` under `⊗`".
-/

public section

open CategoryTheory Category Limits

namespace TauCeti

universe u v v₁ u₁

noncomputable section

namespace SheafOfModules

variable {C : Type u₁} [Category.{v₁} C] {J : GrothendieckTopology C}

/-- Every sheaf of modules over a sheaf of rings all of whose rings of sections are trivial is a
zero object. -/
theorem isZero_of_forall_subsingleton {S : Sheaf J RingCat.{u}}
    (hS : ∀ W, Subsingleton (S.obj.obj W)) (N : SheafOfModules.{v} S) : IsZero N := by
  rw [IsZero.iff_id_eq_zero]
  apply SheafOfModules.hom_ext
  ext W x
  have := hS W
  have := Module.subsingleton (S.obj.obj W) (N.val.obj W)
  exact Subsingleton.elim _ _

variable [HasWeakSheafify J AddCommGrpCat.{v}] [J.WEqualsLocallyBijective AddCommGrpCat.{v}]

/-- The sheaf of rings underlying a sheaf of commutative rings on a site; the site-level
analogue of `AlgebraicGeometry.Scheme.ringCatSheaf`. -/
abbrev ringCatSheaf (R : Sheaf J CommRingCat.{u})
    [J.HasSheafCompose (forget₂ CommRingCat RingCat.{u})] : Sheaf J RingCat.{u} :=
  (sheafCompose J (forget₂ CommRingCat RingCat.{u})).obj R

/-- Sections of a sheaf of modules over the underlying ring sheaf retain the module action
of the original commutative ring of sections. -/
instance _root_.SheafOfModules.sectionModule
    {R : Sheaf J CommRingCat.{u}} [J.HasSheafCompose (forget₂ CommRingCat RingCat.{u})]
    (P : _root_.SheafOfModules.{v} (ringCatSheaf R)) (U : Cᵒᵖ) :
    Module (R.obj.obj U) (P.val.obj U) :=
  inferInstanceAs (Module ((ringCatSheaf R).obj.obj U) (P.val.obj U))

/-- Sheafifying the underlying presheaf of modules of a sheaf of `R`-modules `M`, for a sheaf of
rings `R`, recovers `M`; this is the counit of the sheafification adjunction. -/
def sheafificationIso (R : Sheaf J RingCat.{u}) (M : SheafOfModules.{v} R) :
    (PresheafOfModules.sheafification (R := R) (𝟙 R.obj)).obj M.val ≅ M :=
  (asIso (PresheafOfModules.sheafificationAdjunction (𝟙 R.obj)).counit).app M

/-- The forward map of `sheafificationIso` is the counit of the sheafification adjunction. -/
@[simp]
theorem sheafificationIso_hom (R : Sheaf J RingCat.{u}) (M : SheafOfModules.{v} R) :
    (sheafificationIso R M).hom =
      (PresheafOfModules.sheafificationAdjunction (𝟙 R.obj)).counit.app M := by
  simp only [sheafificationIso]
  rfl

/-- `sheafificationIso` is natural: its inverse intertwines a morphism of sheaves of modules with
the sheafification of the underlying morphism of presheaves of modules. -/
@[reassoc]
theorem sheafificationIso_inv_naturality {R : Sheaf J RingCat.{u}} {M N : SheafOfModules.{v} R}
    (f : M ⟶ N) :
    f ≫ (sheafificationIso R N).inv =
      (sheafificationIso R M).inv ≫ (PresheafOfModules.sheafification (𝟙 R.obj)).map f.val := by
  rw [Iso.comp_inv_eq, assoc, Iso.eq_inv_comp, sheafificationIso_hom, sheafificationIso_hom]
  exact ((PresheafOfModules.sheafificationAdjunction (𝟙 R.obj)).counit.naturality f).symm

/-- The inverse direction of `sheafificationIso_inv_naturality`. -/
@[reassoc]
theorem sheafificationIso_hom_naturality {R : Sheaf J RingCat.{u}} {M N : SheafOfModules.{v} R}
    (f : M ⟶ N) :
    (PresheafOfModules.sheafification (𝟙 R.obj)).map f.val ≫ (sheafificationIso R N).hom =
      (sheafificationIso R M).hom ≫ f := by
  rw [← cancel_epi (sheafificationIso R M).inv, Iso.inv_hom_id_assoc,
    ← Category.assoc, ← sheafificationIso_inv_naturality, Category.assoc,
    Iso.inv_hom_id, Category.comp_id]

end SheafOfModules

end


end TauCeti

end
end CartierSource08

/-! ## Unchanged proof bodies from `TauCeti.CategoryTheory.Monoidal.Braided.Adjunction`

Upstream commit: 6b896c7c411221eb78639e4be8ead6e479a62893.
Original SHA256: 014a64e26464cb4855ec42dca611e4efcb66a73160ded0a426e2cff98d26e769.
Module/import commands alone are relocated; EOF scopes are closed explicitly.
-/
section CartierSource09
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/


/-!
# Braiding and monoidal adjunctions

In a monoidal adjunction, a lax braided right adjoint makes the left adjoint's oplax tensor
map compatible with braiding. If the left adjoint is strong monoidal, it is therefore braided.
Conversely, a braided strong monoidal left adjoint gives its right adjoint a lax braided
structure.

These facts apply to sheafification and to the pullback--pushforward adjunction of modules.
-/

public section

open CategoryTheory MonoidalCategory BraidedCategory
  Functor.LaxMonoidal Functor.OplaxMonoidal

namespace TauCeti

universe v₁ v₂ u₁ u₂

variable {C : Type u₁} [Category.{v₁} C] [MonoidalCategory C] [BraidedCategory C]
  {D : Type u₂} [Category.{v₂} D] [MonoidalCategory D] [BraidedCategory D]
  {F : C ⥤ D} {G : D ⥤ C}

/-- The oplax tensor map of a left adjoint respects braiding when the lax tensor map of its
right adjoint does. No invertibility of the left adjoint's tensor map is required. -/
@[reassoc]
theorem _root_.CategoryTheory.Adjunction.map_braiding_hom_comp_δ (adj : F ⊣ G)
    [F.OplaxMonoidal] [G.LaxBraided] [adj.IsMonoidal] (X Y : C) :
    F.map (β_ X Y).hom ≫ δ F Y X =
      δ F X Y ≫ (β_ (F.obj X) (F.obj Y)).hom := by
  apply (adj.homEquiv _ _).injective
  simp only [Adjunction.homEquiv_unit, Functor.map_comp]
  rw [adj.unit_naturality_assoc, adj.unit_app_tensor_comp_map_δ,
    adj.unit_app_tensor_comp_map_δ_assoc, Functor.LaxBraided.braided]
  exact (braiding_naturality_assoc (adj.unit.app X) (adj.unit.app Y) _).symm

/-- A strong monoidal left adjoint of a lax braided right adjoint is braided, for compatible
monoidal structures. Its monoidal structure is the given structure on `F`. -/
@[instance_reducible]
def _root_.CategoryTheory.Adjunction.leftAdjointBraided (adj : F ⊣ G)
    [F.Monoidal] [G.LaxBraided] [adj.IsMonoidal] : F.Braided where
  toMonoidal := inferInstance
  braided X Y := by
    rw [← cancel_epi (δ F X Y)]
    simp only [Functor.Monoidal.δ_μ_assoc]
    rw [← adj.map_braiding_hom_comp_δ_assoc, Functor.Monoidal.δ_μ,
      Category.comp_id]

/-- The braided left adjoint retains its supplied monoidal structure. -/
@[simp]
theorem _root_.CategoryTheory.Adjunction.leftAdjointBraided_toMonoidal (adj : F ⊣ G)
    [hF : F.Monoidal] [G.LaxBraided] [adj.IsMonoidal] :
    adj.leftAdjointBraided.toMonoidal = hF :=
  (rfl)

/-- A braided strong monoidal left adjoint gives a compatible lax monoidal right adjoint a
lax braided structure, with the given lax monoidal structure on `G`. -/
@[instance_reducible]
def _root_.CategoryTheory.Adjunction.rightAdjointLaxBraided (adj : F ⊣ G)
    [F.Braided] [G.LaxMonoidal] [adj.IsMonoidal] : G.LaxBraided where
  toLaxMonoidal := inferInstance
  braided X Y := by
    apply (adj.homEquiv _ _).symm.injective
    simp only [Adjunction.homEquiv_counit, Functor.map_comp, Category.assoc]
    rw [adj.counit_naturality, adj.map_μ_comp_counit_app_tensor_assoc,
      adj.map_μ_comp_counit_app_tensor, Functor.map_braiding]
    simp only [Category.assoc, Functor.Monoidal.μ_δ_assoc]
    exact congrArg (δ F (G.obj X) (G.obj Y) ≫ ·)
      (braiding_naturality (adj.counit.app X) (adj.counit.app Y))

/-- The lax braided right adjoint retains its supplied lax monoidal structure. -/
@[simp]
theorem _root_.CategoryTheory.Adjunction.rightAdjointLaxBraided_toLaxMonoidal (adj : F ⊣ G)
    [F.Braided] [hG : G.LaxMonoidal] [adj.IsMonoidal] :
    adj.rightAdjointLaxBraided.toLaxMonoidal = hG :=
  (rfl)

end TauCeti

end
end CartierSource09

/-! ## Unchanged proof bodies from `TauCeti.LinearAlgebra.DirectSum.Finsupp`

Upstream commit: 6b896c7c411221eb78639e4be8ead6e479a62893.
Original SHA256: 30c130109acda23cf45eb9772198f67988acec44e6f2f9382c21031475b03989.
Module/import commands alone are relocated; EOF scopes are closed explicitly.
-/
section CartierSource10
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/


/-!
# Coefficients in a tensor product with a free module

Two facts about Mathlib's `TensorProduct.finsuppScalarLeft`, which identifies `(ι →₀ R) ⊗[R] N`
with `ι →₀ N` by taking coefficients against the standard basis.

## Main results

* `TensorProduct.finsuppScalarLeft_lTensor_apply`: taking coefficients is natural in `N`.
* `TensorProduct.sum_single_tmul_finsuppScalarLeft`: an element is the sum of its coefficients
  against the basis vectors.
-/

public section

namespace TensorProduct

variable {R : Type*} [CommSemiring R] {ι : Type*} [DecidableEq ι] {N N' : Type*}
  [AddCommMonoid N] [Module R N] [AddCommMonoid N'] [Module R N']

/-- The coefficients of `(1 ⊗ g) t` in `(ι →₀ R) ⊗ N'` are the images under `g` of the
coefficients of `t`. -/
@[simp]
lemma finsuppScalarLeft_lTensor_apply (g : N →ₗ[R] N') (t : (ι →₀ R) ⊗[R] N) (i : ι) :
    finsuppScalarLeft R N' ι (g.lTensor _ t) i = g (finsuppScalarLeft R N ι t i) := by
  induction t using TensorProduct.inductionOn with
  | tmul p n => simp
  | add a b ha hb => simp [ha, hb]

/-- An element of `(ι →₀ R) ⊗ N` is the sum of its coefficients against the basis vectors. -/
lemma sum_single_tmul_finsuppScalarLeft (t : (ι →₀ R) ⊗[R] N) :
    ∑ i ∈ (finsuppScalarLeft R N ι t).support,
      Finsupp.single i (1 : R) ⊗ₜ finsuppScalarLeft R N ι t i = t := by
  conv_rhs => rw [← (finsuppScalarLeft R N ι).symm_apply_apply t,
    ← Finsupp.sum_single (finsuppScalarLeft R N ι t)]
  simp [Finsupp.sum, finsuppScalarLeft_symm_apply_single]

end TensorProduct

end
end CartierSource10

/-! ## Unchanged proof bodies from `TauCeti.Algebra.Category.ModuleCat.Presheaf.IsMonoidalW`

Upstream commit: 6b896c7c411221eb78639e4be8ead6e479a62893.
Original SHA256: 5a37240b65f064d20856cd95b809e6e865cd0b1a4294b90282df40f87570159c.
Module/import commands alone are relocated; EOF scopes are closed explicitly.
-/
section CartierSource11
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/



/-!
# Local isomorphisms of presheaves of modules are stable under tensor products

Let `R` be a presheaf of commutative rings on a small site `(C, J)`. A morphism `f` of presheaves
of `R`-modules is a *local isomorphism* when its underlying morphism of presheaves of abelian
groups lies in `J.W`, i.e. becomes an isomorphism after sheafification. This file proves that the
sectionwise tensor product of presheaves of modules preserves local isomorphisms in each variable:
the morphism property `J.W.inverseImage (PresheafOfModules.toPresheaf _)` is monoidal.

This is the input needed to compare iterated sheafified tensor products of sheaves of modules:
sheafifying `M ⊗ N` before tensoring with `P` does not change the sheafification of the result.

## Main declarations

* `PresheafOfModules.isLocallySurjective_whiskerLeft`: tensoring with any presheaf of modules
  preserves local surjectivity;
* `PresheafOfModules.isLocallyInjective_free_whiskerLeft`: tensoring with a free presheaf of
  modules preserves local injectivity;
* `PresheafOfModules.inverseImage_W_toPresheaf_whiskerLeft` and
  `PresheafOfModules.inverseImage_W_toPresheaf_whiskerRight`: tensoring with any presheaf of
  modules preserves local isomorphisms;
* `PresheafOfModules.isMonoidal_inverseImage_W_toPresheaf`: the resulting `IsMonoidal` instance.

-/

public section

open CategoryTheory Limits MonoidalCategory Opposite TensorProduct

namespace TauCeti

universe v u

section Locality

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
  {R : Cᵒᵖ ⥤ CommRingCat.{u}}

/-- Tensoring with a presheaf of modules `P` preserves local surjectivity: a section of
`P ⊗ N'` is locally a sum of elementary tensors whose second factors lift along `f`. -/
theorem _root_.PresheafOfModules.isLocallySurjective_whiskerLeft
    (P : PresheafOfModulesOfCommRing.{u} R) {N N' : PresheafOfModulesOfCommRing.{u} R}
    (f : N ⟶ N') [Presheaf.IsLocallySurjective J ((PresheafOfModules.toPresheaf _).map f)] :
    Presheaf.IsLocallySurjective J ((PresheafOfModules.toPresheaf _).map (P ◁ f)) where
  imageSieve_mem {U} t := by
    -- Expose the sectionwise tensor product in order to use tensor-product induction.
    change (P.obj (op U) ⊗ N'.obj (op U) : ModuleCat _) at t
    induction t using TensorProduct.inductionOn with
    | tmul p n' =>
      refine J.superset_covering ?_
        (Presheaf.imageSieve_mem J ((PresheafOfModules.toPresheaf _).map f) n')
      rintro V g ⟨n, hn⟩
      refine ⟨P.map g.op p ⊗ₜ n, ?_⟩
      -- Expose the component of the whiskered morphism as a tensor product of module maps.
      change P.map g.op p ⊗ₜ f.app (op V) n = (P ⊗ N').map g.op (p ⊗ₜ n')
      -- Expose the underlying-presheaf components in the local lifting equation.
      change f.app (op V) n = N'.map g.op n' at hn
      rw [hn]
      rfl
    | add a b ha hb =>
      refine J.superset_covering ?_ (J.intersection_covering ha hb)
      rintro V g ⟨⟨a', ha'⟩, ⟨b', hb'⟩⟩
      exact ⟨a' + b', (map_add _ a' b').trans
        ((congrArg₂ (· + ·) ha' hb').trans (map_add _ a b).symm)⟩

/-- Tensoring with the free presheaf of modules on a presheaf of types `F` preserves local
injectivity. A section of `free F ⊗ N` killed by `free F ◁ f` has all its coefficients killed by
`f`, and these finitely many coefficients vanish together on a covering sieve. -/
theorem _root_.PresheafOfModules.isLocallyInjective_free_whiskerLeft (F : Cᵒᵖ ⥤ Type u)
    {N N' : PresheafOfModulesOfCommRing.{u} R} (f : N ⟶ N')
    [Presheaf.IsLocallyInjective J ((PresheafOfModules.toPresheaf _).map f)] :
    Presheaf.IsLocallyInjective J
      ((PresheafOfModules.toPresheaf _).map ((PresheafOfModules.free _).obj F ◁ f)) where
  equalizerSieve_mem {U} x y hxy := by
    classical
    let e := finsuppScalarLeft (R.obj U) (N.obj U) (F.obj U)
    let t : (F.obj U →₀ R.obj U) ⊗[R.obj U] N.obj U := x - y
    have ht : (f.app U).hom.lTensor _ t = 0 := (map_sub _ x y).trans (sub_eq_zero.2 hxy)
    have hz : ∀ z ∈ (e t).support, Presheaf.equalizerSieve
        (F := (PresheafOfModules.toPresheaf _).obj N) (e t z) 0 ∈ J U.unop := fun z _ ↦
      Presheaf.equalizerSieve_mem J ((PresheafOfModules.toPresheaf _).map f) _ _ <| by
        have := congrArg (fun s ↦ finsuppScalarLeft (R.obj U) (N'.obj U) (F.obj U) s z) ht
        simp only [finsuppScalarLeft_lTensor_apply, map_zero, Finsupp.coe_zero,
          Pi.zero_apply] at this
        exact this.trans (map_zero _).symm
    refine J.superset_covering ?_ (Finset.inf_induction (J.top_mem _)
      (fun _ h₁ _ h₂ ↦ J.intersection_covering h₁ h₂) hz)
    intro V g hg
    have hg' : ∀ z ∈ (e t).support, N.map g.op (e t z) = 0 := fun z hz ↦
      (Finset.inf_le (f := fun z ↦ Presheaf.equalizerSieve
        (F := (PresheafOfModules.toPresheaf _).obj N) (e t z) 0) hz g hg).trans (map_zero _)
    have key : ((PresheafOfModules.free _).obj F ⊗ N).map g.op t = 0 := by
      refine (congrArg _ (sum_single_tmul_finsuppScalarLeft t).symm).trans
        ((map_sum _ _ _).trans (Finset.sum_eq_zero fun z hz ↦ ?_))
      -- Expose the sectionwise tensor map in order to rewrite its second tensor factor.
      change _ ⊗ₜ N.map g.op (e t z) = 0
      exact (congrArg _ (hg' z hz)).trans (tmul_zero _ _)
    exact sub_eq_zero.1 ((map_sub _ x y).symm.trans key)

end Locality

variable {C : Type u} [SmallCategory C] (J : GrothendieckTopology C) {R : Cᵒᵖ ⥤ CommRingCat.{u}}

variable [HasWeakSheafify J AddCommGrpCat.{u}]

/-- Local isomorphisms of presheaves of modules are stable under every shape of colimits which
the forgetful functor to presheaves of abelian groups and sheafification preserve. -/
private lemma isStableUnderColimitsOfShape_inverseImage_W_toPresheaf (K : Type*) [Category K]
    [PreservesColimitsOfShape K (PresheafOfModules.toPresheaf.{u} (R ⋙ forget₂ _ _))]
    [PreservesColimitsOfShape K (presheafToSheaf J AddCommGrpCat.{u})] :
    MorphismProperty.IsStableUnderColimitsOfShape ((J.W (A := AddCommGrpCat.{u})).inverseImage
      (PresheafOfModules.toPresheaf (R ⋙ forget₂ _ _))) K where
  condition X₁ X₂ c₁ c₂ h₁ h₂ f hf φ hφ := by
    let G := PresheafOfModules.toPresheaf (R ⋙ forget₂ _ _) ⋙
      presheafToSheaf J AddCommGrpCat.{u}
    have : PreservesColimitsOfShape K G := comp_preservesColimitsOfShape _ _
    have hW : ∀ {M M' : PresheafOfModules.{u} (R ⋙ forget₂ _ _)} (g : M ⟶ M'),
        (J.W (A := AddCommGrpCat.{u})).inverseImage
          (PresheafOfModules.toPresheaf (R ⋙ forget₂ _ _)) g ↔ IsIso (G.map g) := fun g ↦ by
      rw [MorphismProperty.inverseImage_iff, J.W_eq_inverseImage_isomorphisms]
      rfl
    rw [hW]
    exact MorphismProperty.IsStableUnderColimitsOfShape.condition (W := .isomorphisms _)
      (X₁ ⋙ G) (X₂ ⋙ G) (G.mapCocone c₁) (G.mapCocone c₂) (isColimitOfPreserves G h₁)
      (isColimitOfPreserves G h₂) (Functor.whiskerRight f G) (fun k ↦ (hW _).1 (hf k))
      (G.map φ) (fun k ↦ by simp [G, ← Functor.map_comp, hφ])

/-- If tensoring with each term of a diagram preserves a local isomorphism `f`, then so does
tensoring with the colimit of the diagram. -/
private lemma inverseImage_W_toPresheaf_whiskerLeft_of_isColimit {K : Type*} [Category K]
    [PreservesColimitsOfShape K (PresheafOfModules.toPresheaf.{u} (R ⋙ forget₂ _ _))]
    [∀ N : PresheafOfModules.{u} (R ⋙ forget₂ _ _), PreservesColimitsOfShape K (tensorRight N)]
    {D : K ⥤ PresheafOfModules.{u} (R ⋙ forget₂ _ _)} {c : Cocone D} (hc : IsColimit c)
    {N N' : PresheafOfModules.{u} (R ⋙ forget₂ _ _)} (f : N ⟶ N')
    (hD : ∀ k, (J.W (A := AddCommGrpCat.{u})).inverseImage
      (PresheafOfModules.toPresheaf _) (D.obj k ◁ f)) :
    (J.W (A := AddCommGrpCat.{u})).inverseImage (PresheafOfModules.toPresheaf _) (c.pt ◁ f) :=
  (isStableUnderColimitsOfShape_inverseImage_W_toPresheaf J K).condition
    (D ⋙ tensorRight N) (D ⋙ tensorRight N')
    ((tensorRight N).mapCocone c) ((tensorRight N').mapCocone c) (isColimitOfPreserves _ hc)
    (isColimitOfPreserves _ hc) (Functor.whiskerLeft D ((tensoringRight _).map f)) hD
    (c.pt ◁ f) (fun _ ↦ (whisker_exchange _ _).symm)

variable [J.WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- Tensoring with a presheaf of modules on the left preserves local isomorphisms. -/
theorem _root_.PresheafOfModules.inverseImage_W_toPresheaf_whiskerLeft
    (P : PresheafOfModules.{u} (R ⋙ forget₂ _ _)) {N N' : PresheafOfModules.{u} (R ⋙ forget₂ _ _)}
    {f : N ⟶ N'}
    (hf : (J.W (A := AddCommGrpCat.{u})).inverseImage (PresheafOfModules.toPresheaf _) f) :
    (J.W (A := AddCommGrpCat.{u})).inverseImage (PresheafOfModules.toPresheaf _) (P ◁ f) := by
  rw [MorphismProperty.inverseImage_iff, J.W_iff_isLocallyBijective] at hf
  obtain ⟨_, _⟩ := hf
  have hfree (F : Cᵒᵖ ⥤ Type u) : (J.W (A := AddCommGrpCat.{u})).inverseImage
      (PresheafOfModules.toPresheaf _) ((PresheafOfModules.free _).obj F ◁ f) := by
    have := PresheafOfModules.isLocallySurjective_whiskerLeft J
      ((PresheafOfModules.free _).obj F) f
    have := PresheafOfModules.isLocallyInjective_free_whiskerLeft J F f
    exact J.W_of_isLocallyBijective _
  have hcoprod (M : PresheafOfModules.{u} (R ⋙ forget₂ _ _)) :
      (J.W (A := AddCommGrpCat.{u})).inverseImage (PresheafOfModules.toPresheaf _)
        (M.freeYonedaCoproduct ◁ f) :=
    inverseImage_W_toPresheaf_whiskerLeft_of_isColimit J (colimit.isColimit _) f
      fun _ ↦ hfree _
  exact inverseImage_W_toPresheaf_whiskerLeft_of_isColimit J
    P.isColimitFreeYonedaCoproductsCokernelCofork f (by rintro (_ | _) <;> exact hcoprod _)

/-- Tensoring with a presheaf of modules on the right preserves local isomorphisms. -/
theorem _root_.PresheafOfModules.inverseImage_W_toPresheaf_whiskerRight
    {N N' : PresheafOfModules.{u} (R ⋙ forget₂ _ _)} {f : N ⟶ N'}
    (hf : (J.W (A := AddCommGrpCat.{u})).inverseImage (PresheafOfModules.toPresheaf _) f)
    (P : PresheafOfModules.{u} (R ⋙ forget₂ _ _)) :
    (J.W (A := AddCommGrpCat.{u})).inverseImage (PresheafOfModules.toPresheaf _) (f ▷ P) :=
  (MorphismProperty.arrow_mk_iso_iff _ (Arrow.isoMk (β_ N P) (β_ N' P))).2
    (PresheafOfModules.inverseImage_W_toPresheaf_whiskerLeft J P hf)

/-- Local isomorphisms of presheaves of modules form a monoidal morphism property. -/
instance _root_.PresheafOfModules.isMonoidal_inverseImage_W_toPresheaf :
    MorphismProperty.IsMonoidal ((J.W (A := AddCommGrpCat.{u})).inverseImage
      (PresheafOfModules.toPresheaf.{u} (R ⋙ forget₂ _ _))) where
  whiskerLeft P _ _ _ hg := PresheafOfModules.inverseImage_W_toPresheaf_whiskerLeft J P hg
  whiskerRight _ hf P := PresheafOfModules.inverseImage_W_toPresheaf_whiskerRight J hf P

end TauCeti

end
end CartierSource11

/-! ## Unchanged proof bodies from `TauCeti.Algebra.Category.ModuleCat.Sheaf.TensorProduct.Basic`

Upstream commit: 6b896c7c411221eb78639e4be8ead6e479a62893.
Original SHA256: 83120e1f0d5ed09c689829f65a7d5bb411609815785d332f2583fac201dade55.
Module/import commands alone are relocated; EOF scopes are closed explicitly.
-/
section CartierSource12
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/


/-!
# Tensor products of sheaves of modules

Given a site `(C, J)` carrying a sheaf of commutative rings `R`, and two sheaves of
`R`-modules `M`, `N`, we construct their tensor product `M ⊗ N` as a sheaf of modules:
sectionwise one tensors the modules of sections over the rings of sections, and the
resulting presheaf of modules is sheafified. Mathlib already provides the sectionwise
symmetric monoidal structure on presheaves of modules over a presheaf of commutative
rings (`PresheafOfModules.Monoidal`, contributed at the AIM workshop "Formalising algebraic
geometry" of June 24–28, 2024, https://aimath.org/pastworkshops/alggeominlean.html); here
that structure is transported to presheaves of modules over the sheaf of rings underlying
`R` and combined with Mathlib's sheafification adjunction for presheaves of modules
(`PresheafOfModules.sheafification`). Nothing here is specific to schemes.

## Main declarations

* `SheafOfModules.tensorProduct R M N` is the sheafified tensor product of two sheaves of
  `R`-modules;
* `SheafOfModules.tensorProductIso R M N` is its defining identification with the
  sheafification of the sectionwise tensor product of the underlying presheaves of modules;
* `SheafOfModules.tensorProductCongrLeft/right` transport an isomorphism of one argument
  through the tensor product;
* `SheafOfModules.tensorProductUnitIsoLeft/right` identify `R ⊗ M` and `M ⊗ R` with `M`;
* `SheafOfModules.tensorProductComm` provides symmetry.

The site-level construction remains available on a scheme as
`SheafOfModules.tensorProduct X.sheaf`; the canonical tensor notation `M ⊗ N` and symmetric
monoidal structure on `X.Modules` are in
`TauCeti/AlgebraicGeometry/Modules/TensorProduct.lean`.
-/

public section

open CategoryTheory Category Limits MonoidalCategory Opposite

namespace TauCeti

universe u v₁ u₁

noncomputable section

variable {C : Type u₁} [Category.{v₁} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat RingCat.{u})]
variable [HasWeakSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
variable (R : Sheaf J CommRingCat.{u})

namespace SheafOfModules

/-- The monoidal category structure on presheaves of modules over the sheaf of rings
underlying a sheaf of commutative rings, obtained from Mathlib's monoidal structure on
presheaves of modules over a presheaf of commutative rings. -/
@[expose] instance instMonoidalPresheafOfModulesRingCatSheaf :
    MonoidalCategory (PresheafOfModules.{u} (ringCatSheaf R).obj) :=
  inferInstanceAs (MonoidalCategory (PresheafOfModules.{u}
    (R.obj ⋙ forget₂ CommRingCat RingCat.{u})))

/-- The symmetric category structure on presheaves of modules over the sheaf of rings
underlying a sheaf of commutative rings, obtained from Mathlib's symmetric structure on
presheaves of modules over a presheaf of commutative rings. -/
instance instSymmetricPresheafOfModulesRingCatSheaf :
    SymmetricCategory (PresheafOfModules.{u} (ringCatSheaf R).obj) :=
  inferInstanceAs (SymmetricCategory (PresheafOfModules.{u}
    (R.obj ⋙ forget₂ CommRingCat RingCat.{u})))

/-- The functor of sheafified tensor products with a fixed second argument:
it sends `M` to `M ⊗ N`. -/
def tensorProductRightFunctor (N : SheafOfModules.{u} (ringCatSheaf R)) :
    SheafOfModules.{u} (ringCatSheaf R) ⥤ SheafOfModules.{u} (ringCatSheaf R) :=
  (SheafOfModules.forget (ringCatSheaf R)).comp
    ((MonoidalCategory.tensorRight (C := PresheafOfModules.{u} (ringCatSheaf R).obj)
      N.val).comp (PresheafOfModules.sheafification (𝟙 (ringCatSheaf R).obj)))

/-- The functor of sheafified tensor products with a fixed first argument:
it sends `N` to `M ⊗ N`. -/
def tensorProductLeftFunctor (M : SheafOfModules.{u} (ringCatSheaf R)) :
    SheafOfModules.{u} (ringCatSheaf R) ⥤ SheafOfModules.{u} (ringCatSheaf R) :=
  (SheafOfModules.forget (ringCatSheaf R)).comp
    ((MonoidalCategory.tensorLeft (C := PresheafOfModules.{u} (ringCatSheaf R).obj)
      M.val).comp (PresheafOfModules.sheafification (𝟙 (ringCatSheaf R).obj)))

/-- The tensor product of two sheaves of `R`-modules: the sectionwise tensor product of
the underlying presheaves of modules, sheafified. -/
def tensorProduct (M N : SheafOfModules.{u} (ringCatSheaf R)) :
    SheafOfModules.{u} (ringCatSheaf R) :=
  (tensorProductRightFunctor R N).obj M

@[simp]
lemma tensorProduct_val (M N : SheafOfModules.{u} (ringCatSheaf R)) :
    (tensorProduct R M N).val =
      ((PresheafOfModules.sheafification (𝟙 (ringCatSheaf R).obj)).obj
        (M.val ⊗ N.val)).val := by
  simp only [tensorProduct, tensorProductRightFunctor]
  rfl

/-- The defining identification of the tensor product with the sheafification of the
sectionwise tensor product of the underlying presheaves of modules. -/
def tensorProductIso (M N : SheafOfModules.{u} (ringCatSheaf R)) :
    tensorProduct R M N ≅
      (PresheafOfModules.sheafification (𝟙 (ringCatSheaf R).obj)).obj (M.val ⊗ N.val) :=
  Iso.refl _

/-- An isomorphism of the first argument transports through the tensor product. -/
def tensorProductCongrLeft {M M' N : SheafOfModules.{u} (ringCatSheaf R)} (e : M ≅ M') :
    tensorProduct R M N ≅ tensorProduct R M' N :=
  (tensorProductRightFunctor R N).mapIso e

/-- An isomorphism of the second argument transports through the tensor product. -/
def tensorProductCongrRight {M N N' : SheafOfModules.{u} (ringCatSheaf R)} (e : N ≅ N') :
    tensorProduct R M N ≅ tensorProduct R M N' :=
  (tensorProductLeftFunctor R M).mapIso e

/-- Tensoring with the sheaf of rings itself (on the left) does nothing. -/
def tensorProductUnitIsoLeft (M : SheafOfModules.{u} (ringCatSheaf R)) :
    tensorProduct R (_root_.SheafOfModules.unit (ringCatSheaf R)) M ≅ M :=
  (tensorProductIso R _ M).symm ≪≫
    (PresheafOfModules.sheafification (𝟙 (ringCatSheaf R).obj)).mapIso (λ_ M.val) ≪≫
      sheafificationIso (ringCatSheaf R) M

/-- Tensoring with the sheaf of rings itself (on the right) does nothing. -/
def tensorProductUnitIsoRight (M : SheafOfModules.{u} (ringCatSheaf R)) :
    tensorProduct R M (_root_.SheafOfModules.unit (ringCatSheaf R)) ≅ M :=
  (tensorProductIso R M _).symm ≪≫
    (PresheafOfModules.sheafification (𝟙 (ringCatSheaf R).obj)).mapIso (ρ_ M.val) ≪≫
      sheafificationIso (ringCatSheaf R) M

/-- Symmetry of the tensor product of sheaves of `R`-modules. -/
def tensorProductComm (M N : SheafOfModules.{u} (ringCatSheaf R)) :
    tensorProduct R M N ≅ tensorProduct R N M :=
  (tensorProductIso R M N).symm ≪≫
    (PresheafOfModules.sheafification (𝟙 (ringCatSheaf R).obj)).mapIso (β_ M.val N.val) ≪≫
      tensorProductIso R N M

end SheafOfModules

end

end TauCeti

end
end CartierSource12

/-! ## Upstream proof bodies from `TauCeti.Algebra.Category.ModuleCat.Sheaf.TensorProduct.Monoidal` (compatibility edits recorded)

Upstream commit: 6b896c7c411221eb78639e4be8ead6e479a62893.
Original SHA256: 44d6267cbd777cf97504743010fb7d5c803bc70a9e24d3ada52fc0e09accc79d.
Module/import commands are relocated; EOF scopes are closed explicitly.
Target-version compatibility edits are recorded in
`audit/toric_power/scheme_pass1_repairs.json`; these bodies are not yet verified.
-/
section CartierSource13
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/


/-!
# The symmetric monoidal category of sheaves of modules

Let `R` be a sheaf of commutative rings on a small site `(C, J)`. This file equips the category of
sheaves of `R`-modules with a symmetric monoidal category structure whose tensor product is the
sheafification of the sectionwise tensor product of the underlying presheaves of modules, and
whose unit is `R` itself.

The structure is obtained by localization. Sheafification `PresheafOfModules ⥤ SheafOfModules`
is a localization functor with respect to the local isomorphisms of presheaves of modules
(Mathlib's `PresheafOfModules.sheafification` instance of `Functor.IsLocalization`), and local
isomorphisms are stable under the sectionwise tensor product
(`PresheafOfModules.isMonoidal_inverseImage_W_toPresheaf`). Mathlib's localized monoidal
structure `CategoryTheory.LocalizedMonoidal` (with its braided and symmetric refinements) then
provides the monoidal category structure, the coherence laws, and the braiding on the target of
the localization functor, for which sheafification is a braided monoidal functor.

## Main declarations

* `SheafOfModules.monoidalCategory` and `SheafOfModules.symmetricCategory`: the symmetric
  monoidal category structure on sheaves of `R`-modules;
* `SheafOfModules.tensorUnit_eq`: its unit is the sheaf of modules `R` itself;
* `SheafOfModules.sheafificationMonoidal` and `SheafOfModules.sheafificationBraided`:
  sheafification of presheaves of modules is a braided monoidal functor, whose unit comparison is
  `SheafOfModules.sheafificationUnitIso` (`SheafOfModules.sheafification_ε`);
* `SheafOfModules.tensorUnderlyingIso`: the identification of `M ⊗ N` with the sheafification of
  the sectionwise tensor product of the underlying presheaves of modules, natural in `M` and `N`
  (`SheafOfModules.tensorUnderlyingIso_naturality`) and compatible with the braiding and
  the unitors.
* `SheafOfModules.sheafificationForgetAdjunction`, `SheafOfModules.forgetLaxMonoidal`, and
  `SheafOfModules.forgetLaxBraided`:
  sheafification is left adjoint to the inclusion of sheaves of modules into presheaves of
  modules, which is therefore lax monoidal, with unit map the identity
  (`SheafOfModules.forget_ε`) and tensor map the unit of sheafification
  (`SheafOfModules.forget_μ`);
* `SheafOfModules.tensor_hom_ext`: morphisms out of `M ⊗ N` are determined by their restriction
  along that tensor map to the sectionwise tensor product.

The tensor object `M ⊗ N` and the sheaf `SheafOfModules.tensorProduct R M N` are both
sheafifications of `M.val ⊗ N.val`, through `tensorUnderlyingIso` and `tensorProductIso`
respectively.

The site is assumed small, with modules in the universe of its objects and morphisms, because the
stability of local isomorphisms under tensor products is established in that generality.
-/

public section

open CategoryTheory Category MonoidalCategory

namespace TauCeti

universe u

noncomputable section

variable {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat RingCat.{u})]
variable [HasWeakSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]

namespace SheafOfModules

variable (R : Sheaf J CommRingCat.{u})

/-- Local isomorphisms of presheaves of modules over the sheaf of rings underlying a sheaf of
commutative rings form a monoidal morphism property. -/
instance isMonoidal_inverseImage_W_toPresheaf :
    ((J.W (A := AddCommGrpCat.{u})).inverseImage
      (PresheafOfModules.toPresheaf.{u} (ringCatSheaf R).obj)).IsMonoidal :=
  PresheafOfModules.isMonoidal_inverseImage_W_toPresheaf J (R := R.obj)

/-- Sheafifying the unit presheaf of modules recovers the sheaf of modules `R` itself. This is
the unit datum from which the localized monoidal structure is built. -/
def sheafificationUnitIso :
    (PresheafOfModules.sheafification.{u} (𝟙 (ringCatSheaf R).obj)).obj
      (𝟙_ (PresheafOfModules.{u} (ringCatSheaf R).obj)) ≅
        _root_.SheafOfModules.unit (ringCatSheaf R) :=
  sheafificationIso (ringCatSheaf R) (_root_.SheafOfModules.unit _)

/-- The forward map of `sheafificationUnitIso` is the counit of the sheafification adjunction at
the sheaf of modules `R`. -/
theorem sheafificationUnitIso_hom :
    (sheafificationUnitIso R).hom =
      (PresheafOfModules.sheafificationAdjunction (𝟙 (ringCatSheaf R).obj)).counit.app
        (_root_.SheafOfModules.unit (ringCatSheaf R)) :=
  sheafificationIso_hom _ _

/-- The monoidal category structure on sheaves of `R`-modules: the tensor product is the
sheafification of the sectionwise tensor product, and the unit is `R`. It is the localized
monoidal structure along sheafification. -/
instance monoidalCategory : MonoidalCategory (SheafOfModules.{u} (ringCatSheaf R)) :=
  inferInstanceAs (MonoidalCategory (LocalizedMonoidal
    (PresheafOfModules.sheafification.{u} (𝟙 (ringCatSheaf R).obj))
    ((J.W (A := AddCommGrpCat.{u})).inverseImage
      (PresheafOfModules.toPresheaf.{u} (ringCatSheaf R).obj)) (sheafificationUnitIso R)))

/-- The symmetric monoidal category structure on sheaves of `R`-modules, whose braiding is
induced by the symmetry of the sectionwise tensor product. -/
instance symmetricCategory : SymmetricCategory (SheafOfModules.{u} (ringCatSheaf R)) :=
  inferInstanceAs (SymmetricCategory (LocalizedMonoidal
    (PresheafOfModules.sheafification.{u} (𝟙 (ringCatSheaf R).obj))
    ((J.W (A := AddCommGrpCat.{u})).inverseImage
      (PresheafOfModules.toPresheaf.{u} (ringCatSheaf R).obj)) (sheafificationUnitIso R)))

/-- The unit of the monoidal structure on sheaves of `R`-modules is `R` itself. -/
@[simp]
theorem tensorUnit_eq :
    𝟙_ (SheafOfModules.{u} (ringCatSheaf R)) = _root_.SheafOfModules.unit (ringCatSheaf R) :=
  rfl

/-- Sheafification of presheaves of modules is a monoidal functor. -/
instance sheafificationMonoidal :
    (PresheafOfModules.sheafification.{u} (𝟙 (ringCatSheaf R).obj)).Monoidal :=
  inferInstanceAs (Localization.Monoidal.toMonoidalCategory
    (PresheafOfModules.sheafification.{u} (𝟙 (ringCatSheaf R).obj))
    ((J.W (A := AddCommGrpCat.{u})).inverseImage
      (PresheafOfModules.toPresheaf.{u} (ringCatSheaf R).obj)) (sheafificationUnitIso R)).Monoidal

/-- Sheafification of presheaves of modules is a braided monoidal functor. -/
instance sheafificationBraided :
    (PresheafOfModules.sheafification.{u} (𝟙 (ringCatSheaf R).obj)).Braided :=
  inferInstanceAs (Localization.Monoidal.toMonoidalCategory
    (PresheafOfModules.sheafification.{u} (𝟙 (ringCatSheaf R).obj))
    ((J.W (A := AddCommGrpCat.{u})).inverseImage
      (PresheafOfModules.toPresheaf.{u} (ringCatSheaf R).obj)) (sheafificationUnitIso R)).Braided

/-- The unit comparison of the monoidal functor sheafification is the inverse of
`sheafificationUnitIso`. -/
@[simp]
theorem sheafification_ε :
    Functor.LaxMonoidal.ε (PresheafOfModules.sheafification.{u} (𝟙 (ringCatSheaf R).obj)) =
      (sheafificationUnitIso R).inv :=
  rfl

/-- The inverse unit comparison of the monoidal functor sheafification is
`sheafificationUnitIso`. -/
@[simp]
theorem sheafification_η :
    Functor.OplaxMonoidal.η (PresheafOfModules.sheafification.{u} (𝟙 (ringCatSheaf R).obj)) =
      (sheafificationUnitIso R).hom :=
  rfl

variable {R}

/-- The tensor product of two sheaves of `R`-modules is the sheafification of the sectionwise
tensor product of their underlying presheaves of modules. -/
def _root_.SheafOfModules.tensorUnderlyingIso (M N : SheafOfModules.{u} (ringCatSheaf R)) :
    M ⊗ N ≅ (PresheafOfModules.sheafification.{u} (𝟙 (ringCatSheaf R).obj)).obj
      (M.val ⊗ N.val) :=
  ((sheafificationIso _ M).symm ⊗ᵢ (sheafificationIso _ N).symm) ≪≫
    Functor.Monoidal.μIso _ M.val N.val

/-- The forward map of `tensorUnderlyingIso`: the inverses of `sheafificationIso` on both
factors, followed by the tensor map of sheafification. -/
theorem _root_.SheafOfModules.tensorUnderlyingIso_hom (M N : SheafOfModules.{u} (ringCatSheaf R)) :
    (M.tensorUnderlyingIso N).hom =
      ((sheafificationIso _ M).inv ⊗ₘ (sheafificationIso _ N).inv) ≫
        Functor.LaxMonoidal.μ (PresheafOfModules.sheafification.{u} (𝟙 (ringCatSheaf R).obj))
          M.val N.val := by
  simp [SheafOfModules.tensorUnderlyingIso]

/-- The inverse map of `tensorUnderlyingIso`: the inverse tensor map of sheafification, followed
by `sheafificationIso` on both factors. -/
theorem _root_.SheafOfModules.tensorUnderlyingIso_inv (M N : SheafOfModules.{u} (ringCatSheaf R)) :
    (M.tensorUnderlyingIso N).inv =
      Functor.OplaxMonoidal.δ (PresheafOfModules.sheafification.{u} (𝟙 (ringCatSheaf R).obj))
          M.val N.val ≫
        ((sheafificationIso _ M).hom ⊗ₘ (sheafificationIso _ N).hom) := by
  simp [SheafOfModules.tensorUnderlyingIso]

/-- `tensorUnderlyingIso` is natural: under it, the tensor product of two morphisms of sheaves of
modules is the sheafification of the sectionwise tensor product of their underlying morphisms. -/
@[reassoc]
theorem _root_.SheafOfModules.tensorUnderlyingIso_naturality
    {M M' N N' : SheafOfModules.{u} (ringCatSheaf R)} (f : M ⟶ M') (g : N ⟶ N') :
    (f ⊗ₘ g) ≫ (M'.tensorUnderlyingIso N').hom =
      (M.tensorUnderlyingIso N).hom ≫
        (PresheafOfModules.sheafification.{u} (𝟙 (ringCatSheaf R).obj)).map (f.val ⊗ₘ g.val) := by
  simp only [SheafOfModules.tensorUnderlyingIso, Iso.trans_hom, tensorIso_hom, Iso.symm_hom,
    Functor.Monoidal.μIso_hom, assoc]
  rw [tensorHom_comp_tensorHom_assoc, sheafificationIso_inv_naturality,
    sheafificationIso_inv_naturality, ← tensorHom_comp_tensorHom_assoc,
    Functor.LaxMonoidal.μ_natural]

/-- Under `tensorUnderlyingIso`, the braiding of sheaves of modules is the sheafification of the
braiding of the sectionwise tensor product. -/
@[reassoc]
theorem _root_.SheafOfModules.braiding_hom_tensorUnderlyingIso_hom
    (M N : SheafOfModules.{u} (ringCatSheaf R)) :
    (β_ M N).hom ≫ (N.tensorUnderlyingIso M).hom =
      (M.tensorUnderlyingIso N).hom ≫
        (PresheafOfModules.sheafification.{u} (𝟙 (ringCatSheaf R).obj)).map
          (β_ M.val N.val).hom := by
  simp only [SheafOfModules.tensorUnderlyingIso, Iso.trans_hom, tensorIso_hom, Iso.symm_hom,
    Functor.Monoidal.μIso_hom, BraidedCategory.braiding_naturality_assoc,
    Functor.Braided.braided, assoc]

/-- The left unitor of sheaves of modules is the sheafification of the left unitor of the
sectionwise tensor product, read through the unit comparison `sheafificationUnitIso`. -/
theorem _root_.SheafOfModules.leftUnitor_hom_eq (M : SheafOfModules.{u} (ringCatSheaf R)) :
    (λ_ M).hom = ((sheafificationUnitIso R).inv ⊗ₘ (sheafificationIso _ M).inv) ≫
      Functor.LaxMonoidal.μ (PresheafOfModules.sheafification.{u} (𝟙 (ringCatSheaf R).obj))
        (𝟙_ _) M.val ≫
      (PresheafOfModules.sheafification.{u} (𝟙 (ringCatSheaf R).obj)).map (λ_ M.val).hom ≫
        (sheafificationIso _ M).hom := by
  rw [Functor.Monoidal.map_leftUnitor, sheafification_η]
  simp only [assoc, Functor.Monoidal.μ_δ_assoc, tensorHom_def', ← comp_whiskerRight_assoc,
    Iso.inv_hom_id, id_whiskerRight, id_comp]
  -- The unit `SheafOfModules.unit` produced by the unit comparison is `𝟙_` by `tensorUnit_eq`.
  exact ((leftUnitor_naturality_assoc _ _).trans (by rw [Iso.inv_hom_id, comp_id])).symm

/-- The right unitor of sheaves of modules is the sheafification of the right unitor of the
sectionwise tensor product, read through the unit comparison `sheafificationUnitIso`. -/
theorem _root_.SheafOfModules.rightUnitor_hom_eq (M : SheafOfModules.{u} (ringCatSheaf R)) :
    (ρ_ M).hom = ((sheafificationIso _ M).inv ⊗ₘ (sheafificationUnitIso R).inv) ≫
      Functor.LaxMonoidal.μ (PresheafOfModules.sheafification.{u} (𝟙 (ringCatSheaf R).obj))
        M.val (𝟙_ _) ≫
      (PresheafOfModules.sheafification.{u} (𝟙 (ringCatSheaf R).obj)).map (ρ_ M.val).hom ≫
        (sheafificationIso _ M).hom := by
  rw [Functor.Monoidal.map_rightUnitor, sheafification_η]
  simp only [assoc, Functor.Monoidal.μ_δ_assoc, tensorHom_def, ← whiskerLeft_comp_assoc,
    Iso.inv_hom_id, whiskerLeft_id]
  -- The unit `SheafOfModules.unit` produced by the unit comparison is `𝟙_` by `tensorUnit_eq`.
  exact ((rightUnitor_naturality_assoc (C := SheafOfModules.{u} (ringCatSheaf R))
    (sheafificationIso _ M).inv (sheafificationIso _ M).hom).trans
      (by rw [Iso.inv_hom_id, comp_id])).symm

section Forget

variable (R)

/-- Sheafification of presheaves of modules is left adjoint to the inclusion
`SheafOfModules.forget` of sheaves of modules. This is Mathlib's
`PresheafOfModules.sheafificationAdjunction` along the identity of the sheaf of rings, whose
right adjoint `forget ⋙ restrictScalars (𝟙 _)` is definitionally `forget`. -/
@[expose] def sheafificationForgetAdjunction :
    PresheafOfModules.sheafification.{u} (𝟙 (ringCatSheaf R).obj) ⊣
      _root_.SheafOfModules.forget (ringCatSheaf R) :=
  PresheafOfModules.sheafificationAdjunction (𝟙 (ringCatSheaf R).obj)

/-- The counit of `sheafificationForgetAdjunction` at a sheaf of modules `M` is the
identification `sheafificationIso` of the sheafification of `M.val` with `M`. -/
lemma sheafificationForgetAdjunction_counit_app (M : SheafOfModules.{u} (ringCatSheaf R)) :
    (sheafificationForgetAdjunction R).counit.app M = (sheafificationIso _ M).hom :=
  (sheafificationIso_hom _ M).symm

/-- The inclusion of sheaves of modules into presheaves of modules is lax monoidal, as the right
adjoint of the monoidal functor sheafification. Its tensor map `M.val ⊗ N.val ⟶ (M ⊗ N).val` is
the unit of sheafification (`SheafOfModules.forget_μ`), and its unit map is the identity
(`SheafOfModules.forget_ε`). -/
instance forgetLaxMonoidal : (_root_.SheafOfModules.forget (ringCatSheaf R)).LaxMonoidal :=
  (sheafificationForgetAdjunction R).rightAdjointLaxMonoidal

/-- The inclusion of sheaves of modules into presheaves of modules respects symmetry, as the
right adjoint of braided monoidal sheafification. -/
instance forgetLaxBraided : (_root_.SheafOfModules.forget (ringCatSheaf R)).LaxBraided where
  toLaxMonoidal := forgetLaxMonoidal R
  braided M N := by
    have h := ((sheafificationForgetAdjunction R).rightAdjointLaxBraided).braided M N
    rw [Adjunction.rightAdjointLaxBraided_toLaxMonoidal] at h
    exact h

/-- The unit map of the inclusion of sheaves of modules into presheaves of modules is the
identity. -/
@[simp]
lemma forget_ε : Functor.LaxMonoidal.ε (_root_.SheafOfModules.forget (ringCatSheaf R)) = 𝟙 _ := by
  have h : (sheafificationUnitIso R).hom =
      (sheafificationForgetAdjunction R).counit.app (𝟙_ _) :=
    sheafificationUnitIso_hom R
  rw [forgetLaxMonoidal, Adjunction.rightAdjointLaxMonoidal_ε, sheafification_η, h]
  exact ((sheafificationForgetAdjunction R).homEquiv_unit _ _ _).trans
    ((sheafificationForgetAdjunction R).right_triangle_components (𝟙_ _))

/-- The tensor map `M.val ⊗ N.val ⟶ (M ⊗ N).val` of the inclusion of sheaves of modules into
presheaves of modules is the unit of sheafification, followed by the identification
`tensorUnderlyingIso` of `M ⊗ N` with the sheafification of `M.val ⊗ N.val`. -/
lemma forget_μ (M N : SheafOfModules.{u} (ringCatSheaf R)) :
    Functor.LaxMonoidal.μ (_root_.SheafOfModules.forget (ringCatSheaf R)) M N =
      (sheafificationForgetAdjunction R).unit.app (M.val ⊗ N.val) ≫
        (_root_.SheafOfModules.forget (ringCatSheaf R)).map (M.tensorUnderlyingIso N).inv := by
  rw [forgetLaxMonoidal, Adjunction.rightAdjointLaxMonoidal_μ, Adjunction.homEquiv_unit,
    SheafOfModules.tensorUnderlyingIso_inv, ← sheafificationForgetAdjunction_counit_app,
    ← sheafificationForgetAdjunction_counit_app]
  rfl

variable {R}

/-- A morphism out of `M ⊗ N`, precomposed on underlying presheaves with the tensor map
`M.val ⊗ N.val ⟶ (M ⊗ N).val` of `forget`, is the transpose along sheafification of the morphism
read through `tensorUnderlyingIso`. -/
lemma forget_μ_comp_map {M N P : _root_.SheafOfModules.{u} (ringCatSheaf R)} (p : M ⊗ N ⟶ P) :
    Functor.LaxMonoidal.μ (_root_.SheafOfModules.forget (ringCatSheaf R)) M N ≫
        (_root_.SheafOfModules.forget (ringCatSheaf R)).map p =
      (sheafificationForgetAdjunction R).homEquiv _ _ ((M.tensorUnderlyingIso N).inv ≫ p) := by
  rw [Adjunction.homEquiv_unit, Functor.map_comp, ← assoc, forget_μ]
  -- The two sides differ only in how the source of the unit is written: as `M.val ⊗ N.val`, or
  -- as the tensor product of the images of `M` and `N` under `forget`.
  rfl

/-- Two morphisms out of a tensor product `M ⊗ N` of sheaves of modules agree as soon as they
agree on the sectionwise tensor product `M.val ⊗ N.val` of the underlying presheaves of modules,
that is, after precomposition with the tensor map of `forget`. -/
lemma tensor_hom_ext {M N P : _root_.SheafOfModules.{u} (ringCatSheaf R)} {p q : M ⊗ N ⟶ P}
    (h : Functor.LaxMonoidal.μ (_root_.SheafOfModules.forget (ringCatSheaf R)) M N ≫
        (_root_.SheafOfModules.forget (ringCatSheaf R)).map p =
      Functor.LaxMonoidal.μ (_root_.SheafOfModules.forget (ringCatSheaf R)) M N ≫
        (_root_.SheafOfModules.forget (ringCatSheaf R)).map q) :
    p = q := by
  rw [forget_μ_comp_map, forget_μ_comp_map] at h
  exact (cancel_epi _).mp (((sheafificationForgetAdjunction R).homEquiv _ _).injective h)

end Forget

end SheafOfModules

end

end TauCeti

end
end CartierSource13

/-! ## Unchanged proof bodies from `TauCeti.Algebra.Category.ModuleCat.Sheaf.Free`

Upstream commit: 6b896c7c411221eb78639e4be8ead6e479a62893.
Original SHA256: d90f7981e6352277cdbf1a9d25f92444e7d41f40435aae90fd338f21cd46c984.
Module/import commands alone are relocated; EOF scopes are closed explicitly.
-/
section CartierSource14
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/


/-!
# Free sheaves on finitely many generators

This file records basic properties of free sheaves of modules. It gives the canonical
identification between the free sheaf on one generator and the tensor unit, shows that the free
sheaf on no generators is a zero object, and identifies the sections of a finite free sheaf with
tuples of sections of the coefficient sheaf.

For a finite index type, the free sheaf is also a finite biproduct of copies of the sheaf of
rings, so each of its sections is a linear combination of the tautological sections
`SheafOfModules.freeSection`, with coefficients in the ring of sections over the same object.
The morphism out of a free sheaf determined by a family of sections sends such a combination to
the corresponding combination of those sections. These are the sectionwise computations by
which generators and relations of a finitely presented sheaf are handled locally.

## Main declarations

* `TauCeti.SheafOfModules.freePUnitIsoUnit` identifies the free sheaf on `PUnit` with the sheaf
  of rings itself, regarded as a sheaf of modules;
* `TauCeti.SheafOfModules.isZero_free`: the free sheaf on an empty type is a zero object;
* `TauCeti.SheafOfModules.biproductIsoFree`: a finite free sheaf is the biproduct of copies of
  the unit;
* `TauCeti.SheafOfModules.evaluationFreeIso`: the sections of a finite free sheaf are tuples of
  sections of the coefficient sheaf;
* `TauCeti.SheafOfModules.freeBasis`: the corresponding basis of sections, consisting of the
  tautological sections `freeSection i`;
* `TauCeti.SheafOfModules.exists_eq_sum_smul_freeSection`: every section of a finite free sheaf
  is a linear combination of the tautological sections;
* `TauCeti.SheafOfModules.freeHomEquiv_symm_val_app_sum_smul`: evaluation of the morphism out
  of a free sheaf on such a linear combination;
* `TauCeti.SheafOfModules.isIso_unitHomEquiv_symm`: the morphism `unit R ⟶ M` attached to a
  global section `s` is an isomorphism when scalar multiplication on `s` is bijective over every
  object, that is, when `s` is a global basis of `M`.

The first comparison is used both by tensor-unit computations and when restricting a rank-one
local trivialization. No formalization is vendored; it is Mathlib's canonical isomorphism from a
coproduct indexed by a unique type to its unique summand.
-/

public section

open CategoryTheory Limits MonoidalCategory

namespace TauCeti

universe u v₁ u₁

noncomputable section

namespace SheafOfModules

variable {C : Type u₁} [Category.{v₁} C] {J : GrothendieckTopology C}
  [HasWeakSheafify J AddCommGrpCat.{u}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- The free sheaf on one generator is canonically isomorphic to the tensor unit. -/
def freePUnitIsoUnit (S : Sheaf J RingCat.{u}) :
    _root_.SheafOfModules.free.{u, v₁, u₁} (R := S) PUnit.{u + 1} ≅
      _root_.SheafOfModules.unit.{v₁, u₁, u} S :=
  coproductUniqueIso (fun _ : PUnit.{u + 1} ↦
    _root_.SheafOfModules.unit.{v₁, u₁, u} S)

/-- The inverse of `freePUnitIsoUnit` is the unique basis inclusion. -/
@[simp]
lemma freePUnitIsoUnit_inv (S : Sheaf J RingCat.{u}) :
    (freePUnitIsoUnit S).inv =
      _root_.SheafOfModules.ιFree (R := S) PUnit.unit := by
  exact coproductUniqueIso_inv (fun _ : PUnit.{u + 1} ↦
    _root_.SheafOfModules.unit.{v₁, u₁, u} S)

/-- The free sheaf of modules on an empty type is a zero object: it is the coproduct of the empty
family. -/
theorem isZero_free {S : Sheaf J RingCat.{u}} (I : Type u) [IsEmpty I] :
    IsZero (_root_.SheafOfModules.free (R := S) I) :=
  (isColimitEquivIsInitialOfIsEmpty _ _ (colimit.isColimit _)).isZero

section Sections

variable {R : Sheaf J RingCat.{u}} {I : Type u} [Fintype I]

/-- Every section of a free sheaf on a finite type is a linear combination of the tautological
sections, with coefficients in the ring of sections over the same object. -/
theorem exists_eq_sum_smul_freeSection {Y : Cᵒᵖ}
    (c : (_root_.SheafOfModules.free (R := R) I).val.obj Y) :
    ∃ a : I → R.obj.obj Y,
      c = ∑ k, a k • (_root_.SheafOfModules.freeSection (R := R) k).eval Y := by
  classical
  -- The coordinate projections of the finite coproduct `free I` onto its summands.
  let p : I → (_root_.SheafOfModules.free (R := R) I ⟶ _root_.SheafOfModules.unit R) :=
    fun k ↦ Cofan.IsColimit.desc (_root_.SheafOfModules.isColimitFreeCofan I)
      (fun j ↦ if j = k then 𝟙 _ else 0)
  have htot : ∑ k, p k ≫ _root_.SheafOfModules.ιFree k = 𝟙 _ := by
    refine Cofan.IsColimit.hom_ext (_root_.SheafOfModules.isColimitFreeCofan I) _ _ fun j ↦ ?_
    have hp (k : I) : _root_.SheafOfModules.ιFree j ≫ p k = if j = k then 𝟙 _ else 0 :=
      Cofan.IsColimit.fac (_root_.SheafOfModules.isColimitFreeCofan I) _ j
    -- The injections of `freeCofan I` are the `ιFree j`, but its cone point is only
    -- definitionally `free I`, so the goal is restated with that point.
    change _root_.SheafOfModules.ιFree j ≫ _ = _root_.SheafOfModules.ιFree j ≫ _
    rw [Preadditive.comp_sum, Category.comp_id, Finset.sum_eq_single j]
    · rw [← Category.assoc, hp]
      simp
    · intro k _ hk
      rw [← Category.assoc, hp]
      simp [Ne.symm hk]
    · simp
  refine ⟨fun k ↦ (p k).val.app Y c, ?_⟩
  let ev : (_root_.SheafOfModules.free (R := R) I ⟶ _root_.SheafOfModules.free I) →+
      (_root_.SheafOfModules.free (R := R) I).val.obj Y :=
    { toFun f := f.val.app Y c, map_zero' := rfl, map_add' _ _ := rfl }
  calc c = ev (∑ k, p k ≫ _root_.SheafOfModules.ιFree k) := by rw [htot]; rfl
    _ = _ := by
      rw [map_sum]
      refine Finset.sum_congr rfl fun k _ ↦ ?_
      -- The tautological section is the image of `1` under the basis inclusion.
      have h1 : (_root_.SheafOfModules.freeSection (R := R) k).eval Y =
          (_root_.SheafOfModules.ιFree k).val.app Y (1 : R.obj.obj Y) := rfl
      have h2 : ev (p k ≫ _root_.SheafOfModules.ιFree k) =
          (_root_.SheafOfModules.ιFree k).val.app Y ((p k).val.app Y c) := rfl
      rw [h1, h2]
      -- The unit module has `R.obj.obj Y` itself as carrier, so `r = r • 1` there.
      exact (congrArg ((_root_.SheafOfModules.ιFree k).val.app Y)
        (@mul_one (R.obj.obj Y) _ ((p k).val.app Y c)).symm).trans
          (((_root_.SheafOfModules.ιFree k).val.app Y).hom.map_smul ((p k).val.app Y c)
            (1 : R.obj.obj Y))

/-- The morphism out of a finite free sheaf determined by a family of sections `s` sends a
linear combination of the tautological sections to the same linear combination of the `s k`. -/
theorem freeHomEquiv_symm_val_app_sum_smul {M : _root_.SheafOfModules.{u} R}
    (s : I → M.sections) (Y : Cᵒᵖ) (a : I → R.obj.obj Y) :
    ((_root_.SheafOfModules.freeHomEquiv M).symm s).val.app Y
        (∑ k, a k • (_root_.SheafOfModules.freeSection (R := R) k).eval Y) =
      ∑ k, a k • (s k).eval Y := by
  refine (map_sum _ _ _).trans (Finset.sum_congr rfl fun k _ ↦ ?_)
  refine (((_root_.SheafOfModules.freeHomEquiv M).symm s).val.app Y).hom.map_smul _ _ |>.trans ?_
  exact congrArg (a k • ·) (congrArg (fun t : M.sections ↦ t.eval Y)
    (_root_.SheafOfModules.sectionsMap_freeHomEquiv_symm_freeSection s k))

omit [HasWeakSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}] in
/-- The morphism `unit R ⟶ M` attached to a global section `s` sends a scalar `r` over `Y` to
`r • s`. -/
@[simp]
lemma unitHomEquiv_symm_val_app {M : _root_.SheafOfModules.{u} R} (s : M.sections) (Y : Cᵒᵖ)
    (r : R.obj.obj Y) :
    (M.unitHomEquiv.symm s).val.app Y r = r • s.eval Y :=
  (rfl)

omit [HasWeakSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}] in
/-- The morphism `unit R ⟶ M` attached to a global section `s` is an isomorphism as soon as, over
every object `Y`, multiplying `s` by scalars is a bijection `R(Y) ⟶ M(Y)`: `s` is then a global
basis of `M`. -/
theorem isIso_unitHomEquiv_symm {M : _root_.SheafOfModules.{u} R} (s : M.sections)
    (hs : ∀ Y : Cᵒᵖ, Function.Bijective fun r : R.obj.obj Y ↦ r • s.eval Y) :
    IsIso (M.unitHomEquiv.symm s) := by
  rw [← isIso_iff_of_reflects_iso _ (_root_.SheafOfModules.forget _)]
  have (Y : Cᵒᵖ) : IsIso ((M.unitHomEquiv.symm s).val.app Y) := by
    rw [ConcreteCategory.isIso_iff_bijective]
    exact hs Y
  exact (_root_.PresheafOfModules.isoMk (fun Y ↦ asIso ((M.unitHomEquiv.symm s).val.app Y))
    fun _ _ f ↦ (M.unitHomEquiv.symm s).val.naturality f).isIso_hom

end Sections

end SheafOfModules

namespace SheafOfModules

open _root_.SheafOfModules

variable {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat RingCat.{u})]
variable [HasWeakSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]

variable {R : Sheaf J CommRingCat.{u}} (I : Type u) [Finite I]

/-- The free sheaf of modules on a finite type `I` is the biproduct of `I` copies of the unit. -/
def biproductIsoFree :
    ⨁ (fun _ : I ↦ 𝟙_ (SheafOfModules.{u} (ringCatSheaf R))) ≅ free (R := ringCatSheaf R) I :=
  (biproduct.isColimit _).coconePointUniqueUpToIso (isColimitFreeCofan I)

variable {I}

/-- `biproductIsoFree` sends the `i`-th summand to the `i`-th basis section. -/
@[reassoc (attr := simp)]
theorem biproduct_ι_biproductIsoFree_hom (i : I) :
    biproduct.ι (fun _ : I ↦ unit (ringCatSheaf R)) i ≫
      (biproductIsoFree (R := R) I).hom = ιFree i :=
  (biproduct.isColimit _).comp_coconePointUniqueUpToIso_hom (isColimitFreeCofan I) ⟨i⟩

/-- The inverse of `biproductIsoFree` sends the `i`-th basis section to the `i`-th summand. -/
@[reassoc (attr := simp)]
theorem ιFree_biproductIsoFree_inv (i : I) :
    ιFree i ≫ (biproductIsoFree (R := R) I).inv =
      biproduct.ι (fun _ : I ↦ 𝟙_ (SheafOfModules.{u} (ringCatSheaf R))) i :=
  (biproduct.isColimit _).comp_coconePointUniqueUpToIso_inv (isColimitFreeCofan I) ⟨i⟩

variable (I)

/-- The sections over `W` of the free sheaf of modules on a finite type `I` are the `I`-indexed
tuples of sections of the sheaf of rings over `W`: `free I` is the product of `I` copies of the
unit, and evaluation at `W` preserves products. -/
def evaluationFreeIso (W : Cᵒᵖ) :
    (evaluation (ringCatSheaf R) W).obj (free I) ≅
      ModuleCat.of ((ringCatSheaf R).obj.obj W) (I → (ringCatSheaf R).obj.obj W) :=
  (evaluation (ringCatSheaf R) W).mapIso
      ((biproductIsoFree (R := R) I).symm ≪≫ biproduct.isoProduct _) ≪≫
    PreservesProduct.iso (evaluation (ringCatSheaf R) W) _ ≪≫ ModuleCat.piIsoPi _

/-- The `i`-th coordinate of a section of `free I` under `evaluationFreeIso` is its image under
the `i`-th projection `free I ⟶ R` of the biproduct decomposition of `free I`. -/
@[reassoc (attr := simp)]
theorem evaluationFreeIso_hom_comp_proj (W : Cᵒᵖ) (i : I) :
    (evaluationFreeIso (R := R) I W).hom ≫ ModuleCat.ofHom (LinearMap.proj i) =
      (evaluation (ringCatSheaf R) W).map
        ((biproductIsoFree (R := R) I).inv ≫ biproduct.π _ i) := by
  -- The last factor of `evaluationFreeIso` lands in the module of `I`-tuples of sections of the
  -- unit over `W`, which is the module of `I`-tuples of sections of `R` only after unfolding
  -- `evaluation`; the composite is therefore spelled out in the former form before simplifying.
  change ((evaluation (ringCatSheaf R) W).map
      ((biproductIsoFree (R := R) I).inv ≫ (biproduct.isoProduct _).hom) ≫
    (PreservesProduct.iso (evaluation (ringCatSheaf R) W) _).hom ≫
    (ModuleCat.piIsoPi fun _ : I ↦ (evaluation (ringCatSheaf R) W).obj (𝟙_ _)).hom) ≫
      ModuleCat.ofHom (LinearMap.proj i) = _
  simp

/-- The basis of the sections over `W` of the free sheaf of modules on a finite type `I`, obtained
from the standard basis of `I`-tuples through `evaluationFreeIso`. Its `i`-th member is the basis
section `freeSection i` over `W` (`freeBasis_apply`). -/
def freeBasis (W : Cᵒᵖ) :
    Module.Basis I (R.obj.obj W)
      (PresheafOfModulesOfCommRing.obj (R := R.obj) (free (R := ringCatSheaf R) I).val W) :=
  (Pi.basisFun _ I).map (evaluationFreeIso (R := R) I W).toLinearEquiv.symm

/-- The `i`-th member of `freeBasis I W` is the basis section `freeSection i` over `W`. -/
@[simp]
theorem freeBasis_apply (W : Cᵒᵖ) (i : I) :
    freeBasis (R := R) I W i = (freeSection (R := ringCatSheaf R) i).eval W := by
  classical
  refine (Module.Basis.map_apply _ _ _).trans ((LinearEquiv.symm_apply_eq _).2 ?_)
  funext j
  -- The `j`-th coordinate is computed by `evaluationFreeIso_hom_comp_proj`, and
  -- `freeSection i` over `W` is the image of `1` under `ιFree i`.
  refine Eq.trans ?_ (ConcreteCategory.congr_hom (evaluationFreeIso_hom_comp_proj (R := R) I W j)
    ((ιFree (R := ringCatSheaf R) i).val.app W (1 : R.obj.obj W))).symm
  have h := ιFree_biproductIsoFree_inv_assoc (R := R) i (biproduct.π _ j)
  rw [biproduct.ι_π] at h
  -- `rw` cannot apply `h` to the goal: the coefficient ring is `(ringCatSheaf R).obj.obj W` on
  -- one side and `R.obj.obj W` on the other, which agree only after unfolding `ringCatSheaf`.
  refine Eq.trans ?_ (congrArg (fun g ↦ (g.val.app W) (1 : R.obj.obj W)) h).symm
  split_ifs with hij
  · subst hij
    simp
    -- the identity morphism of sheaves of modules is the identity on sections
    rfl
  · simp [Ne.symm hij]
    -- the zero morphism of sheaves of modules is zero on sections
    rfl

/-- The restriction maps of a finite free sheaf preserve the members of `freeBasis`. -/
theorem freeBasis_map {W W' : Cᵒᵖ} (f : W ⟶ W') (i : I) :
    (free (R := ringCatSheaf R) I).val.map f (freeBasis (R := R) I W i) =
      freeBasis (R := R) I W' i := by
  rw [freeBasis_apply, freeBasis_apply]
  exact PresheafOfModules.sections_property _ f

end SheafOfModules

end


end TauCeti

end
end CartierSource14

/-! ## Unchanged proof bodies from `TauCeti.Algebra.Category.ModuleCat.Sheaf.Invertible.Basic`

Upstream commit: 6b896c7c411221eb78639e4be8ead6e479a62893.
Original SHA256: 1b3caa1c6a44884c8d612909b05f57ae7599306d2fd4fa43dc72d5a535beb12f.
Module/import commands alone are relocated; EOF scopes are closed explicitly.
-/
section CartierSource15
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/


/-!
# Invertible sheaves of modules

Mathlib's `SheafOfModules.IsLocallyFree` remembers local generating families but deliberately
allows their ranks to vary. This file refines that local data by requiring each local generating
type to have exactly one element, which is the site-level content of being locally free of rank
one. Nothing here is specific to schemes, so everything is stated for a sheaf of modules over an
arbitrary site.

## Main declarations

* `SheafOfModules.LocalGeneratorsData.IsInvertible q` says that every presentation
  `free (q.generators i).I ⟶ M.over (q.X i)` is an isomorphism and that each indexing type is
  nonempty and a subsingleton;
* `TauCeti.SheafOfModules.IsInvertible M` says that such data exists for the sheaf of modules `M`;
* `SheafOfModules.LocalGeneratorsData.ofIso` transports local generator data along an
  isomorphism of sheaves of modules, and `TauCeti.SheafOfModules.IsInvertible.of_iso` transports
  invertibility along one.

The predicate implies Mathlib's local freeness (and hence quasi-coherence). Every free sheaf whose
indexing type is nonempty and a subsingleton is invertible.

The scheme-level packaging, where such a sheaf is an invertible sheaf on a scheme, is in
`TauCeti/AlgebraicGeometry/LineBundle/Basic.lean`. This advances
`TauCetiRoadmap/JacobianChallenge/README.md`, Layer A, item "Invertible sheaves on a scheme; the
Picard group `Pic X` under `⊗`". No formalization is vendored. The construction reuses Mathlib's
`SheafOfModules.LocalGeneratorsData`, `IsLocallyFreeData`, and `IsLocallyFree` API from
`Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree`.
-/

public section

open CategoryTheory

namespace TauCeti

universe u v₁ u₁

noncomputable section

namespace SheafOfModules

variable {C : Type u₁} [Category.{v₁} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{u}}
  [∀ Y : C, HasWeakSheafify (J.over Y) AddCommGrpCat.{u}]
  [∀ Y : C, (J.over Y).WEqualsLocallyBijective AddCommGrpCat.{u}]
  {M N : SheafOfModules.{u} R}

/-- Local generators exhibit a sheaf of modules as invertible when they freely generate it
on a cover and every local generating type has exactly one element. -/
structure _root_.SheafOfModules.LocalGeneratorsData.IsInvertible
    (q : SheafOfModules.LocalGeneratorsData M) : Prop where
  /-- The local generators freely generate the restricted sheaf. -/
  isLocallyFreeData : q.IsLocallyFreeData
  /-- Every local free basis has at least one element. -/
  basisNonempty (i : q.I) : Nonempty (q.generators i).I
  /-- Every local free basis has at most one element. -/
  basisSubsingleton (i : q.I) : Subsingleton (q.generators i).I

variable (M) in
/-- A sheaf of modules is invertible if it is locally free of rank one. The witness is
local generator data whose free presentations are isomorphisms and whose basis types have
exactly one element. -/
class IsInvertible : Prop where
  /-- A rank-one local trivialization of the sheaf. -/
  exists_isInvertible :
    ∃ q : SheafOfModules.LocalGeneratorsData.{u₁} M,
      SheafOfModules.LocalGeneratorsData.IsInvertible q

/-- An invertible sheaf is locally free. -/
instance IsInvertible.isLocallyFree (M : SheafOfModules.{u} R) [h : IsInvertible M] :
    M.IsLocallyFree := by
  obtain ⟨q, hq⟩ := h.exists_isInvertible
  let := hq.isLocallyFreeData
  exact q.isLocallyFree

/-- Transport local generator data along an isomorphism of sheaves of modules: the same cover, with
each family of local generators pushed forward along the restricted isomorphism. -/
@[expose, simps]
def _root_.SheafOfModules.LocalGeneratorsData.ofIso (q : SheafOfModules.LocalGeneratorsData M)
    (e : M ≅ N) :
    SheafOfModules.LocalGeneratorsData N where
  I := q.I
  X := q.X
  coversTop := q.coversTop
  generators i := (q.generators i).ofEpi ((SheafOfModules.overFunctor R (q.X i)).mapIso e).hom

/-- Rank-one local generator data stays rank one after transport along an isomorphism. -/
theorem _root_.SheafOfModules.LocalGeneratorsData.IsInvertible.ofIso
    {q : SheafOfModules.LocalGeneratorsData M}
    (hq : SheafOfModules.LocalGeneratorsData.IsInvertible q) (e : M ≅ N) :
    SheafOfModules.LocalGeneratorsData.IsInvertible
      (SheafOfModules.LocalGeneratorsData.ofIso q e) where
  isLocallyFreeData :=
    { isIso := by
        -- `ofIso` leaves the index type of the cover untouched, so the index may be taken in
        -- `q.I`; each transported presentation is then a composite of two isomorphisms.
        change ∀ i : q.I, IsIso ((q.generators i).ofEpi
          ((SheafOfModules.overFunctor R (q.X i)).mapIso e).hom).π
        intro i
        rw [SheafOfModules.GeneratingSections.ofEpi_π]
        exact IsIso.comp_isIso' (hq.isLocallyFreeData.isIso i) inferInstance }
  -- the index type of the transported presentation is the untouched `(q.generators i).I`, but the
  -- goal presents it through `ofEpi`; `change` names it directly, there being no lemma for it.
  basisNonempty i := by
    change Nonempty (q.generators i).I
    exact hq.basisNonempty i
  basisSubsingleton i := by
    change Subsingleton (q.generators i).I
    exact hq.basisSubsingleton i

/-- Invertibility transports along an isomorphism of sheaves of modules. -/
theorem IsInvertible.of_iso (e : M ≅ N) [h : IsInvertible M] : IsInvertible N := by
  obtain ⟨q, hq⟩ := h.exists_isInvertible
  exact ⟨SheafOfModules.LocalGeneratorsData.ofIso q e, hq.ofIso e⟩

section

variable [HasWeakSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [∀ Y : C, HasSheafify (J.over Y) AddCommGrpCat.{u}] [Limits.HasBinaryProducts C]
  [HasSheafify J AddCommGrpCat]

/-- A free sheaf whose indexing type has exactly one element is an invertible sheaf. -/
instance free_isInvertible (I : Type u) [Nonempty I] [Subsingleton I] :
    IsInvertible (SheafOfModules.free (R := R) I) where
  exists_isInvertible :=
    ⟨(SheafOfModules.free.generatingSections (R := R) I).localGeneratorsData,
      { isLocallyFreeData := inferInstance
        -- the index type of `free.generatingSections I` is `I` itself, so the two goals are the
        -- ambient instances; `change` names `I` so instance search can see them.
        basisNonempty := fun _ => by
          change Nonempty I
          infer_instance
        basisSubsingleton := fun _ => by
          change Subsingleton I
          infer_instance }⟩

end

end SheafOfModules

end

end TauCeti

end
end CartierSource15

/-! ## Recovered file CartierCore

Source SHA256: 658e31328762d66433412739e61d9f04a576d33ea49216cfc0f6e83ef58ee8b9.
The original named source sections and every proof body follow unchanged.
-/

/-! Exact proof bodies split from the uncompiled SchemeCore candidate.
No proof is replaced by an assumption. See `third_party/TauCeti/scheme_split.json`.
Verification requires an ordinary successful compiler record for this exact file. -/

/-! ## Unchanged proof bodies from `TauCeti.Algebra.Category.ModuleCat.Sheaf.Invertible.LocalTriviality`

Upstream commit: 6b896c7c411221eb78639e4be8ead6e479a62893.
Original SHA256: 7996f0502b918063a75a7a445d65a622654c5a8a19a182db254bbb5d1b80871e.
Module/import commands alone are relocated; EOF scopes are closed explicitly.
-/
section CartierSource16
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/


/-!
# Local trivializations of invertible sheaves

An invertible sheaf is locally free on a one-element basis. This file turns the
singleton-indexed free presentations in `SheafOfModules.IsInvertible` into the standard
geometric formulation: on every member of a cover, the sheaf is isomorphic to the free sheaf
on `PUnit`.

The structure `SheafOfModules.LocalTrivializations M` records such a cover and its
trivializing isomorphisms. The two formulations are equivalent:

* `SheafOfModules.LocalGeneratorsData.IsInvertible.trivializationIso` standardizes each
  rank-one free presentation;
* `LocalTrivializations.ofIso` transports a local trivialization atlas along an isomorphism;
* `LocalTrivializations.isInvertible` recovers the local-generator formulation;
* `LocalTrivializations.ofIsInvertible` constructs local trivializations from an invertible
  sheaf;
* `LocalTrivializations.nonempty_iff_isInvertible` characterizes invertibility by the existence
  of local trivializations.

This supplies the local-triviality interface for
`TauCetiRoadmap/JacobianChallenge/README.md`, Layer A, item "Invertible sheaves on a scheme; the
Picard group `Pic X` under `⊗`". It is the form needed to prove that tensor products and duals
of invertible sheaves remain invertible. The construction reuses Mathlib's free-sheaf functor and
`LocalGeneratorsData`; no formalization is vendored.
-/

public section

open CategoryTheory

namespace TauCeti

universe u v₁ u₁

noncomputable section

namespace SheafOfModules

variable {C : Type u₁} [Category.{v₁} C] {J : GrothendieckTopology C}
  {R : Sheaf J RingCat.{u}}
  [∀ Y : C, HasWeakSheafify (J.over Y) AddCommGrpCat.{u}]
  [∀ Y : C, (J.over Y).WEqualsLocallyBijective AddCommGrpCat.{u}]
  {M N : SheafOfModules.{u} R}

/-- A local trivialization atlas for a sheaf of modules. It consists of a cover of the terminal
object and, over every member of the cover, an isomorphism from the standard free rank-one
sheaf to the restriction of `M`. -/
structure LocalTrivializations (M : SheafOfModules.{u} R) where
  /-- The indexing type of the trivializing cover. -/
  I : Type u₁
  /-- The objects of the trivializing cover. -/
  X : I → C
  /-- The chosen objects cover the terminal object. -/
  coversTop : J.CoversTop X
  /-- The isomorphism from the standard free rank-one sheaf to `M` on each member of the
  cover. -/
  iso (i : I) :
    _root_.SheafOfModules.free (R := R.over (X i)) PUnit ≅ M.over (X i)


/-- A rank-one free presentation on a member of a cover, standardized to an isomorphism from
the free sheaf on `PUnit`. -/
def _root_.SheafOfModules.LocalGeneratorsData.IsInvertible.trivializationIso
    {q : SheafOfModules.LocalGeneratorsData M}
    (hq : SheafOfModules.LocalGeneratorsData.IsInvertible q) (i : q.I) :
    _root_.SheafOfModules.free (R := R.over (q.X i)) PUnit ≅ M.over (q.X i) := by
  letI : Nonempty (q.generators i).I := hq.basisNonempty i
  letI : Subsingleton (q.generators i).I := hq.basisSubsingleton i
  exact
    ((_root_.SheafOfModules.freeFunctor (R := R.over (q.X i))).mapIso
      Equiv.punitOfNonemptyOfSubsingleton.symm.toIso).trans
      (@asIso _ _ _ _ (q.generators i).π (hq.isLocallyFreeData.isIso i))

/-- The forward map of the standardized trivialization is the relabelling of the free basis,
followed by the original local free presentation. -/
@[simp]
lemma _root_.SheafOfModules.LocalGeneratorsData.IsInvertible.trivializationIso_hom
    {q : SheafOfModules.LocalGeneratorsData M}
    (hq : SheafOfModules.LocalGeneratorsData.IsInvertible q) (i : q.I) :
    (hq.trivializationIso i).hom =
      (_root_.SheafOfModules.freeFunctor (R := R.over (q.X i))).map
        (@Equiv.punitOfNonemptyOfSubsingleton (q.generators i).I
          (hq.basisNonempty i) (hq.basisSubsingleton i)).symm.toIso.hom ≫
        (q.generators i).π :=
  by
    simp only [SheafOfModules.LocalGeneratorsData.IsInvertible.trivializationIso, Iso.trans_hom,
      Functor.mapIso_hom]
    -- the residual goal is `(asIso (q.generators i).π).hom = (q.generators i).π`; `asIso_hom`
    -- no longer rewrites under the composition after the bump, and `asIso` stores its `hom`
    -- field as the given morphism, so this is definitional.
    rfl


namespace LocalTrivializations

/-- Transport local trivializations along an isomorphism of sheaves of modules. -/
def ofIso (t : LocalTrivializations M) (e : M ≅ N) : LocalTrivializations N where
  I := t.I
  X := t.X
  coversTop := t.coversTop
  iso i := t.iso i ≪≫ (SheafOfModules.overFunctor R (t.X i)).mapIso e

/-- Transporting local trivializations preserves the indexing type. -/
@[simp]
lemma ofIso_I (t : LocalTrivializations M) (e : M ≅ N) : (t.ofIso e).I = t.I := (rfl)

/-- Transporting local trivializations preserves the covering objects. -/
@[simp]
lemma ofIso_X (t : LocalTrivializations M) (e : M ≅ N) :
    (t.ofIso e).X = fun i ↦ t.X ((ofIso_I t e).mp i) := (rfl)

/-- The transported trivializations are obtained by composing with the restricted isomorphism. -/
@[simp]
lemma ofIso_iso (t : LocalTrivializations M) (e : M ≅ N) (i : (t.ofIso e).I) : (t.ofIso e).iso i =
      cast (by rw [ofIso_X])
        (t.iso ((ofIso_I t e).mp i) ≪≫
          (SheafOfModules.overFunctor R (t.X ((ofIso_I t e).mp i))).mapIso e) := (rfl)

/-- Local trivializations exhibit a sheaf as invertible. -/
theorem isInvertible (t : LocalTrivializations M) : IsInvertible M := by
  let q : SheafOfModules.LocalGeneratorsData.{u₁} M :=
    { I := t.I
      X := t.X
      coversTop := t.coversTop
      generators i :=
        (_root_.SheafOfModules.free.generatingSections
          (R := R.over (t.X i)) PUnit).ofEpi (t.iso i).hom }
  refine ⟨q, ?_⟩
  refine
    { isLocallyFreeData :=
        { isIso := by
            -- `q` uses the atlas's cover and the standard free generators, so unfold that local
            -- witness to express its isomorphism condition directly in terms of `t`.
            change ∀ i : t.I, IsIso
              ((_root_.SheafOfModules.free.generatingSections
                (R := R.over (t.X i)) PUnit).ofEpi (t.iso i).hom).π
            intro i
            rw [_root_.SheafOfModules.GeneratingSections.ofEpi_π]
            simpa only [_root_.SheafOfModules.free.generatingSections_π, Category.id_comp] using
              inferInstanceAs (IsIso (t.iso i).hom) }
      basisNonempty := fun i ↦ ?_
      basisSubsingleton := fun i ↦ ?_ }
  · simpa only [_root_.SheafOfModules.GeneratingSections.ofEpi_I,
      _root_.SheafOfModules.free.generatingSections_I] using
      inferInstanceAs (Nonempty PUnit)
  · simpa only [_root_.SheafOfModules.GeneratingSections.ofEpi_I,
      _root_.SheafOfModules.free.generatingSections_I] using
      inferInstanceAs (Subsingleton PUnit)

/-- Every invertible sheaf admits local trivializations by the standard free rank-one sheaf. -/
def ofIsInvertible (M : SheafOfModules.{u} R) [hM : IsInvertible M] :
    LocalTrivializations M := by
  let q := hM.exists_isInvertible.choose
  let hq := hM.exists_isInvertible.choose_spec
  exact
    { I := q.I
      X := q.X
      coversTop := q.coversTop
      iso i := hq.trivializationIso i }

/-- A sheaf of modules is invertible exactly when it admits a local trivialization atlas by
the standard free rank-one sheaf. -/
theorem nonempty_iff_isInvertible :
    Nonempty (LocalTrivializations M) ↔ IsInvertible M := by
  constructor
  · rintro ⟨t⟩
    exact t.isInvertible
  · intro hM
    let := hM
    exact ⟨ofIsInvertible M⟩

end LocalTrivializations

end SheafOfModules

end

end TauCeti

end
end CartierSource16

/-! ## Unchanged proof bodies from `TauCeti.AlgebraicGeometry.LineBundle.Basic`

Upstream commit: 6b896c7c411221eb78639e4be8ead6e479a62893.
Original SHA256: dcb7e5cde9e3ffec0844bf259557d600ace6ed016eb615abf4bdb4cb3e8ae134.
Module/import commands alone are relocated; EOF scopes are closed explicitly.
-/
section CartierSource17
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/


/-!
# Invertible sheaves on a scheme

This file begins the scheme-level line-bundle lane of the Jacobian challenge. An invertible
sheaf on a scheme `X` is an `𝒪_X`-module which is locally free of rank one.

The rank-one condition itself is not specific to schemes: it is
`TauCeti.SheafOfModules.IsInvertible` from
`TauCeti/Algebra/Category/ModuleCat/Sheaf/Invertible/Basic.lean`, stated for a sheaf of modules
over an arbitrary site. This file only packages it over a scheme:

* `TauCeti.AlgebraicGeometry.SheafOfModules.isInvertible X` is the `ObjectProperty` on `X.Modules`
  cut out by the predicate (closed under isomorphisms, by the site-level transport theorem, so
  `ObjectProperty.prop_of_iso` and `ObjectProperty.prop_iff_of_iso` apply to it);
* `TauCeti.AlgebraicGeometry.InvertibleSheaf X` is the full subcategory it cuts out;
* `InvertibleSheaf.free X I` is the free sheaf on an indexing type with exactly one element, and
  `InvertibleSheaf.trivial X` is the globally free rank-one sheaf;
* `SheafOfModules.isInvertible_unit` records that the structure sheaf `𝒪_X`, as a sheaf of
  modules over itself, is invertible;
* `SheafOfModules.isInvertible_iff_exists_isOpenCover` characterizes invertible sheaves on a
  scheme as those whose restrictions to the open subschemes of some open cover are isomorphic to
  the structure sheaves of those open subschemes.

A free rank-one trivialization of an `𝒪_X`-module `M` over an open `V` gives local coordinates:

* `Scheme.Modules.trivializationCoordinate` is the linear isomorphism `Γ(M, W) ≃ Γ(X, W)` it
  induces on every open `W ≤ V`, compatible with restriction in both directions
  (`Scheme.Modules.trivializationCoordinate_map` and
  `Scheme.Modules.map_trivializationCoordinate_symm`), and
  `Scheme.Modules.trivializationGenerator` is the basis section of `M` over `V` with coordinate
  one;
* `Scheme.Modules.existsUnique_eq_smul_map_trivializationGenerator` writes every section over
  `W ≤ V` uniquely as a regular multiple of the restricted basis section, and
  `Scheme.Modules.existsUnique_map_trivializationGenerator_eq_smul` shows that the basis sections
  of two trivializations differ by a unique regular unit on any common open subset.

These local rank-one coordinates describe transition functions between local bases and provide
normal forms for sections used in line-bundle constructions.
-/

public section

open CategoryTheory AlgebraicGeometry TopologicalSpace

namespace TauCeti

namespace AlgebraicGeometry

universe u

noncomputable section

namespace SheafOfModules

variable (X : Scheme.{u})

/-- Construct a rank-one atlas from an open cover and a trivialization on each member. -/
def LocalTrivializations.ofIsOpenCover {M : X.Modules} {ι : Type u} (W : ι → X.Opens)
    (hW : IsOpenCover W)
    (e : ∀ i, _root_.SheafOfModules.unit (X.ringCatSheaf.over (W i)) ≅ M.over (W i)) :
    TauCeti.SheafOfModules.LocalTrivializations.{u, u, u} M :=
  { I := ι
    X := W
    coversTop := (Opens.coversTop_iff (X : Type u) W).mpr hW
    iso := fun i ↦ TauCeti.SheafOfModules.freePUnitIsoUnit
      (X.ringCatSheaf.over (W i)) ≪≫ e i }

/-- Construct a rank-one atlas from a neighbourhood of each point and a trivialization there. -/
def LocalTrivializations.ofForallMem {M : X.Modules} (V : X → X.Opens)
    (hx : ∀ x, x ∈ V x)
    (e : ∀ x, _root_.SheafOfModules.unit (X.ringCatSheaf.over (V x)) ≅ M.over (V x)) :
    TauCeti.SheafOfModules.LocalTrivializations.{u, u, u} M :=
  LocalTrivializations.ofIsOpenCover X V
    (TopologicalSpace.IsOpenCover.mk (top_unique fun x _ ↦ Opens.mem_iSup.mpr ⟨x, hx x⟩)) e

/-- The object property of being an invertible sheaf on a scheme. -/
abbrev isInvertible : ObjectProperty X.Modules :=
  TauCeti.SheafOfModules.IsInvertible (R := X.ringCatSheaf)

instance : (isInvertible X).IsClosedUnderIsomorphisms where
  of_iso e hM := by
    have := hM
    exact TauCeti.SheafOfModules.IsInvertible.of_iso (R := X.ringCatSheaf) e

/-- The structure sheaf, regarded as a sheaf of modules over itself, is an invertible sheaf: it is
the free sheaf on one generator. -/
instance isInvertible_unit :
    isInvertible X (_root_.SheafOfModules.unit X.ringCatSheaf) :=
  TauCeti.SheafOfModules.IsInvertible.of_iso
    (M := _root_.SheafOfModules.free (R := X.ringCatSheaf) PUnit.{u + 1})
    (N := _root_.SheafOfModules.unit X.ringCatSheaf)
    (TauCeti.SheafOfModules.freePUnitIsoUnit X.ringCatSheaf)

end SheafOfModules

variable {X : Scheme.{u}}

/-- The full category of invertible sheaves on `X`. Its morphisms are morphisms of
`𝒪_X`-modules. -/
abbrev InvertibleSheaf (X : Scheme.{u}) : Type _ :=
  ObjectProperty.FullSubcategory (SheafOfModules.isInvertible X)

namespace InvertibleSheaf

instance (L : InvertibleSheaf X) : SheafOfModules.isInvertible X L.obj :=
  L.property

/-- The invertible sheaf given by the free sheaf on an indexing type with exactly one element. -/
def free (X : Scheme.{u}) (I : Type u) [Nonempty I] [Subsingleton I] :
    InvertibleSheaf X :=
  ⟨SheafOfModules.free (R := X.ringCatSheaf) I, inferInstance⟩

@[simp]
lemma free_obj (X : Scheme.{u}) (I : Type u) [Nonempty I] [Subsingleton I] :
    (free X I).obj = SheafOfModules.free (R := X.ringCatSheaf) I :=
  (rfl)

/-- The globally free rank-one invertible sheaf. -/
def trivial (X : Scheme.{u}) : InvertibleSheaf X :=
  free X PUnit

@[simp]
lemma trivial_obj (X : Scheme.{u}) :
    (trivial X).obj = SheafOfModules.free (R := X.ringCatSheaf) PUnit :=
  (rfl)

end InvertibleSheaf

end

end AlgebraicGeometry

namespace SheafOfModules.LocalTrivializations

universe u

variable {X : AlgebraicGeometry.Scheme.{u}} {M : X.Modules} {U : X.Opens}

/-- A free rank-one trivialization over an open is an isomorphism from the structure sheaf of
the open subscheme to the restricted module sheaf. -/
noncomputable def unitIsoRestrict
    (e : _root_.SheafOfModules.free (R := X.ringCatSheaf.over U) PUnit ≅ M.over U) :
    _root_.SheafOfModules.unit (U : AlgebraicGeometry.Scheme).ringCatSheaf ≅
      M.restrict (AlgebraicGeometry.Scheme.Opens.ι U) :=
  (AlgebraicGeometry.Scheme.Modules.overEquiv U).functor.mapIso
      ((TauCeti.SheafOfModules.freePUnitIsoUnit (X.ringCatSheaf.over U)).symm ≪≫ e) ≪≫
    (AlgebraicGeometry.Scheme.Modules.overFunctorEquiv U).app M

end SheafOfModules.LocalTrivializations

namespace AlgebraicGeometry.SheafOfModules

open _root_.AlgebraicGeometry TopologicalSpace

universe u

variable {X : Scheme.{u}} {M : X.Modules}

/-- A sheaf of modules on a scheme is invertible exactly when an open cover of the scheme
trivializes it: on every member `W` of the cover, its restriction to the open subscheme `W` is
isomorphic to the structure sheaf `𝒪_W`. -/
theorem isInvertible_iff_exists_isOpenCover :
    isInvertible X M ↔ ∃ (ι : Type u) (W : ι → X.Opens), IsOpenCover W ∧
      ∀ i, Nonempty (_root_.SheafOfModules.unit (W i : Scheme).ringCatSheaf ≅
        M.restrict (W i).ι) := by
  constructor
  · intro hM
    let t := TauCeti.SheafOfModules.LocalTrivializations.ofIsInvertible M
    exact ⟨t.I, t.X, (Opens.coversTop_iff (X : Type u) t.X).mp t.coversTop,
      fun i ↦ ⟨TauCeti.SheafOfModules.LocalTrivializations.unitIsoRestrict (t.iso i)⟩⟩
  · rintro ⟨ι, W, hW, e⟩
    -- On each `W i`, transport the trivialization `𝒪_{W i} ≅ M|_{W i}` of `(W i).toScheme`-modules
    -- back to the slice site over `W i` along the equivalence `Scheme.Modules.overEquiv`.
    exact (LocalTrivializations.ofIsOpenCover X W hW fun i ↦
      (Scheme.Modules.overEquiv (W i)).fullyFaithfulFunctor.preimageIso
        ((e i).some ≪≫ ((Scheme.Modules.overFunctorEquiv (W i)).app M).symm)).isInvertible

end AlgebraicGeometry.SheafOfModules

end TauCeti

namespace AlgebraicGeometry.Scheme.Modules

open CategoryTheory Opposite

universe u

noncomputable section

variable {X : Scheme.{u}}

/-- The coordinate isomorphism from a locally trivial rank-one module sheaf to the structure
sheaf on the trivializing open subset. -/
def trivializationCoordinateIso (M : X.Modules) {U : X.Opens}
    (e : SheafOfModules.free (R := X.ringCatSheaf.over U) PUnit ≅ M.over U) :
    M.over U ≅ SheafOfModules.unit (X.ringCatSheaf.over U) :=
  e.symm ≪≫ TauCeti.SheafOfModules.freePUnitIsoUnit (X.ringCatSheaf.over U)

/-- The coordinate of a free rank-one trivialization over `U`, read on an open subset `W ≤ U`:
the linear isomorphism between sections of the module sheaf and regular functions on `W`. -/
def trivializationCoordinate (M : X.Modules) {U W : X.Opens}
    (e : SheafOfModules.free (R := X.ringCatSheaf.over U) PUnit ≅ M.over U) (i : W ⟶ U) :
    Γ(M, W) ≃ₗ[Γ(X, W)] Γ(X, W) where
  -- Sections of `M.over U` and of the unit sheaf over `Over.mk i` are, by definition of the
  -- pushforward along `Over.forget U`, sections of `M` and of `𝒪_X` over `W`; over each open the
  -- unit sheaf is the ring of sections as a module over itself.
  toFun s := (trivializationCoordinateIso M e).hom.val.app (op (Over.mk i)) s
  invFun r := (trivializationCoordinateIso M e).inv.val.app (op (Over.mk i)) r
  map_add' := map_add _
  map_smul' := ((trivializationCoordinateIso M e).hom.val.app (op (Over.mk i))).hom.map_smul
  left_inv s := Iso.hom_inv_id_apply ((SheafOfModules.forget _ ⋙
    PresheafOfModules.toPresheaf _).mapIso (trivializationCoordinateIso M e) |>.app
      (op (Over.mk i))) (s : Γ(M, W))
  right_inv r := Iso.inv_hom_id_apply ((SheafOfModules.forget _ ⋙
    PresheafOfModules.toPresheaf _).mapIso (trivializationCoordinateIso M e) |>.app
      (op (Over.mk i))) (r : Γ(X, W))

/-- The coordinate on `W ≤ U` is the component of the coordinate isomorphism at `W`. -/
theorem trivializationCoordinate_apply (M : X.Modules) {U W : X.Opens}
    (e : SheafOfModules.free (R := X.ringCatSheaf.over U) PUnit ≅ M.over U) (i : W ⟶ U)
    (s : Γ(M, W)) :
    trivializationCoordinate M e i s =
      (trivializationCoordinateIso M e).hom.val.app (op (Over.mk i)) s := by
  rfl

/-- The coordinate of a free rank-one trivialization commutes with restriction to a smaller open
subset. -/
@[simp]
theorem trivializationCoordinate_map (M : X.Modules) {U W W' : X.Opens}
    (e : SheafOfModules.free (R := X.ringCatSheaf.over U) PUnit ≅ M.over U) (i : W ⟶ U)
    (j : W' ⟶ W) (s : Γ(M, W)) :
    trivializationCoordinate M e (j ≫ i) (M.presheaf.map j.op s) =
      X.presheaf.map j.op (trivializationCoordinate M e i s) :=
  -- Restriction in `M.over U` and in the unit sheaf along `Over.homMk j` is, by definition of
  -- the pushforward along `Over.forget U`, restriction in `M` and in `𝒪_X` along `j`.
  ((SheafOfModules.forget _ ⋙ PresheafOfModules.toPresheaf _).map
    (trivializationCoordinateIso M e).hom).naturality_apply
      (Over.homMk j : Over.mk (j ≫ i) ⟶ Over.mk i).op s

/-- The inverse coordinate of a free rank-one trivialization commutes with restriction to a
smaller open subset. -/
@[simp]
theorem map_trivializationCoordinate_symm (M : X.Modules) {U W W' : X.Opens}
    (e : SheafOfModules.free (R := X.ringCatSheaf.over U) PUnit ≅ M.over U) (i : W ⟶ U)
    (j : W' ⟶ W) (r : Γ(X, W)) :
    M.presheaf.map j.op ((trivializationCoordinate M e i).symm r) =
      (trivializationCoordinate M e (j ≫ i)).symm (X.presheaf.map j.op r) := by
  rw [LinearEquiv.eq_symm_apply, trivializationCoordinate_map, LinearEquiv.apply_symm_apply]

/-- The basis section of a line bundle over an open subset carrying a chosen rank-one
trivialization. -/
def trivializationGenerator (M : X.Modules) {V : X.Opens}
    (t : SheafOfModules.free (R := X.ringCatSheaf.over V) PUnit ≅ M.over V) : Γ(M, V) :=
  (trivializationCoordinate M t (𝟙 V)).symm 1

/-- The chosen trivialization reads the restriction of its basis section to any open subset
`W ≤ V` as the constant coordinate one. -/
@[simp]
theorem trivializationCoordinate_map_trivializationGenerator (M : X.Modules) {V W : X.Opens}
    (t : SheafOfModules.free (R := X.ringCatSheaf.over V) PUnit ≅ M.over V) (i : W ⟶ V) :
    trivializationCoordinate M t i (M.presheaf.map i.op (trivializationGenerator M t)) = 1 := by
  let c := (SheafOfModules.forget _ ⋙ PresheafOfModules.toPresheaf _).map
    (trivializationCoordinateIso M t).inv
  have h := c.naturality_apply (Over.homMk i : Over.mk i ⟶ Over.mk (𝟙 V)).op (1 : Γ(X, V))
  -- Restriction in `M.over V` and in the unit sheaf along `Over.homMk i` is, by definition of
  -- the pushforward along `Over.forget V`, restriction in `M` and in `𝒪_X` along `i`.
  have h' : M.presheaf.map i.op (trivializationGenerator M t) =
      (trivializationCoordinate M t i).symm (X.presheaf.map i.op 1) := by
    have hM : M.presheaf.map i.op (trivializationGenerator M t) =
        (M.over V).val.presheaf.map (Over.homMk i : Over.mk i ⟶ Over.mk (𝟙 V)).op
          (trivializationGenerator M t) := rfl
    have hX : (X.presheaf.map i.op 1 : Γ(X, W)) =
        (SheafOfModules.unit (X.ringCatSheaf.over V)).val.presheaf.map
          (Over.homMk i : Over.mk i ⟶ Over.mk (𝟙 V)).op (1 : Γ(X, V)) := rfl
    rw [hM, hX]
    exact h.symm
  rw [h', map_one, LinearEquiv.apply_symm_apply]

/-- The basis section of a rank-one trivialization has coordinate one. -/
@[simp]
theorem trivializationCoordinate_trivializationGenerator (M : X.Modules) {V : X.Opens}
    (t : SheafOfModules.free (R := X.ringCatSheaf.over V) PUnit ≅ M.over V) :
    trivializationCoordinate M t (𝟙 V) (trivializationGenerator M t) = 1 := by
  have h := trivializationCoordinate_map_trivializationGenerator M t (𝟙 V)
  rwa [op_id, M.presheaf.map_id, ConcreteCategory.id_apply] at h

/-- A section is its coordinate times the restricted basis section of a rank-one
trivialization. -/
theorem eq_trivializationCoordinate_smul_map_trivializationGenerator (M : X.Modules)
    {V W : X.Opens}
    (t : SheafOfModules.free (R := X.ringCatSheaf.over V) PUnit ≅ M.over V) (i : W ⟶ V)
    (s : Γ(M, W)) :
    s = trivializationCoordinate M t i s •
      M.presheaf.map i.op (trivializationGenerator M t) := by
  apply (trivializationCoordinate M t i).injective
  rw [LinearEquiv.map_smul, trivializationCoordinate_map_trivializationGenerator,
    smul_eq_mul, mul_one]

/-- On an open subset `W ≤ V`, every section is a unique regular-function multiple of the
restriction of the basis section of a rank-one trivialization over `V`. -/
theorem existsUnique_eq_smul_map_trivializationGenerator (M : X.Modules) {V W : X.Opens}
    (t : SheafOfModules.free (R := X.ringCatSheaf.over V) PUnit ≅ M.over V) (i : W ⟶ V)
    (s : Γ(M, W)) :
    ∃! r : Γ(X, W), s = r • M.presheaf.map i.op (trivializationGenerator M t) := by
  refine ⟨trivializationCoordinate M t i s,
    eq_trivializationCoordinate_smul_map_trivializationGenerator M t i s, ?_⟩
  intro r hr
  rw [hr, LinearEquiv.map_smul, trivializationCoordinate_map_trivializationGenerator,
    smul_eq_mul, mul_one]

/-- On an open subset `W` contained in the domains of two rank-one trivializations, the
restrictions of their basis sections differ by a unique unit of the regular functions on `W`. -/
theorem existsUnique_map_trivializationGenerator_eq_smul (M : X.Modules) {V₁ V₂ W : X.Opens}
    (t₁ : SheafOfModules.free (R := X.ringCatSheaf.over V₁) PUnit ≅ M.over V₁)
    (t₂ : SheafOfModules.free (R := X.ringCatSheaf.over V₂) PUnit ≅ M.over V₂)
    (i₁ : W ⟶ V₁) (i₂ : W ⟶ V₂) :
    ∃! u : Γ(X, W)ˣ, M.presheaf.map i₁.op (trivializationGenerator M t₁) =
      (u : Γ(X, W)) • M.presheaf.map i₂.op (trivializationGenerator M t₂) := by
  obtain ⟨r, hr, hr_unique⟩ := existsUnique_eq_smul_map_trivializationGenerator M t₂ i₂
    (M.presheaf.map i₁.op (trivializationGenerator M t₁))
  obtain ⟨s, hs, -⟩ := existsUnique_eq_smul_map_trivializationGenerator M t₁ i₁
    (M.presheaf.map i₂.op (trivializationGenerator M t₂))
  obtain ⟨r₁, -, h_unique⟩ := existsUnique_eq_smul_map_trivializationGenerator M t₁ i₁
    (M.presheaf.map i₁.op (trivializationGenerator M t₁))
  have hrs : r * s = 1 := by
    refine (h_unique (r * s) ?_).trans (h_unique 1 (one_smul _ _).symm).symm
    beta_reduce
    rw [mul_smul, ← hs, ← hr]
  refine ⟨Units.mkOfMulEqOne r s hrs, hr, fun u hu ↦ Units.ext ?_⟩
  rw [Units.val_mkOfMulEqOne]
  exact hr_unique _ hu

/-- The distinguished basis section of a rank-one trivialization is nonzero on a nonempty open
subset. -/
theorem trivializationGenerator_ne_zero (M : X.Modules) {V : X.Opens}
    (t : SheafOfModules.free (R := X.ringCatSheaf.over V) PUnit ≅ M.over V)
    [Nonempty V] :
    trivializationGenerator M t ≠ 0 := by
  intro h
  have hcoord := trivializationCoordinate_map_trivializationGenerator M t (𝟙 V)
  rw [op_id, M.presheaf.map_id, ConcreteCategory.id_apply, h, map_zero] at hcoord
  exact zero_ne_one (α := Γ(X, V)) hcoord

open TopologicalSpace in
/-- Every point of a scheme lies in the domain of a rank-one trivialization of an invertible
sheaf. -/
theorem exists_mem_trivialization (M : X.Modules)
    [TauCeti.AlgebraicGeometry.SheafOfModules.isInvertible X M] (x : X) :
    ∃ (V : X.Opens) (_ : SheafOfModules.free (R := X.ringCatSheaf.over V) PUnit ≅ M.over V),
      x ∈ V := by
  let t := TauCeti.SheafOfModules.LocalTrivializations.ofIsInvertible M
  have ht : ⨆ i, t.X i = ⊤ := by
    simpa only [IsOpenCover] using (Opens.coversTop_iff (X : Type u) t.X).mp t.coversTop
  obtain ⟨i, hi⟩ := Opens.mem_iSup.mp (ht ▸ Opens.mem_top x : x ∈ ⨆ i, t.X i)
  exact ⟨t.X i, t.iso i, hi⟩

end

end AlgebraicGeometry.Scheme.Modules

end
end CartierSource17

/-! ## Unchanged proof bodies from `TauCeti.AlgebraicGeometry.CartierDivisor.Sheaf`

Upstream commit: 6b896c7c411221eb78639e4be8ead6e479a62893.
Original SHA256: 0d265054725bbd821827b4f579f03f51c6c1c8c3f57f25888a20a22a4a7e5259.
Module/import commands alone are relocated; EOF scopes are closed explicitly.
-/
section CartierSource18
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/


/-!
# The line bundle of a Cartier divisor

Let `X` be an integral scheme with sheaf of rational functions `𝒦_X`, and let `D` be a Cartier
divisor on `X`, that is, a global section of `𝒦_X^× / 𝒪_X^×`. Near every point `x`, `D` is the
class of a nonzero rational function `f`, a *local equation* of `D` at `x`, well defined up to a
unit of the local ring `𝒪_{X,x}` (`Scheme.CartierDivisor.IsLocalEquationAt`). This file
constructs the sheaf `𝒪_X(D) ⊆ 𝒦_X`.

For nonempty `U`, its sections are rational functions satisfying

`Γ(U, 𝒪_X(D)) = {g ∈ K(X) | f g ∈ 𝒪_{X,x} for every x ∈ U and every local equation f at x}`.

Over the empty open subset, there is a unique section. In general the definition uses sections
of `𝒦_X` over `U`, so it also covers this case.

Consequently `𝒪_X(D) = f⁻¹ 𝒪_X` over any open subset on which `f` is an equation of `D`.
This file also proves that it is a line bundle.

## Main declarations

* `Scheme.CartierDivisor.sections D U`, the displayed submodule of `Γ(𝒦_X, U)`, described through
  a single local equation by `Scheme.CartierDivisor.mem_sections_iff_exists`, and, over an open
  subset on which `f` is an equation of `D`, as `f⁻¹ Γ(X, U)` by
  `Scheme.CartierDivisor.mem_sections_iff_of_rationalUnitClass_eq`;
* `Scheme.CartierDivisor.sheaf D`, the sheaf `𝒪_X(D)` of `𝒪_X`-modules, with its inclusion
  `Scheme.CartierDivisor.sheafι D : 𝒪_X(D) ⟶ 𝒦_X` (`sheafι_app_mem`, `range_sheafι_app`) and
  the factorization `Scheme.CartierDivisor.sheafLift` through it of a morphism to `𝒦_X` whose
  sections satisfy the defining condition, an isomorphism when that morphism is injective with
  image `𝒪_X(D)` (`Scheme.CartierDivisor.isIso_sheafLift`);
* `Scheme.CartierDivisor.sheafOverIsoOfRestrictEq`: divisors that agree on an open subset `V` have
  isomorphic sheaves over `V`;
* `Scheme.CartierDivisor.unitIsoSheafPrincipalCartierDivisor`: the sheaf of the principal divisor
  of `f` is `f⁻¹ 𝒪_X`, trivialized by multiplication by `f`;
* `Scheme.CartierDivisor.isInvertible_sheaf` and `Scheme.CartierDivisor.toInvertibleSheaf`:
  `𝒪_X(D)` is a line bundle.

## References

* R. Hartshorne, *Algebraic Geometry*, Section II.6, the construction of `𝓛(D)` preceding
  Proposition II.6.13.
* `TauCeti/AlgebraicGeometry/WeilDivisor/Scheme/Sheaf.lean`, whose submodule sheaf
  construction is the model for this Cartier divisor sheaf.
-/

@[expose] public section

open CategoryTheory TopologicalSpace AlgebraicGeometry Opposite

namespace TauCeti

namespace AlgebraicGeometry

universe u

noncomputable section

namespace Scheme

variable {X : Scheme.{u}} [IsIntegral X]

namespace CartierDivisor

/-- The sections of `𝒪_X(D)` over an open subset `U`: the rational functions `g` such that `f g`
lies in the local ring `𝒪_{X,x}` for every point `x ∈ U` and every local equation `f` of `D`
at `x`.

By `IsLocalEquationAt.mul_mem_range_iff` it suffices to test one local equation at each point
(`mem_sections_iff_exists`). -/
def sections (D : CartierDivisor X) (U : X.Opens) :
    Submodule Γ(X, U) Γ(rationalFunctions X, U) where
  carrier := {s | ∀ (x : X) (hx : x ∈ U) (f : X.functionFieldˣ), D.IsLocalEquationAt x f →
    haveI : Nonempty U := ⟨⟨x, hx⟩⟩
    (f : X.functionField) * rationalFunctionsEquiv U s ∈
      (algebraMap (X.presheaf.stalk x) X.functionField).range}
  zero_mem' := by
    intro x hx f _
    have : Nonempty U := ⟨⟨x, hx⟩⟩
    rw [map_zero, mul_zero]
    exact Subring.zero_mem _
  add_mem' := by
    intro s t hs ht x hx f hf
    have : Nonempty U := ⟨⟨x, hx⟩⟩
    rw [map_add, mul_add]
    exact Subring.add_mem _ (hs x hx f hf) (ht x hx f hf)
  smul_mem' := by
    intro r s hs x hx f hf
    have : Nonempty U := ⟨⟨x, hx⟩⟩
    rw [map_smul, ← germ_smul_functionField hx, Algebra.smul_def, mul_left_comm]
    exact Subring.mul_mem _ (RingHom.mem_range_self _ _) (hs x hx f hf)

/-- Membership in `CartierDivisor.sections`, unfolded. -/
lemma mem_sections {D : CartierDivisor X} {U : X.Opens} {s : Γ(rationalFunctions X, U)} :
    s ∈ D.sections U ↔ ∀ (x : X) (hx : x ∈ U) (f : X.functionFieldˣ),
      D.IsLocalEquationAt x f →
        haveI : Nonempty U := ⟨⟨x, hx⟩⟩
        (f : X.functionField) * rationalFunctionsEquiv U s ∈
          (algebraMap (X.presheaf.stalk x) X.functionField).range :=
  Iff.rfl

/-- A rational function is a section of `𝒪_X(D)` over `U` as soon as, at every point of `U`, its
product with *some* local equation of `D` lies in the local ring. -/
theorem mem_sections_iff_exists {D : CartierDivisor X} {U : X.Opens}
    {s : Γ(rationalFunctions X, U)} :
    s ∈ D.sections U ↔ ∀ (x : X) (hx : x ∈ U), ∃ f : X.functionFieldˣ,
      D.IsLocalEquationAt x f ∧
        haveI : Nonempty U := ⟨⟨x, hx⟩⟩
        (f : X.functionField) * rationalFunctionsEquiv U s ∈
          (algebraMap (X.presheaf.stalk x) X.functionField).range := by
  constructor
  · intro hs x hx
    obtain ⟨f, hf⟩ := D.exists_isLocalEquationAt x
    exact ⟨f, hf, hs x hx f hf⟩
  · intro hs x hx g hg
    obtain ⟨f, hf, hmem⟩ := hs x hx
    exact (hf.mul_mem_range_iff hg _).mp hmem

/-- Restricting to a smaller open subset preserves the sections of `𝒪_X(D)`. -/
lemma sections_map {D : CartierDivisor X} {U V : X.Opens} (i : V ⟶ U)
    {s : Γ(rationalFunctions X, U)} (hs : s ∈ D.sections U) :
    (rationalFunctions X).presheaf.map i.op s ∈ D.sections V := by
  intro x hx f hf
  have : Nonempty V := ⟨⟨x, hx⟩⟩
  have : Nonempty U := ⟨⟨x, i.le hx⟩⟩
  rw [rationalFunctionsEquiv_map]
  exact hs x (i.le hx) f hf

/-- **The sections of `𝒪_X(D)` over an open subset carrying an equation.** Let `f` be an equation
of `D` over `V`. Over every nonempty open `W ≤ V`, a rational function `g` is a section of
`𝒪_X(D)` exactly when `f g` is regular on `W`; that is, `𝒪_X(D) = f⁻¹ 𝒪_X` over `V`. -/
theorem mem_sections_iff_of_rationalUnitClass_eq {D : CartierDivisor X} {V W : X.Opens}
    [Nonempty V] [Nonempty W] (hWV : W ≤ V) {f : X.functionFieldˣ}
    (hf : rationalUnitClass X V (Additive.ofMul f) = D |_ V) {s : Γ(rationalFunctions X, W)} :
    s ∈ D.sections W ↔
      ∃ a : Γ(X, W), X.germToFunctionField W a = f * rationalFunctionsEquiv W s := by
  have hfW := rationalUnitClass_eq_of_le hWV hf
  constructor
  · intro hs
    exact exists_germToFunctionField_eq_of_forall_mem_range fun y hy ↦
      hs y hy f (isLocalEquationAt_of_rationalUnitClass_eq hfW hy)
  · rintro ⟨a, ha⟩
    refine mem_sections_iff_exists.mpr fun x hx ↦
      ⟨f, isLocalEquationAt_of_rationalUnitClass_eq hfW hx, ?_⟩
    rw [← ha, ← _root_.AlgebraicGeometry.Scheme.algebraMap_germ_eq_germToFunctionField X hx]
    exact RingHom.mem_range_self _ _

/-- Divisors that agree on an open subset `V` have the same sections over every open `W ≤ V`. -/
lemma sections_congr {D E : CartierDivisor X} {V W : X.Opens} (h : D |_ V = E |_ V)
    (hWV : W ≤ V) : D.sections W = E.sections W := by
  ext s
  simp only [mem_sections]
  exact forall_congr' fun x ↦ forall_congr' fun hx ↦ forall_congr' fun f ↦
    imp_congr_left (isLocalEquationAt_congr h (hWV hx) f)

/-- The `𝒪_X`-submodule `𝒪_X(D)` of the sheaf `𝒦_X` of rational functions. The membership
condition is imposed point by point, so this is a submodule of the *sheaf* `𝒦_X`. -/
def submodule (D : CartierDivisor X) : (rationalFunctions X).Submodule where
  obj U := D.sections U.unop
  map i := fun {_} hs ↦ sections_map i.unop hs
  isSheaf {U} s hs := by
    intro x hx f hf
    obtain ⟨V, i, hi, hxV⟩ := hs x hx
    have : Nonempty V := ⟨⟨x, hxV⟩⟩
    have : Nonempty U.unop := ⟨⟨x, hx⟩⟩
    -- `hi` says that the restriction of `s` to `V` lies in the component of the submodule under
    -- construction at `op V`, which is `D.sections V` by definition.
    have hi' : (rationalFunctions X).presheaf.map i.op s ∈ D.sections V := hi
    rw [← rationalFunctionsEquiv_map i s]
    exact hi' x hxV f hf

/-- The component of the submodule `𝒪_X(D) ⊆ 𝒦_X` at an object of the opposite category. -/
@[simp]
lemma submodule_obj (D : CartierDivisor X) (U : (Opens X)ᵒᵖ) :
    D.submodule.toSubmodule.obj U = D.sections U.unop := by
  induction U using Opposite.rec
  rfl

/-- The sheaf `𝒪_X(D)` of `𝒪_X`-modules attached to a Cartier divisor `D`. -/
def sheaf (D : CartierDivisor X) : X.Modules :=
  D.submodule.toSheafOfModules

/-- The inclusion `𝒪_X(D) ⟶ 𝒦_X`. -/
def sheafι (D : CartierDivisor X) : D.sheaf ⟶ rationalFunctions X :=
  D.submodule.ι

/-- A rational function satisfying the conditions for `𝒪_X(D)` as a section of that sheaf. -/
def sectionMk {D : CartierDivisor X} {U : X.Opens} (s : Γ(rationalFunctions X, U))
    (hs : s ∈ D.sections U) : Γ(D.sheaf, U) :=
  ⟨s, hs⟩

/-- The inclusion `𝒪_X(D) ⟶ 𝒦_X` is injective on sections over every open subset. -/
lemma sheafι_app_injective (D : CartierDivisor X) (U : X.Opens) :
    Function.Injective (Scheme.Modules.Hom.app D.sheafι U) :=
  TauCeti.SheafOfModules.ι_val_app_injective D.submodule (op U)

/-- Including a section built from a rational function recovers that function. -/
@[simp]
lemma sheafι_app_sectionMk {D : CartierDivisor X} {U : X.Opens}
    (s : Γ(rationalFunctions X, U)) (hs : s ∈ D.sections U) :
    Scheme.Modules.Hom.app D.sheafι U (sectionMk s hs) = s :=
  (rfl)

/-- The inclusion `𝒪_X(D) ⟶ 𝒦_X` sends a section of `𝒪_X(D)` over `U` into `sections D U`. -/
lemma sheafι_app_mem (D : CartierDivisor X) (U : X.Opens) (t : Γ(D.sheaf, U)) :
    Scheme.Modules.Hom.app D.sheafι U t ∈ D.sections U :=
  TauCeti.SheafOfModules.ι_val_app_mem D.submodule (op U) t

/-- **The sections of `𝒪_X(D)` over `U` are exactly `sections D U`.** Together with
`sheafι_app_injective` this identifies the sections of `𝒪_X(D)` with the submodule of
`Γ(𝒦_X, U)` which defines it. -/
@[simp]
lemma range_sheafι_app (D : CartierDivisor X) (U : X.Opens) :
    Set.range (Scheme.Modules.Hom.app D.sheafι U) = D.sections U :=
  TauCeti.SheafOfModules.range_ι_val_app D.submodule (op U)

/-- The inclusion `𝒪_X(D) ⟶ 𝒦_X` is a monomorphism. -/
instance (D : CartierDivisor X) : Mono D.sheafι :=
  -- Instance search does not see through `X.Modules` to `SheafOfModules X.ringCatSheaf`, so
  -- Mathlib's instance for the inclusion of a submodule is supplied explicitly.
  SheafOfModules.Submodule.instMonoι D.submodule

instance (D : CartierDivisor X) (V : X.Opens) : Mono (D.sheafι.over V) :=
  SheafOfModules.Submodule.instMonoιOver D.submodule V

/-- A morphism `M ⟶ 𝒦_X` all of whose sections lie in `𝒪_X(D)` factors through `𝒪_X(D)`. -/
def sheafLift {M : X.Modules} (D : CartierDivisor X) (φ : M ⟶ rationalFunctions X)
    (hφ : ∀ (U : X.Opens) (s : Γ(M, U)), Scheme.Modules.Hom.app φ U s ∈ D.sections U) :
    M ⟶ D.sheaf :=
  TauCeti.SheafOfModules.liftToSubmodule D.submodule φ fun U s ↦ hφ U.unop s

/-- `sheafLift` factors `φ` through `𝒪_X(D)`: composing it with the inclusion
`sheafι D : 𝒪_X(D) ⟶ 𝒦_X` recovers `φ`. -/
@[reassoc (attr := simp)]
lemma sheafLift_ι {M : X.Modules} (D : CartierDivisor X) (φ : M ⟶ rationalFunctions X)
    (hφ : ∀ (U : X.Opens) (s : Γ(M, U)), Scheme.Modules.Hom.app φ U s ∈ D.sections U) :
    D.sheafLift φ hφ ≫ D.sheafι = φ :=
  TauCeti.SheafOfModules.liftToSubmodule_ι _ _ _

/-- On sections, `sheafLift` followed by the inclusion into `𝒦_X` is the original morphism. -/
@[simp]
lemma sheafι_app_sheafLift {M : X.Modules} (D : CartierDivisor X)
    (φ : M ⟶ rationalFunctions X)
    (hφ : ∀ (U : X.Opens) (s : Γ(M, U)), Scheme.Modules.Hom.app φ U s ∈ D.sections U)
    (U : X.Opens) (s : Γ(M, U)) :
    Scheme.Modules.Hom.app D.sheafι U (Scheme.Modules.Hom.app (D.sheafLift φ hφ) U s) =
      Scheme.Modules.Hom.app φ U s :=
  TauCeti.SheafOfModules.liftToSubmodule_val_app_coe D.submodule φ
    (fun V t ↦ hφ V.unop t) (op U) s

/-- A factorization through `𝒪_X(D)` is an isomorphism if its map into rational functions is
injective on sections and has image exactly the sections of `𝒪_X(D)`. -/
theorem isIso_sheafLift {M : X.Modules} (D : CartierDivisor X) (φ : M ⟶ rationalFunctions X)
    (hφ : ∀ (U : X.Opens) (s : Γ(M, U)), Scheme.Modules.Hom.app φ U s ∈ D.sections U)
    (hinj : ∀ U : X.Opens, Function.Injective (Scheme.Modules.Hom.app φ U))
    (hsurj : ∀ (U : X.Opens) (s : Γ(rationalFunctions X, U)),
      s ∈ D.sections U → ∃ t, Scheme.Modules.Hom.app φ U t = s) :
    IsIso (D.sheafLift φ hφ) :=
  TauCeti.SheafOfModules.isIso_liftToSubmodule _ _ _ (fun U ↦ hinj U.unop)
    fun U s hs ↦ hsurj U.unop s ((D.submodule_obj U) ▸ hs)

/-- **Divisors agreeing on an open subset have isomorphic sheaves there.** If `D` and `E` have the
same restriction to `V`, then `𝒪_X(D)` and `𝒪_X(E)` have the same sections over every open
subset of `V`, so they are isomorphic over `V`, compatibly with their inclusions into `𝒦_X`
(`sheafOverIsoOfRestrictEq_hom_ι`, `sheafOverIsoOfRestrictEq_inv_ι`). -/
def sheafOverIsoOfRestrictEq (D E : CartierDivisor X) (V : X.Opens) (h : D |_ V = E |_ V) :
    D.sheaf.over V ≅ E.sheaf.over V :=
  D.submodule.overIsoOfEq E.submodule V fun W i ↦
    (D.submodule_obj (op W)).trans ((sections_congr h i.le).trans (E.submodule_obj (op W)).symm)

/-- The isomorphism `sheafOverIsoOfRestrictEq` is compatible with the inclusions into `𝒦_X`. -/
@[reassoc (attr := simp)]
lemma sheafOverIsoOfRestrictEq_hom_ι (D E : CartierDivisor X) (V : X.Opens)
    (h : D |_ V = E |_ V) :
    (sheafOverIsoOfRestrictEq D E V h).hom ≫ E.sheafι.over V = D.sheafι.over V :=
  SheafOfModules.Submodule.overIsoOfEq_hom_ι _ _ _ _

/-- The inverse of `sheafOverIsoOfRestrictEq` is compatible with the inclusions into `𝒦_X`. -/
@[reassoc (attr := simp)]
lemma sheafOverIsoOfRestrictEq_inv_ι (D E : CartierDivisor X) (V : X.Opens)
    (h : D |_ V = E |_ V) :
    (sheafOverIsoOfRestrictEq D E V h).inv ≫ D.sheafι.over V = E.sheafι.over V :=
  SheafOfModules.Submodule.overIsoOfEq_inv_ι _ _ _ _

/-- For a regular function `a` on `U`, the rational function `f⁻¹ a` is a section of the sheaf of
the principal divisor of `f` over `U`. -/
lemma rationalFunctionsMul_inv_toRationalFunctions_app_mem_sections (f : X.functionFieldˣ)
    (U : X.Opens) (a : Γ(X, U)) :
    Scheme.Modules.Hom.app (rationalFunctionsMul X ((f⁻¹ : X.functionFieldˣ) : X.functionField))
        U (Scheme.Modules.Hom.app (toRationalFunctions X) U a) ∈
      (principalCartierDivisor X f).sections U := by
  rcases isEmpty_or_nonempty U with hU | hU
  · -- Over the empty set the membership condition is vacuous.
    exact mem_sections.mpr fun x hx ↦ hU.elim ⟨x, hx⟩
  · refine (mem_sections_iff_of_rationalUnitClass_eq le_rfl
      (principalCartierDivisor_restrict X f U).symm).mpr ⟨a, ?_⟩
    rw [rationalFunctionsEquiv_rationalFunctionsMul_app,
      rationalFunctionsEquiv_toRationalFunctions_app, ← mul_assoc, Units.mul_inv, one_mul]

variable (X) in
/-- Multiplication by `f⁻¹`, from `𝒪_X` to the sheaf of the principal divisor of `f`: a regular
function `a` goes to the section `f⁻¹ a` of `𝒪_X(div f)`. -/
def unitToSheafPrincipalCartierDivisor (f : X.functionFieldˣ) :
    @Quiver.Hom X.Modules _ (SheafOfModules.unit X.ringCatSheaf)
      (principalCartierDivisor X f).sheaf :=
  (principalCartierDivisor X f).sheafLift
    (toRationalFunctions X ≫ rationalFunctionsMul X ((f⁻¹ : X.functionFieldˣ) : X.functionField))
    fun U a ↦ rationalFunctionsMul_inv_toRationalFunctions_app_mem_sections f U a

/-- `unitToSheafPrincipalCartierDivisor X f`, read inside `𝒦_X`, is multiplication by `f⁻¹`. -/
@[simp, reassoc]
lemma unitToSheafPrincipalCartierDivisor_ι (f : X.functionFieldˣ) :
    unitToSheafPrincipalCartierDivisor X f ≫ (principalCartierDivisor X f).sheafι =
      toRationalFunctions X ≫
        rationalFunctionsMul X ((f⁻¹ : X.functionFieldˣ) : X.functionField) :=
  sheafLift_ι _ _ _

/-- The principal-divisor map sends `a` to `f⁻¹ a` inside the rational-function sheaf. -/
@[simp]
lemma unitToSheafPrincipalCartierDivisor_app (f : X.functionFieldˣ)
    (U : X.Opens) (a : Γ(SheafOfModules.unit X.ringCatSheaf, U)) :
    Scheme.Modules.Hom.app (principalCartierDivisor X f).sheafι U
        (Scheme.Modules.Hom.app (unitToSheafPrincipalCartierDivisor X f) U a) =
      Scheme.Modules.Hom.app (rationalFunctionsMul X
        ((f⁻¹ : X.functionFieldˣ) : X.functionField)) U
        (Scheme.Modules.Hom.app (toRationalFunctions X) U a) := by
  unfold unitToSheafPrincipalCartierDivisor
  simpa only [Scheme.Modules.Hom.comp_app (M := SheafOfModules.unit X.ringCatSheaf),
    ConcreteCategory.comp_apply] using
    sheafι_app_sheafLift (principalCartierDivisor X f)
      (toRationalFunctions X ≫ rationalFunctionsMul X
        ((f⁻¹ : X.functionFieldˣ) : X.functionField))
      (fun V b ↦ rationalFunctionsMul_inv_toRationalFunctions_app_mem_sections f V b) U a

/-- Multiplication by `f⁻¹` is an isomorphism from `𝒪_X` to the sheaf `𝒪_X(div f)` of the
principal divisor of `f`; it is packaged as `unitIsoSheafPrincipalCartierDivisor`. -/
instance isIso_unitToSheafPrincipalCartierDivisor (f : X.functionFieldˣ) :
    IsIso (unitToSheafPrincipalCartierDivisor X f) := by
  -- Injectivity comes from that of `𝒪_X ⟶ 𝒦_X`; surjectivity from the description of the
  -- sections of `𝒪_X(div f)` as the rational functions `g` with `f g` regular.
  refine TauCeti.SheafOfModules.isIso_liftToSubmodule _ _ _ (fun U a b hab ↦ ?_)
    fun U t ht ↦ ?_
  · -- Multiplication by `f⁻¹` is injective on sections, with left inverse multiplication by `f`.
    refine toRationalFunctions_app_injective U.unop ?_
    rw [← rationalFunctionsMul_app_rationalFunctionsMul_inv_app f U.unop
        (Scheme.Modules.Hom.app (toRationalFunctions X) U.unop a),
      ← rationalFunctionsMul_app_rationalFunctionsMul_inv_app f U.unop
        (Scheme.Modules.Hom.app (toRationalFunctions X) U.unop b)]
    exact congrArg _ hab
  · induction U using Opposite.rec with | op U => ?_
    rw [submodule_obj] at ht
    rcases isEmpty_or_nonempty U with hU | hU
    · have hbot : U = ⊥ := Opens.coe_eq_empty.mp (Set.isEmpty_coe_sort.mp hU)
      have := subsingleton_rationalFunctions U hbot
      exact ⟨0, @Subsingleton.elim _ this _ _⟩
    · obtain ⟨a, ha⟩ := (mem_sections_iff_of_rationalUnitClass_eq le_rfl
        (principalCartierDivisor_restrict X f U).symm).mp ht
      refine ⟨a, (rationalFunctionsEquiv U).injective ?_⟩
      -- The isomorphism criterion states the goal with `φ.val.app (op U)`, while the
      -- multiplication lemmas use `Scheme.Modules.Hom.app φ U`. The latter is defined from the
      -- former, and Mathlib has no lemma relating them, so we restate the goal.
      change rationalFunctionsEquiv U (Scheme.Modules.Hom.app (rationalFunctionsMul X
        ((f⁻¹ : X.functionFieldˣ) : X.functionField)) U
        (Scheme.Modules.Hom.app (toRationalFunctions X) U a)) = _
      rw [rationalFunctionsEquiv_rationalFunctionsMul_app,
        rationalFunctionsEquiv_toRationalFunctions_app, ha, ← mul_assoc, Units.inv_mul,
        one_mul]

variable (X) in
/-- **The sheaf of a principal Cartier divisor is trivial.** Multiplication by `f⁻¹` identifies
`𝒪_X` with `𝒪_X(div f)`. -/
def unitIsoSheafPrincipalCartierDivisor (f : X.functionFieldˣ) :
    @Iso X.Modules _ (SheafOfModules.unit X.ringCatSheaf) (principalCartierDivisor X f).sheaf :=
  asIso (unitToSheafPrincipalCartierDivisor X f)

/-- The forward map of `unitIsoSheafPrincipalCartierDivisor` is multiplication by `f⁻¹`. -/
@[simp]
lemma unitIsoSheafPrincipalCartierDivisor_hom (f : X.functionFieldˣ) :
    (unitIsoSheafPrincipalCartierDivisor X f).hom = unitToSheafPrincipalCartierDivisor X f :=
  (rfl)

/-- The inverse of `unitIsoSheafPrincipalCartierDivisor`, read inside `𝒦_X`, is multiplication by
`f`: it sends a section `g` of `𝒪_X(div f)` to the regular function `f g`. -/
@[simp, reassoc]
lemma unitIsoSheafPrincipalCartierDivisor_inv_toRationalFunctions (f : X.functionFieldˣ) :
    (unitIsoSheafPrincipalCartierDivisor X f).inv ≫ toRationalFunctions X =
      (principalCartierDivisor X f).sheafι ≫
        rationalFunctionsMul X ((f : X.functionFieldˣ) : X.functionField) :=
  -- The goal mentions `SheafOfModules.unit X.ringCatSheaf`, which `rw` cannot see to be
  -- type-correct (`TopCat.Sheaf` is not unfolded at instance transparency), so the
  -- associativity steps are chained as terms.
  (Iso.inv_comp_eq (unitIsoSheafPrincipalCartierDivisor X f)).mpr <|
    (Category.comp_id _).symm.trans <|
      (congrArg (toRationalFunctions X ≫ ·) (rationalFunctionsMul_inv_comp f).symm).trans <|
        (Category.assoc _ _ _).symm.trans <|
          (congrArg (· ≫ rationalFunctionsMul X ((f : X.functionFieldˣ) : X.functionField))
            (unitToSheafPrincipalCartierDivisor_ι f).symm).trans (Category.assoc _ _ _)

/-- A rank-one local trivialization atlas for `𝒪_X(D)`, indexed by the points of `X`: near `x`,
choose an equation `f` of `D` over a neighbourhood `V`; then `𝒪_X(D)` agrees with `𝒪_X(div f)`
over `V`, and the latter is trivialized by multiplication by `f`. -/
private def localTrivializations (D : CartierDivisor X) :
    TauCeti.SheafOfModules.LocalTrivializations.{u, u, u} D.sheaf := by
  choose f hf using D.exists_isLocalEquationAt
  choose V hx hV using fun x ↦ isLocalEquationAt_iff.mp (hf x)
  exact SheafOfModules.LocalTrivializations.ofForallMem X V hx fun x ↦
    haveI : Nonempty (V x) := ⟨⟨x, hx x⟩⟩
    (SheafOfModules.overFunctor X.ringCatSheaf (V x)).mapIso
      (unitIsoSheafPrincipalCartierDivisor X (f x)) ≪≫
      sheafOverIsoOfRestrictEq _ D (V x)
        ((principalCartierDivisor_restrict X (f x) (V x)).trans (hV x))

/-- **The sheaf of a Cartier divisor is a line bundle.** On an integral scheme, `𝒪_X(D)` is
locally free of rank one: over an open subset on which `f` is an equation of `D`, it is
`f⁻¹ 𝒪_X`. -/
theorem isInvertible_sheaf (D : CartierDivisor X) : SheafOfModules.isInvertible X D.sheaf :=
  D.localTrivializations.isInvertible

/-- The line bundle `𝒪_X(D)` attached to a Cartier divisor `D` on an integral scheme. -/
def toInvertibleSheaf (D : CartierDivisor X) : InvertibleSheaf X :=
  ⟨D.sheaf, D.isInvertible_sheaf⟩

/-- The underlying sheaf of the line bundle attached to `D` is `𝒪_X(D)`. -/
@[simp]
lemma toInvertibleSheaf_obj (D : CartierDivisor X) : D.toInvertibleSheaf.obj = D.sheaf :=
  (rfl)

end CartierDivisor

end Scheme

end

end AlgebraicGeometry

end TauCeti

end
end CartierSource18
