module

public import paper_verification.ambient_zero6
import all paper_verification.ambient_zero6
public import Mathlib.Algebra.Category.ModuleCat.ExteriorPower
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.OfCommRing
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import Mathlib.Algebra.Category.Ring.Limits
public import Mathlib.LinearAlgebra.Matrix.SchurComplement
public import Mathlib.LinearAlgebra.Matrix.Notation
public import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
public import Mathlib.Algebra.Category.ModuleCat.Products
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.Algebra.Category.ModuleCat.Kernels
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Kernels
public import paper_verification.literal005
import all paper_verification.literal005
import Lean.Util.CollectAxioms
import Lean.Util.FoldConsts
import Lean.PrettyPrinter

set_option Elab.async false

section ComponentSource_0
/- Original module: TauCeti.Algebra.Category.ModuleCat.ExteriorPower.RestrictScalars -/
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/


/-!
# Exterior powers and restriction of scalars

Restriction of scalars has a natural exterior-power comparison, sending a wedge over the
source ring to the same wedge over the target ring. It is an isomorphism when the coefficient
map is bijective, though not for an arbitrary ring map. This gives exterior-power restriction
isomorphisms for module presheaves with isomorphic coefficient maps, and for module sheaves
when the coefficient map is an isomorphism and the site functor is also cocontinuous.
The construction uses Mathlib's
`ModuleCat.exteriorPower.desc` and supplies the sectionwise maps
for exterior powers of pushforwards of module presheaves.
-/

public section

open CategoryTheory

namespace TauCeti.ModuleCat

universe u v w

noncomputable section

variable {S : Type u} {R : Type v} [CommRing S] [CommRing R] (f : S →+* R)

private def restrictScalarsExteriorPowerApp (n : ℕ) (M : ModuleCat.{max u v w} R) :
    ((ModuleCat.restrictScalars f).obj M).exteriorPower n ⟶
      (ModuleCat.restrictScalars f).obj (M.exteriorPower n) :=
  ModuleCat.exteriorPower.desc
    { toFun m := ModuleCat.exteriorPower.mk (M := M) m
      map_update_add' m i a b :=
        (ModuleCat.exteriorPower.mk (M := M)).map_update_add m i a b
      map_update_smul' m i r a :=
        (ModuleCat.exteriorPower.mk (M := M)).map_update_smul m i (f r) a
      map_eq_zero_of_eq' m _ _ h hij :=
        (ModuleCat.exteriorPower.mk (M := M)).map_eq_zero_of_eq m h hij }

private lemma restrictScalarsExteriorPowerApp_mk (n : ℕ)
    (M : ModuleCat.{max u v w} R) (m : Fin n → (ModuleCat.restrictScalars f).obj M) :
    restrictScalarsExteriorPowerApp f n M (ModuleCat.exteriorPower.mk m) =
      ModuleCat.exteriorPower.mk (M := M) m :=
  ModuleCat.exteriorPower.desc_mk _ _

/-- Restriction of scalars carries the natural exterior-power comparison, changing the
coefficient ring of a wedge without changing its factors. -/
def restrictScalarsExteriorPowerComparison (n : ℕ) :
    ModuleCat.restrictScalars.{max u v w} f ⋙ ModuleCat.exteriorPower.functor S n ⟶
      ModuleCat.exteriorPower.functor R n ⋙ ModuleCat.restrictScalars f where
  app := restrictScalarsExteriorPowerApp f n
  naturality {M N} φ := by
    dsimp only [Functor.comp_obj, Functor.comp_map, ModuleCat.exteriorPower.functor]
    apply ModuleCat.exteriorPower.hom_ext
    apply ModuleCat.AlternatingMap.ext
    intro m
    simp only [ModuleCat.AlternatingMap.postcomp_apply, ModuleCat.comp_apply,
      ModuleCat.restrictScalars.map_apply, ModuleCat.exteriorPower.map_mk,
      restrictScalarsExteriorPowerApp_mk, Function.comp_def]
    -- Restriction of scalars gives the concrete-category coercions different bundled objects
    -- with the same carriers, preventing `simp` from matching these two wedge formulas.
    exact (restrictScalarsExteriorPowerApp_mk f n N (φ ∘ m)).trans
      (ModuleCat.exteriorPower.map_mk φ m).symm

/-- The restriction-of-scalars comparison preserves the factors of a decomposable wedge. -/
-- Explicit objects keep the coercion to a function in simp normal form.
@[simp]
theorem restrictScalarsExteriorPowerComparison_app_mk (n : ℕ)
    (M : ModuleCat.{max u v w} R) (m : Fin n → (ModuleCat.restrictScalars f).obj M) :
    (ConcreteCategory.hom
      (X := (ModuleCat.exteriorPower.functor S n).obj ((ModuleCat.restrictScalars f).obj M))
      (Y := (ModuleCat.restrictScalars f).obj ((ModuleCat.exteriorPower.functor R n).obj M))
      ((restrictScalarsExteriorPowerComparison f n).app M))
      (ModuleCat.exteriorPower.mk m) = ModuleCat.exteriorPower.mk (M := M) m :=
  restrictScalarsExteriorPowerApp_mk f n M m

-- The reverse wedge map, with the target action transported by the inverse ring map.
private def restrictScalarsExteriorPowerInvAux (e : S ≃+* R) (n : ℕ)
    (M : ModuleCat.{max u v w} R) :
    M.exteriorPower n ⟶ (ModuleCat.restrictScalars e.symm.toRingHom).obj
      (((ModuleCat.restrictScalars e.toRingHom).obj M).exteriorPower n) := by
  let N := (ModuleCat.restrictScalars e.toRingHom).obj M
  let P := (ModuleCat.restrictScalars e.symm.toRingHom).obj (N.exteriorPower n)
  let a : M.AlternatingMap P n :=
    { toFun m := ModuleCat.exteriorPower.mk (M := N) m
      map_update_add' m i a b := (ModuleCat.exteriorPower.mk (M := N)).map_update_add m i a b
      map_update_smul' m i r a := by
        -- The action of `e.symm r` on `N` is the original action of `r` on `M`.
        have hw := (ModuleCat.exteriorPower.mk (M := N)).map_update_smul m i (e.symm r) a
        erw [ModuleCat.restrictScalars.smul_def e.toRingHom, RingEquiv.apply_symm_apply] at hw
        exact hw
      map_eq_zero_of_eq' m _ _ h hij :=
        (ModuleCat.exteriorPower.mk (M := N)).map_eq_zero_of_eq m h hij }
  exact ModuleCat.exteriorPower.desc a

private lemma restrictScalarsExteriorPowerInvAux_mk (e : S ≃+* R) (n : ℕ)
    (M : ModuleCat.{max u v w} R) (m : Fin n → M) :
    restrictScalarsExteriorPowerInvAux e n M (ModuleCat.exteriorPower.mk m) =
      ModuleCat.exteriorPower.mk (M := (ModuleCat.restrictScalars e.toRingHom).obj M) m :=
  ModuleCat.exteriorPower.desc_mk _ m

/-- Restriction along an isomorphism of coefficient rings preserves exterior powers. -/
theorem isIso_restrictScalarsExteriorPowerComparison_app_of_bijective
    (hf : Function.Bijective f) (n : ℕ) (M : ModuleCat.{max u v w} R) :
    IsIso ((restrictScalarsExteriorPowerComparison f n).app M) := by
  let e := RingEquiv.ofBijective f hf
  let : RingHomInvPair e.toRingHom e.symm.toRingHom := RingHomInvPair.of_ringEquiv e
  let N := (ModuleCat.restrictScalars e.toRingHom).obj M
  -- Opposite coefficient changes make both composites linear over their source rings.
  let c : N.exteriorPower n →ₛₗ[e.toRingHom] M.exteriorPower n :=
    (ModuleCat.semilinearMapAddEquiv e.toRingHom _ _).symm
      ((restrictScalarsExteriorPowerComparison e.toRingHom n).app M)
  let h : M.exteriorPower n →ₛₗ[e.symm.toRingHom] N.exteriorPower n :=
    (ModuleCat.semilinearMapAddEquiv e.symm.toRingHom _ _).symm
      (restrictScalarsExteriorPowerInvAux e n M)
  -- Mathlib's evaluation lemma explicitly identifies the semilinear and restricted maps.
  have hc (m : Fin n → N) :
      c (ModuleCat.exteriorPower.mk m) = ModuleCat.exteriorPower.mk (M := M) m := by
    exact (ModuleCat.semilinearMapAddEquiv_symm_apply_apply e.toRingHom _ _ _ _).trans
      (restrictScalarsExteriorPowerApp_mk e.toRingHom n M m)
  have hh (m : Fin n → M) :
      h (ModuleCat.exteriorPower.mk m) = ModuleCat.exteriorPower.mk (M := N) m := by
    exact (ModuleCat.semilinearMapAddEquiv_symm_apply_apply e.symm.toRingHom _ _ _ _).trans
      (restrictScalarsExteriorPowerInvAux_mk e n M m)
  have hleft : Function.LeftInverse h c := by
    have heq : (h.comp c : N.exteriorPower n →ₗ[S] N.exteriorPower n) = LinearMap.id := by
      apply _root_.exteriorPower.linearMap_ext
      apply _root_.AlternatingMap.ext
      intro m
      exact (congrArg h (hc m)).trans (hh m)
    exact fun x ↦ DFunLike.congr_fun heq x
  have hright : Function.RightInverse h c := by
    have heq : (c.comp h : M.exteriorPower n →ₗ[R] M.exteriorPower n) = LinearMap.id := by
      apply _root_.exteriorPower.linearMap_ext
      apply _root_.AlternatingMap.ext
      intro m
      exact (congrArg c (hh m)).trans (hc m)
    exact fun x ↦ DFunLike.congr_fun heq x
  exact (ConcreteCategory.isIso_iff_bijective _).mpr
    ⟨hleft.injective, hright.surjective⟩

end

end TauCeti.ModuleCat
end
end ComponentSource_0

run_cmd Lean.logInfo "COMPONENT_SOURCE_END: TauCeti.Algebra.Category.ModuleCat.ExteriorPower.RestrictScalars"

section ComponentSource_1
/- Original module: TauCeti.Algebra.Category.ModuleCat.Presheaf.ExteriorPower.Basic -/
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/


/-!
# Exterior powers of presheaves of modules

Let `R` be a presheaf of commutative rings on a category `C`. For a presheaf of `R`-modules `M`
and `n : ℕ`, the `n`-th exterior power of `M` is the presheaf of modules whose sections over `X`
are the exterior power `⋀[R.obj X]^n (M.obj X)` (Mathlib's `ModuleCat.exteriorPower`), and whose
restriction along `f : X ⟶ Y` sends `m₁ ∧ ⋯ ∧ mₙ` to `M.map f m₁ ∧ ⋯ ∧ M.map f mₙ`. This is the
presheaf-level input to exterior powers of sheaves of modules, which are obtained by
sheafification. As for Mathlib's monoidal structure on these presheaves of modules
(`PresheafOfModulesOfCommRing.monoidalCategoryStruct`), modules are taken in the universe of the
rings.

## Main declarations

* `PresheafOfModulesOfCommRing.exteriorPower n` is the `n`-th exterior power, as an
  endofunctor of presheaves of `R`-modules; `exteriorPower_obj_obj`, `exteriorPower_obj_map_mk`
  and `exteriorPower_map_app` compute its sections, restriction maps and action on morphisms;
* `PresheafOfModulesOfCommRing.exteriorPowerZeroIso` identifies the zeroth exterior power
  with the constant functor at the unit presheaf of modules `R`;
* `PresheafOfModulesOfCommRing.exteriorPowerOneIso` identifies the first exterior power
  with the identity functor.
-/

public section

open CategoryTheory

universe u v w

noncomputable section

namespace PresheafOfModulesOfCommRing

variable {C : Type v} [Category.{w} C] {R : Cᵒᵖ ⥤ CommRingCat.{u}}

/-- Auxiliary definition for `exteriorPower`: the restriction maps of the exterior power of a
presheaf of modules, sending `m₁ ∧ ⋯ ∧ mₙ` to `M.map f m₁ ∧ ⋯ ∧ M.map f mₙ`. -/
def exteriorPowerObjMap (M : PresheafOfModulesOfCommRing.{u} R) (n : ℕ) {X Y : Cᵒᵖ}
    (f : X ⟶ Y) :
    (M.obj X).exteriorPower n ⟶
      (ModuleCat.restrictScalars (R.map f).hom).obj ((M.obj Y).exteriorPower n) :=
  ModuleCat.exteriorPower.map (M.map f) n ≫
    (TauCeti.ModuleCat.restrictScalarsExteriorPowerComparison (R.map f).hom n).app (M.obj Y)

set_option maxHeartbeats 1000000 in
/-- The restriction maps of the exterior power on decomposable elements. -/
lemma exteriorPowerObjMap_mk (M : PresheafOfModulesOfCommRing.{u} R) (n : ℕ) {X Y : Cᵒᵖ}
    (f : X ⟶ Y) (x : Fin n → M.obj X) :
    exteriorPowerObjMap M n f (ModuleCat.exteriorPower.mk x) =
      ModuleCat.exteriorPower.mk (M := M.obj Y) fun j ↦ M.map f (x j) := by
  exact (congrArg
    (fun z ↦ (TauCeti.ModuleCat.restrictScalarsExteriorPowerComparison
      (R.map f).hom n).app (M.obj Y) z)
    (ModuleCat.exteriorPower.map_mk (M.map f) x)).trans
    (TauCeti.ModuleCat.restrictScalarsExteriorPowerComparison_app_mk
      (R.map f).hom n (M.obj Y) _)

/-- Auxiliary definition for `exteriorPower`: the exterior power of a presheaf of modules. -/
@[expose]
def exteriorPowerObj (M : PresheafOfModulesOfCommRing.{u} R) (n : ℕ) :
    PresheafOfModulesOfCommRing.{u} R :=
  PresheafOfModulesOfCommRing.mk (fun X ↦ (M.obj X).exteriorPower n)
    (fun f ↦ exteriorPowerObjMap M n f)
    (fun X ↦ ModuleCat.exteriorPower.hom_ext (by
      ext x
      simp only [ModuleCat.AlternatingMap.postcomp_apply, exteriorPowerObjMap_mk,
        PresheafOfModules.map_id, ModuleCat.restrictScalarsId'_inv_app,
        ModuleCat.restrictScalarsId'App_inv_apply]
      rfl))
    (fun {_ _ Z} f g ↦ ModuleCat.exteriorPower.hom_ext (by
      ext x
      refine (exteriorPowerObjMap_mk M n (f ≫ g) x).trans ?_
      -- the restriction-of-scalars comparison maps on the right are identities on elements
      exact (congrArg (ModuleCat.exteriorPower.mk (M := M.obj Z) (n := n))
        (funext fun j ↦ M.map_comp_apply f g (x j))).trans
          ((congrArg (exteriorPowerObjMap M n g) (exteriorPowerObjMap_mk M n f x)).trans
            (exteriorPowerObjMap_mk M n g _)).symm))

/-- The restriction maps of the exterior power are natural in the presheaf of modules. -/
lemma exteriorPowerObjMap_naturality {M N : PresheafOfModulesOfCommRing.{u} R} (φ : M ⟶ N)
    (n : ℕ) {X Y : Cᵒᵖ} (f : X ⟶ Y) :
    exteriorPowerObjMap M n f ≫ (ModuleCat.restrictScalars (R.map f).hom).map
        (ModuleCat.exteriorPower.map (φ.app' Y) n) =
      ModuleCat.exteriorPower.map (φ.app' X) n ≫ exteriorPowerObjMap N n f :=
  ModuleCat.exteriorPower.hom_ext (by
    ext x
    refine ((congrArg (ModuleCat.exteriorPower.map (φ.app' Y) n)
      (exteriorPowerObjMap_mk M n f x)).trans (ModuleCat.exteriorPower.map_mk _ _)).trans ?_
    refine Eq.trans ?_ ((congrArg (exteriorPowerObjMap N n f)
      (ModuleCat.exteriorPower.map_mk _ _)).trans (exteriorPowerObjMap_mk N n f _)).symm
    exact congrArg (ModuleCat.exteriorPower.mk (M := N.obj Y) (n := n))
      (funext fun j ↦ PresheafOfModulesOfCommRing.naturality_apply φ f (x j)))

/-- The `n`-th exterior power of presheaves of modules over a presheaf of commutative rings,
computed sectionwise: its sections over `X` are `⋀[R.obj X]^n (M.obj X)`, and its restriction maps
send `m₁ ∧ ⋯ ∧ mₙ` to the wedge product of the restrictions of the `mᵢ`. -/
@[expose]
def exteriorPower (n : ℕ) :
    PresheafOfModulesOfCommRing.{u} R ⥤ PresheafOfModulesOfCommRing.{u} R where
  obj M := exteriorPowerObj M n
  map φ := PresheafOfModulesOfCommRing.homMk
    (fun X ↦ ModuleCat.exteriorPower.map (φ.app' X) n)
    (fun f ↦ exteriorPowerObjMap_naturality φ n f)
  map_id M := by
    ext X : 1
    exact (ModuleCat.exteriorPower.functor _ n).map_id (M.obj X)
  map_comp φ ψ := by
    ext X : 1
    exact (ModuleCat.exteriorPower.functor _ n).map_comp (φ.app' X) (ψ.app' X)

/-- The sections of the exterior power over `X` are the exterior power of the sections. -/
lemma exteriorPower_obj_obj (n : ℕ) (M : PresheafOfModulesOfCommRing.{u} R) (X : Cᵒᵖ) :
    ((exteriorPower n).obj M).obj X = (M.obj X).exteriorPower n :=
  rfl

/-- The restriction maps of the exterior power restrict each factor of a wedge product. -/
@[simp]
lemma exteriorPower_obj_map_mk (n : ℕ) (M : PresheafOfModulesOfCommRing.{u} R) {X Y : Cᵒᵖ}
    (f : X ⟶ Y) (x : Fin n → M.obj X) :
    ((exteriorPower n).obj M).map f (ModuleCat.exteriorPower.mk x) =
      ModuleCat.exteriorPower.mk (M := M.obj Y) fun j ↦ M.map f (x j) :=
  exteriorPowerObjMap_mk M n f x

/-- The exterior power of a morphism is computed sectionwise. -/
@[simp]
lemma exteriorPower_map_app (n : ℕ) {M N : PresheafOfModulesOfCommRing.{u} R} (φ : M ⟶ N)
    (X : Cᵒᵖ) :
    ((exteriorPower n).map φ).app X = ModuleCat.exteriorPower.map (φ.app' X) n :=
  rfl

variable (R) in
/-- The zeroth exterior power of a presheaf of `R`-modules is the unit presheaf of modules `R`,
naturally; on sections it is `ModuleCat.exteriorPower.iso₀`. -/
def exteriorPowerZeroIso :
    exteriorPower (R := R) 0 ≅ (Functor.const _).obj (PresheafOfModulesOfCommRing.unit R) :=
  NatIso.ofComponents
    (fun M ↦ PresheafOfModulesOfCommRing.isoMk
      (fun X ↦ ModuleCat.exteriorPower.iso₀ (M.obj X))
      (fun X Y f ↦ ModuleCat.exteriorPower.hom_ext (by
        ext x
        refine ((congrArg (ModuleCat.exteriorPower.iso₀ (M.obj Y)).hom
          (exteriorPower_obj_map_mk 0 M f x)).trans
            (ModuleCat.exteriorPower.iso₀_hom_apply _)).trans ?_
        exact ((congrArg ((PresheafOfModulesOfCommRing.unit R).map f)
          (ModuleCat.exteriorPower.iso₀_hom_apply x)).trans
            (PresheafOfModules.unit_map_one _ f)).symm)))
    (fun φ ↦ by
      ext X : 1
      exact ModuleCat.exteriorPower.iso₀_hom_naturality (φ.app' X))

@[simp]
lemma exteriorPowerZeroIso_hom_app_app (M : PresheafOfModulesOfCommRing.{u} R) (X : Cᵒᵖ) :
    ((exteriorPowerZeroIso R).hom.app M).app X = (ModuleCat.exteriorPower.iso₀ (M.obj X)).hom :=
  (rfl)

@[simp]
lemma exteriorPowerZeroIso_inv_app_app (M : PresheafOfModulesOfCommRing.{u} R) (X : Cᵒᵖ) :
    ((exteriorPowerZeroIso R).inv.app M).app X = (ModuleCat.exteriorPower.iso₀ (M.obj X)).inv :=
  (rfl)

variable (R) in
/-- The first exterior power of a presheaf of `R`-modules is the presheaf of modules itself,
naturally; on sections it is `ModuleCat.exteriorPower.iso₁`. -/
def exteriorPowerOneIso : exteriorPower (R := R) 1 ≅ 𝟭 _ :=
  NatIso.ofComponents
    (fun M ↦ PresheafOfModulesOfCommRing.isoMk
      (fun X ↦ ModuleCat.exteriorPower.iso₁ (M.obj X))
      (fun X Y f ↦ ModuleCat.exteriorPower.hom_ext (by
        ext x
        refine ((congrArg (ModuleCat.exteriorPower.iso₁ (M.obj Y)).hom
          (exteriorPower_obj_map_mk 1 M f x)).trans
            (ModuleCat.exteriorPower.iso₁_hom_apply _)).trans ?_
        exact congrArg (M.map f) (ModuleCat.exteriorPower.iso₁_hom_apply x).symm)))
    (fun φ ↦ by
      ext X : 1
      exact ModuleCat.exteriorPower.iso₁_hom_naturality (φ.app' X))

@[simp]
lemma exteriorPowerOneIso_hom_app_app (M : PresheafOfModulesOfCommRing.{u} R) (X : Cᵒᵖ) :
    ((exteriorPowerOneIso R).hom.app M).app X = (ModuleCat.exteriorPower.iso₁ (M.obj X)).hom :=
  (rfl)

@[simp]
lemma exteriorPowerOneIso_inv_app_app (M : PresheafOfModulesOfCommRing.{u} R) (X : Cᵒᵖ) :
    ((exteriorPowerOneIso R).inv.app M).app X = (ModuleCat.exteriorPower.iso₁ (M.obj X)).inv :=
  (rfl)

end PresheafOfModulesOfCommRing

end
end
end ComponentSource_1

run_cmd Lean.logInfo "COMPONENT_SOURCE_END: TauCeti.Algebra.Category.ModuleCat.Presheaf.ExteriorPower.Basic"

section ComponentSource_2
/- Original module: PaperVerification.AlternatingSectionPresheaf -/


/-!
# Alternating forms as genuine morphisms of module presheaves

A list of coordinate functions on a module presheaf and a compatible family
of coefficients define a functional on its second exterior power.  The
formula on every open is the original alternating coefficient formula;
restriction compatibility is proved using the coefficient-ring maps.
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false

open CategoryTheory
open scoped BigOperators

universe u v w

namespace PaperVerification.AlternatingSectionPresheaf

open AlternatingSectionAlgebra

variable {C : Type v} [Category.{w} C] {R : Cᵒᵖ ⥤ CommRingCat.{u}}
variable {M : PresheafOfModulesOfCommRing.{u} R}
variable {P N : Type u} [Fintype P]
variable (a b : P → N)
variable (coord : N → (M ⟶ PresheafOfModulesOfCommRing.unit R))
variable (c : P → (PresheafOfModulesOfCommRing.unit R).sections)

-- The unit module has exactly the original ring of sections as its carrier.
local instance (X : Cᵒᵖ) : CommRing ((PresheafOfModulesOfCommRing.unit R).obj X) :=
  inferInstanceAs (CommRing (R.obj X))

/-- The original coordinate functions evaluated on sections over an object. -/
def coordinates (X : Cᵒᵖ) : M.obj X →ₗ[R.obj X] (N → R.obj X) :=
  LinearMap.pi fun i ↦ ((coord i).app' X).hom

/-- The alternating map on local sections with the prescribed coefficients. -/
def localForm (X : Cᵒᵖ) :
    (M.obj X).AlternatingMap ((PresheafOfModulesOfCommRing.unit R).obj X) 2 :=
  (coefficientForm (R := R.obj X) a b (fun p ↦ (c p).eval X)).compLinearMap (coordinates coord X)

@[simp] theorem localForm_apply (X : Cᵒᵖ) (v : Fin 2 → M.obj X) :
    localForm a b coord c X v =
      ∑ p, (c p).eval X *
        ((coord (a p)).app' X (v 0) * (coord (b p)).app' X (v 1) -
         (coord (b p)).app' X (v 0) * (coord (a p)).app' X (v 1)) := by
  exact coefficientForm_apply a b (fun p ↦ (c p).eval X)
    (fun i ↦ coordinates coord X (v i))

/-- Restricting a local form agrees with evaluating it on restricted vectors. -/
theorem localForm_naturality {X Y : Cᵒᵖ} (f : X ⟶ Y)
    (v : Fin 2 → M.obj X) :
    localForm a b coord c Y (fun i ↦ M.map f (v i)) =
      (PresheafOfModulesOfCommRing.unit R).map f (localForm a b coord c X v) := by
  have hc (p : P) : (c p).eval Y = (R.map f) ((c p).eval X) :=
    (PresheafOfModules.sections_property (c p) f).symm
  have hv (i : N) (j : Fin 2) :
      (coord i).app' Y (M.map f (v j)) = (R.map f) ((coord i).app' X (v j)) :=
    PresheafOfModulesOfCommRing.naturality_apply (coord i) f (v j)
  change localForm a b coord c Y (fun i ↦ M.map f (v i)) =
    (R.map f) (localForm a b coord c X v)
  simp only [localForm_apply, map_sum, map_mul, map_sub, hc, hv]

/-- The actual morphism from the second exterior-power presheaf to the
structure presheaf, obtained by the universal property on every object. -/
def functional :
    (PresheafOfModulesOfCommRing.exteriorPower 2).obj M ⟶
      PresheafOfModulesOfCommRing.unit R :=
  PresheafOfModulesOfCommRing.homMk
    (fun X ↦ ModuleCat.exteriorPower.desc (localForm a b coord c X))
    (fun {X Y} f ↦ by
      apply ModuleCat.exteriorPower.hom_ext
      apply ModuleCat.AlternatingMap.ext
      intro v
      change ModuleCat.exteriorPower.desc (localForm a b coord c Y)
          (((PresheafOfModulesOfCommRing.exteriorPower 2).obj M).map f
            (ModuleCat.exteriorPower.mk v)) =
        (PresheafOfModulesOfCommRing.unit R).map f
          (ModuleCat.exteriorPower.desc (localForm a b coord c X)
            (ModuleCat.exteriorPower.mk v))
      rw [PresheafOfModulesOfCommRing.exteriorPower_obj_map_mk,
        ModuleCat.exteriorPower.desc_mk, ModuleCat.exteriorPower.desc_mk]
      exact localForm_naturality a b coord c f v)

/-- The presheaf functional evaluates decomposable wedges by exactly the
coefficient formula, with no chosen presentation of the exterior power. -/
@[simp] theorem functional_app_mk (X : Cᵒᵖ) (v : Fin 2 → M.obj X) :
    (functional a b coord c).app' X (ModuleCat.exteriorPower.mk v) =
      ∑ p, (c p).eval X *
        ((coord (a p)).app' X (v 0) * (coord (b p)).app' X (v 1) -
         (coord (b p)).app' X (v 0) * (coord (a p)).app' X (v 1)) :=
  (ModuleCat.exteriorPower.desc_mk _ v).trans (localForm_apply a b coord c X v)

end PaperVerification.AlternatingSectionPresheaf
end
end
end ComponentSource_2

run_cmd Lean.logInfo "COMPONENT_SOURCE_END: PaperVerification.AlternatingSectionPresheaf"

section ComponentSource_3
/- Original module: TauCeti.Algebra.Category.ModuleCat.Sheaf.Defs -/
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
  underlying presheaf, naturally (`SheafOfModules.sheafificationIso_inv_naturality`);
* `SheafOfModules.unit_comp_val_sheafification_map_comp_sheafificationIso_hom`: the
  sheafification of a morphism to a sheaf restricts to that morphism along the sheafification map.

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

/-- On the sheafification map of a presheaf of modules `P`, the sheafification of a morphism
`g : P ⟶ M` to a sheaf, followed by `sheafificationIso`, is `g`. -/
theorem unit_comp_val_sheafification_map_comp_sheafificationIso_hom {R : Sheaf J RingCat.{u}}
    {P : PresheafOfModules.{v} R.obj} {M : SheafOfModules.{v} R} (g : P ⟶ M.val) :
    (PresheafOfModules.sheafificationAdjunction (𝟙 R.obj)).unit.app P ≫
      ((PresheafOfModules.sheafification (𝟙 R.obj)).map g ≫ (sheafificationIso R M).hom).val =
    g := by
  rw [sheafificationIso_hom]
  -- Move `g` past the sheafification map, then use a triangle identity.
  let adj := PresheafOfModules.sheafificationAdjunction (𝟙 R.obj)
  exact (adj.unit.naturality_assoc _ _).symm.trans
    ((congrArg (g ≫ ·) (adj.right_triangle_components M)).trans (Category.comp_id _))

end SheafOfModules

end


end TauCeti
end
end ComponentSource_3

run_cmd Lean.logInfo "COMPONENT_SOURCE_END: TauCeti.Algebra.Category.ModuleCat.Sheaf.Defs"

section ComponentSource_4
/- Original module: PaperVerification.AlternatingSectionSheaf -/


/-!
# The global sheaf functional defined by an alternating form

The domain is the sheafification of the sectionwise second exterior power.
Thus this is a morphism from the actual exterior-power sheaf, and not just
a collection of formulas in a chosen frame.  The final theorem computes
it on sheafified wedges, retaining the original coefficients and signs.
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false

open CategoryTheory
open scoped BigOperators
open TauCeti.SheafOfModules (ringCatSheaf)

universe u v w

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

local instance (X : Cᵒᵖ) : CommRing ((ringCatSheaf R).obj.obj X) :=
  inferInstanceAs (CommRing (R.obj.obj X))

local instance (X : Cᵒᵖ) : CommRing ((SheafOfModules.unit (ringCatSheaf R)).val.obj X) :=
  inferInstanceAs (CommRing (R.obj.obj X))

/-- Sheafification of the local alternating functional, followed by the
canonical identification of the sheafified structure sheaf with itself. -/
def functional :
    (PresheafOfModules.sheafification (𝟙 (ringCatSheaf R).obj)).obj
        ((PresheafOfModulesOfCommRing.exteriorPower 2).obj M.val) ⟶
      SheafOfModules.unit (ringCatSheaf R) :=
  (PresheafOfModules.sheafification (𝟙 (ringCatSheaf R).obj)).map
      (AlternatingSectionPresheaf.functional a b (fun i ↦ (coord i).val) c) ≫
    (TauCeti.SheafOfModules.sheafificationIso (ringCatSheaf R)
      (SheafOfModules.unit (ringCatSheaf R))).hom

/-- The global functional restricts to the original local functional along
the actual sheafification map. -/
theorem unit_comp_functional :
    (PresheafOfModules.sheafificationAdjunction (𝟙 (ringCatSheaf R).obj)).unit.app
        ((PresheafOfModulesOfCommRing.exteriorPower 2).obj M.val) ≫
      (functional a b coord c).val =
    AlternatingSectionPresheaf.functional a b (fun i ↦ (coord i).val) c :=
  TauCeti.SheafOfModules.unit_comp_val_sheafification_map_comp_sheafificationIso_hom _

/-- On every open, the sheaf functional evaluates a sheafified wedge by
the alternating coefficient formula. -/
theorem functional_app_sheafified_wedge (X : Cᵒᵖ) (v : Fin 2 → M.val.obj X) :
    (functional a b coord c).val.app X
        (((PresheafOfModules.sheafificationAdjunction
            (𝟙 (ringCatSheaf R).obj)).unit.app
          ((PresheafOfModulesOfCommRing.exteriorPower 2).obj M.val)).app X
            (ModuleCat.exteriorPower.mk v)) =
      ∑ p, (c p).eval X *
        ((coord (a p)).val.app X (v 0) * (coord (b p)).val.app X (v 1) -
         (coord (b p)).val.app X (v 0) * (coord (a p)).val.app X (v 1)) := by
  have h := ConcreteCategory.congr_hom
    (congrArg (fun f ↦ f.app X) (unit_comp_functional a b coord c))
    (ModuleCat.exteriorPower.mk v)
  exact h.trans
    (AlternatingSectionPresheaf.functional_app_mk a b (fun i ↦ (coord i).val) c X v)

end PaperVerification.AlternatingSectionSheaf
end
end
end ComponentSource_4

run_cmd Lean.logInfo "COMPONENT_SOURCE_END: PaperVerification.AlternatingSectionSheaf"

section ComponentSource_5
/- Original module: PaperVerification.AlternatingSectionVanishing -/


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
end
end
end ComponentSource_5

run_cmd Lean.logInfo "COMPONENT_SOURCE_END: PaperVerification.AlternatingSectionVanishing"

section ComponentSource_6
/- Original module: PaperVerification.NormalizedTautologicalKernel -/


/-!
# The tautological kernel on a normalized matrix chart

A vector belongs to the span of the normalized rows precisely when every
augmented maximal minor vanishes. The proof works over every commutative ring,
including nonreduced rings. The pivot projection is an explicit inverse to the
row-coordinate map, so the resulting kernel is genuinely free of rank `s`.
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators Matrix

namespace PaperVerification.NormalizedTautologicalKernel

variable {R : Type*} [CommRing R] {s n : ℕ}

def augmented (A : Matrix (Fin s) (Fin n) R) (v : Fin n → R) :
    Matrix (Fin (s+1)) (Fin n) R := Fin.cons v A

/-- Every coordinate of the exterior product of a vector with the row wedge.
Repeated column words are retained; their determinants vanish automatically. -/
def incidence (A : Matrix (Fin s) (Fin n) R) (v : Fin n → R)
    (J : Fin (s+1) → Fin n) : R :=
  Matrix.det ((augmented A v).submatrix id J)

private def oneTailEquiv (s : ℕ) : Fin 1 ⊕ Fin s ≃ Fin (s+1) :=
  (finSumFinEquiv : Fin 1 ⊕ Fin s ≃ Fin (1+s)).trans (finCongr (by omega))

@[simp] private lemma oneTailEquiv_zero (s : ℕ) :
    oneTailEquiv s (Sum.inl 0)=0 := by
  apply Fin.ext
  simp [oneTailEquiv]

@[simp] private lemma oneTailEquiv_succ (s : ℕ) (i : Fin s) :
    oneTailEquiv s (Sum.inr i)=i.succ := by
  apply Fin.ext
  simp [oneTailEquiv]

/-- The augmented minor on one arbitrary column and all pivot columns is
exactly the error in the corresponding row-span equation. -/
theorem incidence_pivot_columns
    (A : Matrix (Fin s) (Fin n) R) (p : Fin s → Fin n)
    (hp : A.submatrix id p=1) (v : Fin n → R) (j : Fin n) :
    incidence A v (Fin.cons j p) = v j - ∑ i, v (p i)*A i j := by
  classical
  let M := (augmented A v).submatrix id (Fin.cons j p)
  let B : Matrix (Fin 1) (Fin s) R := fun _ i => v (p i)
  let C : Matrix (Fin s) (Fin 1) R := fun i _ => A i j
  let D : Matrix (Fin 1) (Fin 1) R := fun _ _ => v j
  have hp' (a b : Fin s) : A a (p b)=(1 : Matrix (Fin s) (Fin s) R) a b :=
    congrFun (congrFun hp a) b
  have hb : M.submatrix (oneTailEquiv s) (oneTailEquiv s)=
      Matrix.fromBlocks D B C 1 := by
    ext a b
    cases a with
    | inl a =>
      have ha : a=0 := Subsingleton.elim _ _
      subst a
      cases b with
      | inl b =>
        have hb : b=0 := Subsingleton.elim _ _
        subst b
        simp [M,D,augmented,Matrix.submatrix]
      | inr b => simp [M,B,augmented,Matrix.submatrix]
    | inr a =>
      cases b with
      | inl b =>
        have hb : b=0 := Subsingleton.elim _ _
        subst b
        simp [M,C,augmented,Matrix.submatrix]
      | inr b => simp [M,augmented,Matrix.submatrix,hp']
  change Matrix.det M = _
  rw [← Matrix.det_submatrix_equiv_self (oneTailEquiv s) M,hb,
    Matrix.det_fromBlocks_one₂₂]
  simp [D,B,C,Matrix.det_unique,Matrix.sub_apply,Matrix.mul_apply]

/-- A linear combination of the rows has zero exterior product with them. -/
theorem incidence_rowCombination (A : Matrix (Fin s) (Fin n) R)
    (x : Fin s → R) (J : Fin (s+1) → Fin n) :
    incidence A (x ᵥ* A) J=0 := by
  classical
  let M := (augmented A 0).submatrix id J
  let c : Fin (s+1) → R := Fin.cons 0 x
  have h := Matrix.det_updateRow_sum M (0 : Fin (s+1)) c
  have he : M.updateRow 0 (∑ i, c i • M i)=
      (augmented A (x ᵥ* A)).submatrix id J := by
    ext i j
    refine Fin.cases ?_ (fun i => ?_) i
    · simp [M,c,augmented,Matrix.updateRow,Function.update,
        Matrix.submatrix,Fin.sum_univ_succ,Matrix.vecMul,dotProduct,Finset.sum_apply]
    · simp [M,c,augmented,Matrix.updateRow,Function.update,Matrix.submatrix,Fin.succ_ne_zero]
  rw [he] at h
  simpa only [c,Fin.cons_zero,zero_smul,incidence] using h

/-- The complete kernel is the original row span, with its explicit pivot
coordinates. No field-valued-point or radical argument is involved. -/
theorem incidence_zero_iff_rowCombination
    (A : Matrix (Fin s) (Fin n) R) (p : Fin s → Fin n)
    (hp : A.submatrix id p=1) (v : Fin n → R) :
    (∀ J, incidence A v J=0) ↔ v=(fun i => v (p i)) ᵥ* A := by
  constructor
  · intro h
    funext j
    have hj := h (Fin.cons j p)
    rw [incidence_pivot_columns A p hp] at hj
    exact sub_eq_zero.mp hj
  · intro h J
    rw [h]
    exact incidence_rowCombination A _ J

/-- Projection to the pivot columns recovers every row-coordinate vector. -/
theorem rowCombination_pivot
    (A : Matrix (Fin s) (Fin n) R) (p : Fin s → Fin n)
    (hp : A.submatrix id p=1) (x : Fin s → R) (i : Fin s) :
    (x ᵥ* A) (p i)=x i := by
  have h : x ᵥ* (A.submatrix id p)=x := by rw [hp,Matrix.vecMul_one]
  exact congrFun h i

end PaperVerification.NormalizedTautologicalKernel
end
end
end ComponentSource_6

run_cmd Lean.logInfo "COMPONENT_SOURCE_END: PaperVerification.NormalizedTautologicalKernel"

section ComponentSource_7
/- Original module: PaperVerification.NormalizedTautologicalFrame -/


/-!
# The explicit free frame of the exterior-incidence kernel

The equations are the augmented determinants, and the linear equivalence is
the original row map with pivot projection as inverse. This construction is
valid over an arbitrary commutative ring.
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators Matrix

namespace PaperVerification.NormalizedTautologicalKernel

variable {R : Type*} [CommRing R] {s n : ℕ}

theorem incidence_eq_sum (A : Matrix (Fin s) (Fin n) R)
    (v : Fin n → R) (J : Fin (s+1) → Fin n) :
    incidence A v J = ∑ q : Fin (s+1), (-1 : R)^q.val * v (J q) *
      Matrix.det (A.submatrix id (fun z => J (q.succAbove z))) := by
  rw [incidence, Matrix.det_succ_row_zero]
  apply Finset.sum_congr rfl
  intro q hq
  simp only [augmented, Matrix.submatrix, Matrix.of_apply, Fin.cons_zero, Fin.cons_succ,
    id_eq]

/-- The actual exterior-incidence equations, assembled as a linear map. -/
def incidenceLinearMap (A : Matrix (Fin s) (Fin n) R) :
    (Fin n → R) →ₗ[R] ((Fin (s+1) → Fin n) → R) where
  toFun v J := incidence A v J
  map_add' v w := by
    funext J
    simp only [incidence_eq_sum, Pi.add_apply, mul_add, add_mul,
      Finset.sum_add_distrib]
  map_smul' r v := by
    funext J
    simp only [incidence_eq_sum, Pi.smul_apply, smul_eq_mul, RingHom.id_apply,
      Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro q hq
    ring

/-- The normalized rows give a free frame of the genuine incidence kernel. -/
def incidenceKernelEquiv (A : Matrix (Fin s) (Fin n) R)
    (p : Fin s → Fin n) (hp : A.submatrix id p=1) :
    (Fin s → R) ≃ₗ[R] (incidenceLinearMap A).ker where
  toFun x := ⟨x ᵥ* A, by
    apply LinearMap.mem_ker.mpr
    funext J
    exact incidence_rowCombination A x J⟩
  invFun v i := v.val (p i)
  left_inv x := by
    funext i
    exact rowCombination_pivot A p hp x i
  right_inv v := by
    apply Subtype.ext
    have h : ∀ J, incidence A v.val J=0 := fun J =>
      congrFun (LinearMap.mem_ker.mp v.property) J
    exact ((incidence_zero_iff_rowCombination A p hp v.val).mp h).symm
  map_add' x y := by
    apply Subtype.ext
    exact (A.vecMulLinear).map_add x y
  map_smul' r x := by
    apply Subtype.ext
    exact (A.vecMulLinear).map_smul r x

@[simp] theorem incidenceKernelEquiv_apply (A : Matrix (Fin s) (Fin n) R)
    (p : Fin s → Fin n) (hp : A.submatrix id p=1) (x : Fin s → R) :
    (incidenceKernelEquiv A p hp x).val=x ᵥ* A := rfl

@[simp] theorem incidenceKernelEquiv_symm_apply (A : Matrix (Fin s) (Fin n) R)
    (p : Fin s → Fin n) (hp : A.submatrix id p=1)
    (v : (incidenceLinearMap A).ker) (i : Fin s) :
    (incidenceKernelEquiv A p hp).symm v i=v.val (p i) := rfl

/-- Normalization is preserved by every coefficient-ring homomorphism. -/
theorem pivot_map {S : Type*} [CommRing S] (φ : R →+* S)
    (A : Matrix (Fin s) (Fin n) R) (p : Fin s → Fin n)
    (hp : A.submatrix id p=1) : (A.map φ).submatrix id p=1 := by
  change φ.mapMatrix (A.submatrix id p)=1
  rw [hp,map_one]

/-- For any presentation of the same actual incidence equations, pivot
projection identifies its kernel with the free coordinate module. -/
theorem kernel_pivot_bijective
    {M N : Type*} [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N]
    (f : M →ₗ[R] N) (e : M ≃ₗ[R] (Fin n → R))
    (A : Matrix (Fin s) (Fin n) R) (p : Fin s → Fin n)
    (hp : A.submatrix id p=1)
    (h : ∀ x, f x=0 ↔ ∀ J, incidence A (e x) J=0) :
    Function.Bijective (fun x : f.ker => fun i => e x.val (p i)) := by
  constructor
  · intro x y hxy
    apply Subtype.ext
    apply e.injective
    have hx := (incidence_zero_iff_rowCombination A p hp (e x.val)).mp
      ((h x.val).mp (LinearMap.mem_ker.mp x.property))
    have hy := (incidence_zero_iff_rowCombination A p hp (e y.val)).mp
      ((h y.val).mp (LinearMap.mem_ker.mp y.property))
    rw [hx, hy]
    exact congrArg (fun c : Fin s → R => c ᵥ* A) hxy
  · intro c
    let v := e.symm (c ᵥ* A)
    have hv : f v=0 := (h v).mpr (by
      intro J
      change incidence A (e (e.symm (c ᵥ* A))) J=0
      rw [e.apply_symm_apply]
      exact incidence_rowCombination A c J)
    refine ⟨⟨v,LinearMap.mem_ker.mpr hv⟩,?_⟩
    funext i
    change e (e.symm (c ᵥ* A)) (p i)=c i
    rw [e.apply_symm_apply]
    exact rowCombination_pivot A p hp c i

end PaperVerification.NormalizedTautologicalKernel
end
end
end ComponentSource_7

run_cmd Lean.logInfo "COMPONENT_SOURCE_END: PaperVerification.NormalizedTautologicalFrame"

section ComponentSource_8
/- Original module: PaperVerification.SheafModulePowers -/


/-!
# Concrete sections of powers of a module sheaf

Products and kernels are the actual categorical constructions on sheaves of
modules. Evaluation preserves these limits. The comparison below identifies
sections of a power with tuples of sections, compatibly with every projection.
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CategoryTheory.Limits Opposite

namespace PaperVerification.SheafModulePowers

universe u
variable {X : AlgebraicGeometry.Scheme.{u}}

def power (M : X.Modules) (I : Type u) : X.Modules := ∏ᶜ (fun _ : I => M)

/-- A power of the actual structure module. For finite `I` this is `𝒪^I`. -/
def structurePower (X : AlgebraicGeometry.Scheme.{u}) (I : Type u) : X.Modules :=
  power (X:=X) (SheafOfModules.unit X.ringCatSheaf) I

/-- Coordinate reindexing between genuine categorical powers. -/
def reindex (M : X.Modules) (I J : Type u) (f : J → I) :
    power M I ⟶ power M J :=
  Pi.lift fun j ↦ Pi.π (fun _ : I ↦ M) (f j)

/-- Reindexing retains each specified coordinate projection. -/
theorem reindex_projection (M : X.Modules) (I J : Type u) (f : J → I) (j : J) :
    reindex M I J f ≫ Pi.π (fun _ : J ↦ M) j = Pi.π (fun _ : I ↦ M) (f j) := by
  unfold reindex
  exact Pi.lift_comp_π _ j

/-- The section comparison is induced by the genuine product projections. -/
def sectionsIso (M : X.Modules) (I : Type u) (U : X.Opens) :
    (SheafOfModules.evaluation X.ringCatSheaf (op U)).obj (power M I) ≅
      ModuleCat.of (X.ringCatSheaf.obj.obj (op U))
        (I → M.val.obj (op U)) :=
  PreservesProduct.iso (SheafOfModules.evaluation X.ringCatSheaf (op U))
      (fun _ : I => M) ≪≫
    ModuleCat.piIsoPi (fun _ : I => M.val.obj (op U))

def sectionsEquiv (M : X.Modules) (I : Type u) (U : X.Opens) :
    (power M I).val.obj (op U) ≃ₗ[X.ringCatSheaf.obj.obj (op U)]
      (I → M.val.obj (op U)) :=
  (sectionsIso M I U).toLinearEquiv

@[simp] theorem sectionsEquiv_apply (M : X.Modules) (I : Type u) (U : X.Opens)
    (x : (power M I).val.obj (op U)) (i : I) :
    sectionsEquiv M I U x i = (Pi.π (fun _ : I => M) i).val.app (op U) x := by
  have h : (sectionsIso M I U).hom ≫
      ModuleCat.ofHom (LinearMap.proj i) =
        (SheafOfModules.evaluation X.ringCatSheaf (op U)).map
          (Pi.π (fun _ : I => M) i) := by
    simp only [sectionsIso, Iso.trans_hom, Category.assoc,
      ModuleCat.piIsoPi_hom_ker_subtype, PreservesProduct.iso_hom]
    exact piComparison_comp_π (SheafOfModules.evaluation X.ringCatSheaf (op U))
      (fun _ : I => M) i
  exact congrArg (fun f => f x) h

/-- Equalities of tuples detect equalities of actual sections. -/
theorem sections_ext (M : X.Modules) (I : Type u) (U : X.Opens)
    {x y : (power M I).val.obj (op U)}
    (h : ∀ i, (Pi.π (fun _ : I => M) i).val.app (op U) x =
      (Pi.π (fun _ : I => M) i).val.app (op U) y) : x=y := by
  apply (sectionsEquiv M I U).injective
  funext i
  simpa only [sectionsEquiv_apply] using h i

/-- A section of the genuine product is zero exactly when all components are. -/
theorem section_eq_zero_iff (M : X.Modules) (I : Type u) (U : X.Opens)
    (x : (power M I).val.obj (op U)) :
    x=0 ↔ ∀ i, (Pi.π (fun _ : I => M) i).val.app (op U) x=0 := by
  constructor
  · intro h i
    rw [h,map_zero]
  · intro h
    apply sections_ext M I U
    intro i
    rw [map_zero]
    exact h i

end PaperVerification.SheafModulePowers
end
end
end ComponentSource_8

run_cmd Lean.logInfo "COMPONENT_SOURCE_END: PaperVerification.SheafModulePowers"

section ComponentSource_9
/- Original module: PaperVerification.SheafCoordinateMorphisms -/


/-!
# Morphisms specified by finite families of actual sheaf sections

The formulas use the genuine structure module, product projections and
the canonical structure-module/sections equivalence.
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits Opposite
open scoped BigOperators

namespace PaperVerification.SheafCoordinateMorphisms

universe u

/-- A linear frame carries the coordinate sum to the same linear combination
of the corresponding frame sections. -/
theorem sum_smul_eq_frame {R M I : Type*} [CommRing R] [AddCommGroup M]
    [Module R M] [Fintype I] (e : R ≃ₗ[R] M)
    (v a : I → R) (s : I → M) (h : ∀ i, e (a i) = s i) :
    (∑ i, v i • s i) = e (∑ i, v i * a i) := by
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro i hi
  simpa only [smul_eq_mul] using
    (congrArg (fun z : M => v i • z) (h i).symm).trans
      (e.map_smul (v i) (a i)).symm

variable {X : AlgebraicGeometry.Scheme.{u}} (M : X.Modules)

theorem unit_morphism_apply (s : M.sections) (U : X.Opens)
    (a : X.ringCatSheaf.obj.obj (op U)) :
    ((SheafOfModules.unitHomEquiv M).symm s).val.app (op U) a =
      a • s.eval (op U) := by
  let f := (SheafOfModules.unitHomEquiv M).symm s
  have h : f.val.app (op U) (1 : X.ringCatSheaf.obj.obj (op U)) = s.eval (op U) := by
    have hh := congrArg (fun z : M.sections => z.eval (op U))
      ((SheafOfModules.unitHomEquiv M).apply_symm_apply s)
    exact hh
  have hh := (f.val.app (op U)).hom.map_smul a
    (1 : X.ringCatSheaf.obj.obj (op U))
  simpa only [f, smul_eq_mul, mul_one, h] using hh

/-- The finite structure-module power maps to `M` by the chosen sections. -/
def fromSections {I : Type u} [Fintype I] (s : I → M.sections) :
    SheafModulePowers.structurePower X I ⟶ M :=
  ∑ i, Pi.π (fun _ : I => SheafOfModules.unit X.ringCatSheaf) i ≫
    (SheafOfModules.unitHomEquiv M).symm (s i)

/-- Its map on sections is the literal finite linear combination. -/
theorem fromSections_apply {I : Type u} [Fintype I] (s : I → M.sections)
    (U : X.Opens) (x : (SheafModulePowers.structurePower X I).val.obj (op U)) :
    (fromSections M s).val.app (op U) x =
      ∑ i, (show X.ringCatSheaf.obj.obj (op U) from
        SheafModulePowers.sectionsEquiv
          (SheafOfModules.unit X.ringCatSheaf) I U x i) • (s i).eval (op U) := by
  classical
  have h (T : Finset I) :
      (∑ i ∈ T, Pi.π (fun _ : I => SheafOfModules.unit X.ringCatSheaf) i ≫
        (SheafOfModules.unitHomEquiv M).symm (s i)).val.app (op U) x =
      ∑ i ∈ T, (show X.ringCatSheaf.obj.obj (op U) from
        SheafModulePowers.sectionsEquiv
          (SheafOfModules.unit X.ringCatSheaf) I U x i) • (s i).eval (op U) := by
    induction T using Finset.induction_on with
    | empty => rfl
    | @insert i T hi ih =>
      rw [Finset.sum_insert hi, Finset.sum_insert hi]
      change ((SheafOfModules.unitHomEquiv M).symm (s i)).val.app (op U)
          ((Pi.π (fun _ : I => SheafOfModules.unit X.ringCatSheaf) i).val.app
            (op U) x) + _ = _ + _
      apply congrArg₂ (fun a b : M.val.obj (op U) => a + b)
      · rw [unit_morphism_apply, SheafModulePowers.sectionsEquiv_apply]
      · exact ih
  exact h Finset.univ

end PaperVerification.SheafCoordinateMorphisms
end
end
end ComponentSource_9

run_cmd Lean.logInfo "COMPONENT_SOURCE_END: PaperVerification.SheafCoordinateMorphisms"

section ComponentSource_10
/- Original module: PaperVerification.SheafModuleKernels -/


/-!
# Sections of the actual kernel sheaf

Evaluation preserves limits of module sheaves. This gives the concrete kernel
of the map on sections, and the comparison commutes with the inclusion.
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CategoryTheory.Limits Opposite

namespace PaperVerification.SheafModuleKernels

universe u
variable {X : AlgebraicGeometry.Scheme.{u}} {M N : X.Modules}

local instance (U : X.Opens) :
    (SheafOfModules.evaluation X.ringCatSheaf (op U)).Additive := by
  dsimp [SheafOfModules.evaluation]
  infer_instance

/-- Evaluation of the categorical kernel is the ordinary kernel module. -/
def sectionsIso (f : M ⟶ N) (U : X.Opens) :
    (SheafOfModules.evaluation X.ringCatSheaf (op U)).obj (kernel f) ≅
      ModuleCat.of (X.ringCatSheaf.obj.obj (op U))
        ((SheafOfModules.evaluation X.ringCatSheaf (op U)).map f).hom.ker :=
  PreservesKernel.iso (SheafOfModules.evaluation X.ringCatSheaf (op U)) f ≪≫
    ModuleCat.kernelIsoKer ((SheafOfModules.evaluation X.ringCatSheaf (op U)).map f)

/-- The canonical section comparison as a linear equivalence. -/
def sectionsEquiv (f : M ⟶ N) (U : X.Opens) :
    (kernel f).val.obj (op U) ≃ₗ[X.ringCatSheaf.obj.obj (op U)]
      ((SheafOfModules.evaluation X.ringCatSheaf (op U)).map f).hom.ker :=
  (sectionsIso f U).toLinearEquiv

/-- The comparison identifies the actual sheaf inclusion with subtype inclusion. -/
@[simp] theorem sectionsEquiv_coe (f : M ⟶ N) (U : X.Opens)
    (x : (kernel f).val.obj (op U)) :
    (sectionsEquiv f U x).val = (kernel.ι f).val.app (op U) x := by
  have h : (sectionsIso f U).hom ≫ ModuleCat.ofHom
      (((SheafOfModules.evaluation X.ringCatSheaf (op U)).map f).hom.ker.subtype) =
        (SheafOfModules.evaluation X.ringCatSheaf (op U)).map (kernel.ι f) := by
    simp only [sectionsIso, Iso.trans_hom, Category.assoc,
      ModuleCat.kernelIsoKer_hom_ker_subtype, PreservesKernel.iso_hom,
      kernelComparison_comp_ι]
  exact congrArg (fun g => g x) h

end PaperVerification.SheafModuleKernels
end
end
end ComponentSource_10

run_cmd Lean.logInfo "COMPONENT_SOURCE_END: PaperVerification.SheafModuleKernels"

section ComponentSource_11
/- Original module: TauCeti.AlgebraicGeometry.ProjectiveSpectrum.TwistingSheaf.LocalTriviality -/
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/


/-!
# The original local trivializations of Proj twisting sheaves

This component retains the exact chart-generator, section-coordinate and
chart-isomorphism bodies from TauCeti's LocalTriviality module. It omits only
the later global-invertibility corollaries for symmetric algebras, which are
not used by the actual tautological determinant comparison. In particular,
the twisting sheaf remains the original homogeneous-fraction construction.
The retained construction works for every integer twist and arbitrary
commutative coefficient rings, including rings with nilpotents.
-/

public section

noncomputable section

open CategoryTheory TopologicalSpace

namespace AlgebraicGeometry.Proj

universe u

variable {A : Type u} {σ : Type*} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
variable {𝒜 : ℕ → σ} [GradedRing 𝒜]

namespace twistingSheaf

variable (n : ℤ) (f : A) (hf : f ∈ 𝒜 1) (U : (Proj 𝒜).Opens)
  (hU : U ≤ basicOpen 𝒜 f)

/-- The standard basis section `fⁿ` of `𝒪(n)` on an open contained in `D₊(f)`, for
a homogeneous element `f` of degree one. -/
def chartGenerator : Γ(twistingSheaf 𝒜 n, U) :=
  const (i := (-n).toNat) (j := n.toNat) (by omega)
    (f ^ n.toNat) (f ^ (-n).toNat)
    (by simpa using SetLike.pow_mem_graded n.toNat hf)
    (by simpa using SetLike.pow_mem_graded (-n).toNat hf) U
    (fun x hx ↦ fun h ↦ hU hx (x.isPrime.mem_of_pow_mem _ h))

/-- The standard basis section is the fraction `f ^ n.toNat / f ^ (-n).toNat`. -/
@[simp]
theorem chartGenerator_apply (x : U) :
    (chartGenerator n f hf U hU).1 x =
      Localization.mk (f ^ n.toNat)
        ⟨f ^ (-n).toNat, fun h ↦ hU x.2 (x.1.isPrime.mem_of_pow_mem _ h)⟩ :=
  (rfl)

/-- The standard basis sections commute with restriction. -/
@[simp]
theorem res_chartGenerator {V : (Proj 𝒜).Opens} (i : V ⟶ U) :
    (twistingSheaf 𝒜 n).presheaf.map i.op (chartGenerator n f hf U hU) =
      chartGenerator n f hf V (i.le.trans hU) :=
  (rfl)

/-- Multiplication of standard basis sections adds their degrees. -/
@[simp↓]
theorem mul_chartGenerator_apply (m : ℤ) (x : U) :
    (mul 𝒜 U m n (chartGenerator m f hf U hU) (chartGenerator n f hf U hU)).1 x =
      (chartGenerator (m + n) f hf U hU).1 x := by
  let := x.1.isPrime
  simp only [mul_apply, chartGenerator_apply, Localization.mk_mul]
  apply Localization.mk_eq_mk_iff.mpr
  apply Localization.r_of_eq
  -- Here `change` reduces the denominator subtype projections and `Submonoid.mul`,
  -- exposing the cross-multiplied equality in `A` for the exponent calculation.
  change f ^ (-(m + n)).toNat * (f ^ m.toNat * f ^ n.toNat) =
    (f ^ (-m).toNat * f ^ (-n).toNat) * f ^ (m + n).toNat
  simp only [← pow_add]
  congr 1
  omega

/-- The product of the standard basis sections of `𝒪(m)` and `𝒪(n)` is the standard basis
section of `𝒪(m + n)`. -/
@[simp]
theorem mul_chartGenerator (m : ℤ) :
    mul 𝒜 U m n (chartGenerator m f hf U hU) (chartGenerator n f hf U hU) =
      chartGenerator (m + n) f hf U hU :=
  ext fun x ↦ mul_chartGenerator_apply n f hf U hU m x

/-- The standard basis sections in opposite degrees multiply to one in each localization. -/
theorem chartGenerator_apply_mul_chartGenerator_neg_apply (x : U) :
    (chartGenerator n f hf U hU).1 x * (chartGenerator (-n) f hf U hU).1 x = 1 := by
  let := x.1.isPrime
  simp only [chartGenerator_apply, neg_neg]
  rw [Localization.mk_mul, mul_comm (f ^ n.toNat)]
  exact Localization.mk_self
    (⟨f ^ (-n).toNat, fun h ↦ hU x.2 (x.1.isPrime.mem_of_pow_mem _ h)⟩ *
      ⟨f ^ n.toNat, fun h ↦ hU x.2 (x.1.isPrime.mem_of_pow_mem _ h)⟩ :
        x.1.asHomogeneousIdeal.toIdeal.primeCompl)

end twistingSheaf

namespace twistingSheaf

open ProjectiveSpectrum.TwistingSheaf

variable (n : ℤ) (f : A) (hf : f ∈ 𝒜 1) (U : (Proj 𝒜).Opens)
  (hU : U ≤ basicOpen 𝒜 f)

private def chartInverse (s : Γ(twistingSheaf 𝒜 n, U)) : Γ(twistingSheaf 𝒜 0, U) :=
  ⟨s.1 * (chartGenerator (-n) f hf U hU).1, by
    apply (mem_sectionsAddSubgroup_iff _).mpr
    simpa only [add_neg_cancel] using
      isLocallyFraction_mul s.2 (chartGenerator (-n) f hf U hU).2⟩

private theorem chartInverse_apply (s : Γ(twistingSheaf 𝒜 n, U)) (x : U) :
    (chartInverse n f hf U hU s).1 x =
      s.1 x * (chartGenerator (-n) f hf U hU).1 x :=
  (rfl)

/-- Multiplication by `fⁿ` trivializes the sections of `𝒪(n)` on every open contained in
the degree-one chart `D₊(f)`. -/
def chartSectionsLinearEquiv :
    Γ(Proj 𝒜, U) ≃ₗ[Γ(Proj 𝒜, U)] Γ(twistingSheaf 𝒜 n, U) where
  toFun a := a • chartGenerator n f hf U hU
  map_add' a b := add_smul a b _
  map_smul' a b := mul_smul a b _
  invFun s := (sectionsLinearEquivTwistingSheafZero 𝒜 U).symm (chartInverse n f hf U hU s)
  left_inv a := Subtype.ext <| funext fun x ↦ HomogeneousLocalization.val_injective _ <| by
    simp only [sectionsLinearEquivTwistingSheafZero_symm_apply_val U _ x,
      chartInverse_apply n f hf U hU _ x, smul_apply a _ x,
      mul_assoc, chartGenerator_apply_mul_chartGenerator_neg_apply n f hf U hU x, mul_one]
  right_inv s := ext fun x ↦ by
    simp only [smul_apply _ _ x, sectionsLinearEquivTwistingSheafZero_symm_apply_val U _ x,
      chartInverse_apply n f hf U hU s x, mul_assoc,
      mul_comm ((chartGenerator (-n) f hf U hU).1 x),
      chartGenerator_apply_mul_chartGenerator_neg_apply n f hf U hU x, mul_one]

/-- In standard chart coordinates the forward map multiplies by the basis section. -/
theorem chartSectionsLinearEquiv_apply (a : Γ(Proj 𝒜, U)) :
    chartSectionsLinearEquiv n f hf U hU a = a • chartGenerator n f hf U hU :=
  (rfl)

/-- The forward chart coordinate map is multiplication by `fⁿ` in each localization. -/
@[simp]
theorem chartSectionsLinearEquiv_apply_apply (a : Γ(Proj 𝒜, U)) (x : U) :
    (chartSectionsLinearEquiv n f hf U hU a).1 x =
      (a.1 x).val * (chartGenerator n f hf U hU).1 x :=
  (rfl)

/-- The inverse chart coordinate is multiplication by `f⁻ⁿ` in the localizations. -/
@[simp]
theorem chartSectionsLinearEquiv_symm_apply_val (s : Γ(twistingSheaf 𝒜 n, U)) (x : U) :
    (((chartSectionsLinearEquiv n f hf U hU).symm s).1 x).val =
      s.1 x * (chartGenerator (-n) f hf U hU).1 x :=
  sectionsLinearEquivTwistingSheafZero_symm_apply_val _ _ _

/-- The chart coordinate isomorphisms commute with restriction to smaller opens. -/
theorem res_chartSectionsLinearEquiv {V : (Proj 𝒜).Opens} (i : V ⟶ U)
    (a : Γ(Proj 𝒜, U)) :
    (twistingSheaf 𝒜 n).presheaf.map i.op (chartSectionsLinearEquiv n f hf U hU a) =
      chartSectionsLinearEquiv n f hf V (i.le.trans hU) ((Proj 𝒜).presheaf.map i.op a) :=
  (rfl)

/-- The twisting sheaf `𝒪(n)` is trivial on the standard open of a degree-one element,
for every integer `n`. -/
def chartIso :
    SheafOfModules.unit ((Proj 𝒜).ringCatSheaf.over (basicOpen 𝒜 f)) ≅
      (twistingSheaf 𝒜 n).over (basicOpen 𝒜 f) :=
  (SheafOfModules.fullyFaithfulForget _).preimageIso <| PresheafOfModules.isoMk
    (fun V ↦ (chartSectionsLinearEquiv n f hf V.unop.left V.unop.hom.le).toModuleIso)
    (fun _ _ _ ↦ rfl)

/-- On each smaller open the standard sheaf trivialization is multiplication by `fⁿ`. -/
theorem chartIso_hom_app_apply
    (V : Over (basicOpen 𝒜 f)) (a : Γ(Proj 𝒜, V.left)) :
    (chartIso n f hf).hom.val.app (Opposite.op V) a =
      chartSectionsLinearEquiv n f hf V.left V.hom.le a :=
  (rfl)

/-- The inverse standard sheaf trivialization gives the chart coordinate of a section. -/
theorem chartIso_inv_app_apply
    (V : Over (basicOpen 𝒜 f)) (s : Γ(twistingSheaf 𝒜 n, V.left)) :
    (chartIso n f hf).inv.val.app (Opposite.op V) s =
      (chartSectionsLinearEquiv n f hf V.left V.hom.le).symm s :=
  (rfl)

/-- The standard sheaf trivialization multiplies values by `fⁿ`. -/
@[simp]
theorem chartIso_hom_app_apply_apply
    (V : Over (basicOpen 𝒜 f)) (a : Γ(Proj 𝒜, V.left)) (x : V.left) :
    ((chartIso n f hf).hom.val.app (Opposite.op V) a).1 x =
      (a.1 x).val * (chartGenerator n f hf V.left V.hom.le).1 x :=
  (rfl)

/-- The inverse standard sheaf trivialization multiplies values by `f⁻ⁿ`. -/
@[simp]
theorem chartIso_inv_app_apply_val
    (V : Over (basicOpen 𝒜 f)) (s : Γ(twistingSheaf 𝒜 n, V.left)) (x : V.left) :
    (((chartIso n f hf).inv.val.app (Opposite.op V) s).1 x).val =
      s.1 x * (chartGenerator (-n) f hf V.left V.hom.le).1 x :=
  chartSectionsLinearEquiv_symm_apply_val n f hf V.left V.hom.le s x

end twistingSheaf

end AlgebraicGeometry.Proj

end
end
end ComponentSource_11

run_cmd Lean.logInfo "COMPONENT_SOURCE_END: TauCeti.AlgebraicGeometry.ProjectiveSpectrum.TwistingSheaf.LocalTriviality"

section ComponentSource_12
/- Original module: PaperVerification.TwistingChartFractions -/


/-!
# Homogeneous fractions and the actual twisting-sheaf frame

On the standard open of a degree-one element `f`, the section `r/f` of the
structure sheaf becomes the homogeneous section `r` of `𝒪(1)` under the
canonical frame. This comparison is between the existing sheaf constructions.
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
open AlgebraicGeometry CategoryTheory

namespace PaperVerification.TwistingChartFractions

variable {A : Type*} {σ : Type*} [CommRing A] [SetLike σ A]
  [AddSubgroupClass σ A] {𝒜 : ℕ → σ} [GradedRing 𝒜]

/-- Dividing by the pivot and then applying the genuine `𝒪(1)` chart frame
recovers the original homogeneous section. -/
theorem chart_frame_fraction {f : A} (hf : f ∈ 𝒜 1) (r : 𝒜 1) :
    Proj.twistingSheaf.chartSectionsLinearEquiv (𝒜:=𝒜) 1 f hf
      (Proj.basicOpen 𝒜 f) le_rfl
      (Proj.awayToSection 𝒜 f
        (HomogeneousLocalization.Away.mk 𝒜 hf 1 r (by simpa using r.property))) =
      Proj.toTwistingSheaf 𝒜 rfl (Proj.basicOpen 𝒜 f) r := by
  apply Proj.twistingSheaf.ext
  intro x
  rw [Proj.twistingSheaf.chartSectionsLinearEquiv_apply_apply,
    Proj.val_awayToSection_mk_apply,
    Proj.twistingSheaf.chartGenerator_apply,
    Proj.toTwistingSheaf_apply_apply]
  rw [Localization.mk_mul]
  apply Localization.mk_eq_mk_iff.mpr
  apply Localization.r_of_eq
  simp [mul_comm]

end PaperVerification.TwistingChartFractions
end
end
end ComponentSource_12

run_cmd Lean.logInfo "COMPONENT_SOURCE_END: PaperVerification.TwistingChartFractions"


set_option pp.explicit false
set_option pp.proofs false
set_option pp.deepTerms false
set_option maxHeartbeats 0

open Lean Elab Command in
run_cmd do
  let env := (← getEnv).setExporting false
  let opts ← getOptions
  if true && env.header.trustLevel != 0 then
    throwError "The final environment has nonzero kernel trust level"
  if Lean.debug.skipKernelTC.get opts then
    throwError "The final environment disabled kernel type checking"
  if Lean.Elab.inServer.get opts then
    throwError "The final environment unexpectedly uses server mode"
  let required : Array (Name × String) := #[
    (`PaperVerification.AlternatingSectionSheaf.functional, "definition"),
    (`PaperVerification.AlternatingSectionSheaf.functional_app_sheafified_wedge, "theorem"),
    (`PaperVerification.AlternatingSectionSheaf.functional_eq_zero, "theorem"),
    (`PaperVerification.NormalizedTautologicalKernel.incidenceKernelEquiv, "definition"),
    (`PaperVerification.NormalizedTautologicalKernel.kernel_pivot_bijective, "theorem"),
    (`PaperVerification.SheafModulePowers.reindex_projection, "theorem"),
    (`PaperVerification.SheafModulePowers.sectionsEquiv, "definition"),
    (`PaperVerification.SheafModuleKernels.sectionsEquiv, "definition"),
    (`PaperVerification.SheafCoordinateMorphisms.fromSections_apply, "theorem"),
    (`PaperVerification.TwistingChartFractions.chart_frame_fraction, "theorem"),
    (`AlgebraicGeometry.Proj.twistingSheaf.chartGenerator, "definition"),
    (`AlgebraicGeometry.Proj.twistingSheaf.chartSectionsLinearEquiv, "definition"),
    (`AlgebraicGeometry.Proj.twistingSheaf.chartIso, "definition")
  ]
  let localNames := env.checked.get.constants.foldStage2 (fun acc name _ => acc.push name) (#[] : Array Name)
  if localNames.isEmpty then throwError "Empty authored declaration audit"
  let mut names := localNames
  for (name, _) in required do
    unless names.contains name do names := names.push name
  let mut rows : Array Json := #[]
  for name in names do
    let some info := env.checked.get.find? name | throwError "Missing checked declaration {name}"
    let kind := match info with
      | .thmInfo _ => "theorem"
      | .defnInfo _ => "definition"
      | .opaqueInfo _ => "opaque"
      | .axiomInfo _ => "axiom"
      | .inductInfo _ => "inductive"
      | .ctorInfo _ => "constructor"
      | .recInfo _ => "recursor"
      | .quotInfo _ => "quotient primitive"
    if kind == "axiom" then throwError "Authored axiom {name}"
    let value := info.value? (allowOpaque := true)
    if kind == "theorem" || kind == "definition" || kind == "opaque" then
      unless value.isSome do throwError "No actual body {name}"
    for (requiredName, expectedKind) in required do
      if name == requiredName && kind != expectedKind then
        throwError "Endpoint kind mismatch {name}: expected {expectedKind}, got {kind}"
    let axioms ← collectAxioms name
    for ax in axioms do
      if ax != ``propext && ax != ``Classical.choice && ax != ``Quot.sound then
        throwError "Unapproved transitive axiom {name}: {ax}"
    let mut fields := [("name", toJson name.toString), ("kind", toJson kind),
      ("actual_body_available", toJson value.isSome),
      ("universe_parameters", toJson (info.levelParams.map Name.toString)),
      ("type_dependencies", toJson (info.type.getUsedConstants.map Name.toString)),
      ("body_dependencies", toJson ((value.map Expr.getUsedConstants).getD #[] |>.map Name.toString)),
      ("transitive_axioms", toJson (axioms.map Name.toString))]
    if required.any (fun e => e.1 == name) then
      let typeText ← liftTermElabM <| return (← Meta.ppExpr info.type).pretty
      fields := fields ++ [("readable_type", toJson typeText)]
    rows := rows.push (Json.mkObj fields)
  IO.FS.createDirAll ".lake/reports"
  let path := ".lake/reports/" ++ (← getEnv).mainModule.toString ++ ".json"
  IO.FS.writeFile path (Json.mkObj [("accepted", toJson true),
    ("nonce", toJson "b57bd476fe07dda04df3e520c81c478c"), ("declaration_count", toJson localNames.size),
    ("kernel_trust_level", toJson env.header.trustLevel.toNat),
    ("kernel_type_checking_enabled", toJson (!Lean.debug.skipKernelTC.get opts)),
    ("server_mode", toJson (Lean.Elab.inServer.get opts)),
    ("required_endpoint_count", toJson required.size),
    ("all_new_declarations_read_from_checked_environment", toJson true),
    ("declarations", toJson rows)]).pretty
  logInfo "LITERAL_COMPONENT_KERNEL_AUDIT_COMPLETE:b57bd476fe07dda04df3e520c81c478c"
