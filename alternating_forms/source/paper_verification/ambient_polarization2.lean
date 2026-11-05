module

public import paper_verification.ambient_zero6
import all paper_verification.ambient_zero6
public import paper_verification.literal005
import all paper_verification.literal005
public import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Functor
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
public import Mathlib.CategoryTheory.Sites.LocalProperties
public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.Algebra.Category.ModuleCat.EpiMono
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackFree
public import paper_verification.ambient_generic1
import all paper_verification.ambient_generic1
public import paper_verification.ambient_intrinsic5
import all paper_verification.ambient_intrinsic5
import Lean.Util.CollectAxioms
import Lean.Util.FoldConsts
import Lean.PrettyPrinter

set_option Elab.async false

section ComponentSource_0
/- Original module: PaperVerification.TwistingSheafMap -/


/-!
# Functorial homogeneous fractions in the actual twisting sheaves

A degree-preserving ring map sends a local fraction `a / b` to `f a / f b`.
This gives the canonical morphism from the twisting sheaf on the target
of `Proj.map` to the pushforward of the twisting sheaf on its source.
Its adjoint is the actual pullback morphism of sheaves of modules.

The construction uses the existing local-fraction definition of `𝒪(n)`;
it introduces neither a substitute sheaf nor any cohomological assumption.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

namespace PaperVerification.TwistingSheafMap

open AlgebraicGeometry CategoryTheory TopologicalSpace
open AlgebraicGeometry.ProjectiveSpectrum.TwistingSheaf

universe u

variable {A B σ τ : Type u} [CommRing A] [CommRing B]
  [SetLike σ A] [AddSubgroupClass σ A]
  [SetLike τ B] [AddSubgroupClass τ B]
  {𝒜 : ℕ → σ} {ℬ : ℕ → τ} [GradedRing 𝒜] [GradedRing ℬ]
  (f : 𝒜 →+*ᵍ ℬ)
  (hf : HomogeneousIdeal.irrelevant ℬ ≤ (HomogeneousIdeal.irrelevant 𝒜).map f)

/-- The map on the ambient localizations, evaluated on a section. -/
def fractionMap (U : (Proj 𝒜).Opens) (V : (Proj ℬ).Opens)
    (hUV : V ≤ (Proj.map f hf) ⁻¹ᵁ U)
    (s : ∀ x : U, Localizations 𝒜 x.val) (y : V) : Localizations ℬ y.val := by
  letI := y.val.isPrime
  letI := (ProjectiveSpectrum.comap f hf y.val).isPrime
  exact Localization.localRingHom
    (ProjectiveSpectrum.comap f hf y.val).asHomogeneousIdeal.toIdeal
    y.val.asHomogeneousIdeal.toIdeal f.toRingHom rfl
      (s ⟨ProjectiveSpectrum.comap f hf y.val, hUV y.property⟩)

set_option backward.isDefEq.respectTransparency false in
/-- Being locally a fraction of degree `n` is preserved by the actual map. -/
theorem fractionMap_isLocallyFraction (n : ℤ)
    (U : (Proj 𝒜).Opens) (V : (Proj ℬ).Opens)
    (hUV : V ≤ (Proj.map f hf) ⁻¹ᵁ U)
    (s : ∀ x : U, Localizations 𝒜 x.val)
    (hs : (isLocallyFraction 𝒜 n).pred s) :
    (isLocallyFraction ℬ n).pred (fractionMap f hf U V hUV s) := by
  rintro ⟨p, hpV⟩
  obtain ⟨W, m, iWU, i, j, hij, a, b, hb, hfrac⟩ :=
    hs ⟨ProjectiveSpectrum.comap f hf p, hUV hpV⟩
  refine ⟨W.comap (ProjectiveSpectrum.comap f hf) ⊓ V, ⟨m, hpV⟩,
    Opens.infLERight _ _, i, j, hij, f.gradedAddHom j a, f.gradedAddHom i b,
    fun ⟨q, hqW, hqV⟩ => hb ⟨_, hqW⟩, fun ⟨q, hqW, hqV⟩ => ?_⟩
  letI := q.isPrime
  have h := hfrac ⟨_, hqW⟩
  exact (congrArg (Localization.localRingHom
    (ProjectiveSpectrum.comap f hf q).asHomogeneousIdeal.toIdeal
    q.asHomogeneousIdeal.toIdeal f.toRingHom rfl) h).trans (by simp)

/-- Pull a genuine local-fraction section back along `Proj.map`. -/
def sectionsMap (n : ℤ) (U : (Proj 𝒜).Opens) :
    Γ(Proj.twistingSheaf 𝒜 n, U) →
      Γ(Proj.twistingSheaf ℬ n, (Proj.map f hf) ⁻¹ᵁ U) :=
  fun s => ⟨fractionMap f hf U _ le_rfl s.val,
    fractionMap_isLocallyFraction f hf n U _ le_rfl s.val s.property⟩

@[simp] theorem sectionsMap_add (n : ℤ) (U : (Proj 𝒜).Opens)
    (s t : Γ(Proj.twistingSheaf 𝒜 n, U)) :
    sectionsMap f hf n U (s + t) = sectionsMap f hf n U s + sectionsMap f hf n U t := by
  apply Proj.twistingSheaf.ext
  intro x
  exact map_add _ _ _

set_option backward.isDefEq.respectTransparency false in
/-- The section map is linear with the actual structure-sheaf pullback. -/
theorem sectionsMap_smul (n : ℤ) (U : (Proj 𝒜).Opens)
    (a : Γ(Proj 𝒜, U)) (s : Γ(Proj.twistingSheaf 𝒜 n, U)) :
    sectionsMap f hf n U (a • s) =
      (Proj.map f hf).app U a • sectionsMap f hf n U s := by
  apply Proj.twistingSheaf.ext
  intro x
  change Localization.localRingHom _ _ f.toRingHom rfl
    (((a.val ⟨_, x.property⟩).val) * s.val ⟨_, x.property⟩) =
    (HomogeneousLocalization.localRingHom f _ _ rfl
      (a.val ⟨_, x.property⟩)).val *
        Localization.localRingHom _ _ f.toRingHom rfl (s.val ⟨_, x.property⟩)
  rw [map_mul, HomogeneousLocalization.val_localRingHom]
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- The canonical morphism of actual sheaves of modules, before adjunction. -/
def pushforwardHom (n : ℤ) :
    Proj.twistingSheaf 𝒜 n ⟶
      (Scheme.Modules.pushforward (Proj.map f hf)).obj (Proj.twistingSheaf ℬ n) where
  val :=
    { app := fun U => by
        let M := (Proj.twistingSheaf 𝒜 n).val.obj U
        let N := ((Scheme.Modules.pushforward (Proj.map f hf)).obj
          (Proj.twistingSheaf ℬ n)).val.obj U
        exact ModuleCat.ofHom (X := M) (Y := N)
          { toFun := sectionsMap f hf n U.unop
            map_add' := sectionsMap_add f hf n U.unop
            map_smul' := fun a s => sectionsMap_smul f hf n U.unop a s }
      naturality := by
        intro U V i
        ext s x
        rfl }

/-- The canonical pullback map `Proj(f)^* 𝒪(n) → 𝒪(n)`. -/
def pullbackHom (n : ℤ) :
    (Scheme.Modules.pullback (Proj.map f hf)).obj (Proj.twistingSheaf 𝒜 n) ⟶
      Proj.twistingSheaf ℬ n :=
  ((Scheme.Modules.pullbackPushforwardAdjunction (Proj.map f hf)).homEquiv _ _).symm
    (pushforwardHom f hf n)

end PaperVerification.TwistingSheafMap
end
end
end ComponentSource_0

run_cmd Lean.logInfo "COMPONENT_SOURCE_END: PaperVerification.TwistingSheafMap"

section ComponentSource_1
/- Original module: TauCeti.Algebra.Category.ModuleCat.Sheaf.LocalIsomorphism -/
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/


/-!
# Isomorphisms of sheaves of modules are local

A morphism of sheaves of modules is an isomorphism if it is one after restriction to every
member of a cover of the terminal object. This lets one check an isomorphism involving a line
bundle, such as its tensor evaluation map, on a cover of free rank-one trivializations.

This is the module-sheaf counterpart of Mathlib's local isomorphism criterion for sheaves.
-/

public section

open CategoryTheory

namespace TauCeti

universe u v w x

namespace SheafOfModules

variable {C : Type u} [Category.{w} C] {J : GrothendieckTopology C}
  {R : Sheaf J RingCat.{v}} {M N : _root_.SheafOfModules.{v} R}
  {ι : Type x} {X : ι → C}

/-- A morphism of sheaves of modules that is an isomorphism on every member of a covering
family is an isomorphism globally. -/
theorem _root_.SheafOfModules.isIso_of_coversTop (hX : J.CoversTop X) (f : M ⟶ N)
    (hf : ∀ i, IsIso (f.over (X i))) : IsIso f := by
  have h : IsIso ((_root_.SheafOfModules.toSheaf R).map f) := by
    apply Sheaf.isIso_of_coversTop hX
    intro i
    -- Pullback of the underlying sheaf is definitionally the underlying sheaf of the
    -- restricted module; the two expressions carry different categorical wrappers.
    change IsIso ((_root_.SheafOfModules.toSheaf (R.over (X i))).map (f.over (X i)))
    let h := hf i
    infer_instance
  exact (isIso_iff_of_reflects_iso f (_root_.SheafOfModules.toSheaf R)).mp h

/-- A morphism of sheaves of modules is an isomorphism exactly when its restrictions to a
cover are isomorphisms. -/
theorem _root_.SheafOfModules.isIso_iff_of_coversTop (hX : J.CoversTop X) (f : M ⟶ N) :
    IsIso f ↔ ∀ i, IsIso (f.over (X i)) :=
  ⟨fun _ _ => inferInstance, _root_.SheafOfModules.isIso_of_coversTop hX f⟩

end SheafOfModules

end TauCeti
end
end ComponentSource_1

run_cmd Lean.logInfo "COMPONENT_SOURCE_END: TauCeti.Algebra.Category.ModuleCat.Sheaf.LocalIsomorphism"

section ComponentSource_2
/- Original module: PaperVerification.LineSheafSurjective -/


/-!
# Surjectivity between actual trivial line sheaves

A surjective endomorphism of a commutative ring as a module is
multiplication by a unit. Consequently a sectionwise surjective morphism
between two actual sheaves trivialized by the structure sheaf is an
isomorphism. The argument is local and works over rings with zero divisors.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace PaperVerification.LineSheafSurjective

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u v w

local instance {X : Scheme.{u}} (U : X.Opens) (V : (Over U)ᵒᵖ) :
    CommRing ((X.ringCatSheaf.over U).obj.obj V) :=
  inferInstanceAs (CommRing Γ(X, V.unop.left))

local instance {X : Scheme.{u}} (U : X.Opens) (V : (Over U)ᵒᵖ) :
    CommRing ((SheafOfModules.unit (X.ringCatSheaf.over U)).val.obj V) :=
  inferInstanceAs (CommRing Γ(X, V.unop.left))

/-- An endomorphism of a free rank-one module is invertible whenever it
is surjective. No domain or field hypothesis is used. -/
theorem rankOne_bijective_of_surjective {R : Type u} [CommRing R]
    (φ : R →ₗ[R] R) (hφ : Function.Surjective φ) : Function.Bijective φ := by
  have hm (r : R) : φ r = r * φ 1 := by
    simpa only [smul_eq_mul, mul_one] using φ.map_smul r 1
  obtain ⟨r, hr⟩ := hφ 1
  have hru : r * φ 1 = 1 := (hm r).symm.trans hr
  let a : Rˣ := ⟨φ 1, r, (mul_comm _ _).trans hru, hru⟩
  have he : (φ : R → R) = fun b => b * a.val := funext hm
  rw [he]
  exact IsUnit.isUnit_iff_mulRight_bijective.mp a.isUnit

/-- Componentwise bijectivity gives an actual sheaf isomorphism, with the
original morphism as its forward map. -/
theorem isIso_of_app_bijective {C : Type u} [Category.{v} C]
    {J : GrothendieckTopology C} {R : Sheaf J RingCat.{w}}
    {M N : SheafOfModules.{w} R} (φ : M ⟶ N)
    (hφ : ∀ V, Function.Bijective (φ.val.app V)) : IsIso φ := by
  let e : M.val ≅ N.val := PresheafOfModules.isoMk
    (fun V => (LinearEquiv.ofBijective (φ.val.app V).hom (hφ V)).toModuleIso)
    (fun {_ _} i => φ.val.naturality i)
  let e' : M ≅ N := (SheafOfModules.fullyFaithfulForget R).preimageIso e
  have he : e'.hom = φ := by
    apply SheafOfModules.hom_ext
    apply PresheafOfModules.hom_ext
    intro V
    rfl
  rw [← he]
  infer_instance

/-- Surjectivity on every subopen of one trivializing open makes the
original morphism invertible on that open. -/
theorem isIso_over_of_surjective {X : Scheme.{u}} {M N : X.Modules}
    (φ : M ⟶ N) (U : X.Opens)
    (e : M.over U ≅ SheafOfModules.unit (X.ringCatSheaf.over U))
    (f : N.over U ≅ SheafOfModules.unit (X.ringCatSheaf.over U))
    (hφ : ∀ V : Over U, Function.Surjective (φ.app V.left)) :
    IsIso (φ.over U) := by
  let θ := e.inv ≫ φ.over U ≫ f.hom
  have hθ : IsIso θ := by
    apply isIso_of_app_bijective
    intro V
    let E := (PresheafOfModules.evaluation _ V).mapIso
      ((SheafOfModules.forget _).mapIso e)
    let F := (PresheafOfModules.evaluation _ V).mapIso
      ((SheafOfModules.forget _).mapIso f)
    apply rankOne_bijective_of_surjective (θ.val.app V).hom
    exact F.toLinearEquiv.surjective.comp
      ((hφ V.unop).comp E.toLinearEquiv.symm.surjective)
  simpa only [θ, isIso_comp_left_iff, isIso_comp_right_iff] using hθ

/-- A preimage of `1` on the entire trivializing open restricts to a
preimage of `1` on every subopen. Linearity then gives surjectivity there. -/
theorem unitEnd_app_surjective {X : Scheme.{u}} (U : X.Opens)
    (θ : SheafOfModules.unit (X.ringCatSheaf.over U) ⟶
      SheafOfModules.unit (X.ringCatSheaf.over U))
    (hθ : Function.Surjective (θ.val.app (.op (Over.mk (𝟙 U)))))
    (V : Over U) : Function.Surjective (θ.val.app (.op V)) := by
  obtain ⟨r, hr⟩ := hθ 1
  let j : V ⟶ Over.mk (𝟙 U) := Over.homMk V.hom (by simp)
  let s : (SheafOfModules.unit (X.ringCatSheaf.over U)).val.obj (.op V) :=
    (SheafOfModules.unit (X.ringCatSheaf.over U)).val.map j.op r
  have hs : θ.val.app (.op V) s = 1 := by
    have h := PresheafOfModules.naturality_apply θ.val j.op r
    exact h.trans (by
      rw [hr]
      exact PresheafOfModules.unit_map_one _ j.op)
  intro t
  refine ⟨t • s, ?_⟩
  rw [map_smul, hs]
  exact mul_one t

/-- For two line sheaves trivialized on `U`, surjectivity on the single
open `U` already proves an isomorphism throughout that open. -/
theorem isIso_over_of_surjective_top {X : Scheme.{u}} {M N : X.Modules}
    (φ : M ⟶ N) (U : X.Opens)
    (e : M.over U ≅ SheafOfModules.unit (X.ringCatSheaf.over U))
    (f : N.over U ≅ SheafOfModules.unit (X.ringCatSheaf.over U))
    (hφ : Function.Surjective (φ.app U)) : IsIso (φ.over U) := by
  let θ := e.inv ≫ φ.over U ≫ f.hom
  have htop : Function.Surjective (θ.val.app (.op (Over.mk (𝟙 U)))) := by
    let E := (PresheafOfModules.evaluation _ (.op (Over.mk (𝟙 U)))).mapIso
      ((SheafOfModules.forget _).mapIso e)
    let F := (PresheafOfModules.evaluation _ (.op (Over.mk (𝟙 U)))).mapIso
      ((SheafOfModules.forget _).mapIso f)
    exact F.toLinearEquiv.surjective.comp
      (hφ.comp E.toLinearEquiv.symm.surjective)
  have hθ : IsIso θ := by
    apply isIso_of_app_bijective
    intro V
    exact rankOne_bijective_of_surjective (θ.val.app V).hom
      (unitEnd_app_surjective U θ htop V.unop)
  simpa only [θ, isIso_comp_left_iff, isIso_comp_right_iff] using hθ

end PaperVerification.LineSheafSurjective
end
end
end ComponentSource_2

run_cmd Lean.logInfo "COMPONENT_SOURCE_END: PaperVerification.LineSheafSurjective"

section ComponentSource_3
/- Original module: PaperVerification.ModulePullbackLocal -/
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

The unit, restriction, and section constructions below are the corresponding
constructions from TauCeti/AlgebraicGeometry/Modules/Pullback/{Basic,Sections}.
They are placed in a separate namespace and given only their direct Mathlib
imports, so this elementary local argument does not require the independent
tensor-product and quasicoherent-presentation theories. The underlying
pullback, adjunction, and restriction functors remain Mathlib's originals.
-/


/-!
# Local coordinates for the actual module pullback

These explicit comparison isomorphisms identify a pullback restricted to
an inverse-image open with the pullback of the restricted module. The
section map is the unit of the actual pullback–pushforward adjunction.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace PaperVerification.ModulePullbackLocal

open AlgebraicGeometry CategoryTheory TopologicalSpace
open AlgebraicGeometry.Scheme.Modules

universe u
variable {X Y : Scheme.{u}}

/-- Pullback preserves the actual structure sheaf. -/
def unitIso (f : X ⟶ Y) :
    (pullback f).obj (SheafOfModules.unit Y.ringCatSheaf) ≅
      SheafOfModules.unit X.ringCatSheaf :=
  letI : (SheafOfModules.pushforward.{u} f.toRingCatSheafHom).IsRightAdjoint :=
    inferInstanceAs (pushforward f).IsRightAdjoint
  have h : IsIso (SheafOfModules.pullbackObjUnitToUnit f.toRingCatSheafHom) :=
    SheafOfModules.instIsIsoPullbackObjUnitToUnitOfFinal _
  @asIso _ _ _ _ (SheafOfModules.pullbackObjUnitToUnit f.toRingCatSheafHom) h

/-- Restriction of pullback agrees with pullback along the restricted map. -/
def restrictObjIso (f : X ⟶ Y) (V : Y.Opens) (M : Y.Modules) :
    ((pullback f).obj M).restrict (f ⁻¹ᵁ V).ι ≅
      (pullback (f ∣_ V)).obj (M.restrict V.ι) :=
  (restrictFunctorIsoPullback (f ⁻¹ᵁ V).ι).app _ ≪≫
    (pullbackComp (f ⁻¹ᵁ V).ι f).app M ≪≫
    (pullbackCongr (morphismRestrict_ι f V).symm).app M ≪≫
    ((pullbackComp (f ∣_ V) V.ι).app M).symm ≪≫
    (pullback (f ∣_ V)).mapIso ((restrictFunctorIsoPullback V.ι).app M).symm

/-- The actual pullback read on the two open slice sites. -/
def overPullback (f : X ⟶ Y) (V : Y.Opens) :
    SheafOfModules (Y.ringCatSheaf.over V) ⥤
      SheafOfModules (X.ringCatSheaf.over (f ⁻¹ᵁ V)) :=
  (overEquiv V).functor ⋙ pullback (f ∣_ V) ⋙ (overEquiv (f ⁻¹ᵁ V)).inverse

/-- The slice-site pullback preserves the structure sheaf. -/
def overUnitIso (f : X ⟶ Y) (V : Y.Opens) :
    SheafOfModules.unit _ ≅ (overPullback f V).obj (SheafOfModules.unit _) :=
  (overEquiv (f ⁻¹ᵁ V)).unitIso.app _ ≪≫
    (overEquiv (f ⁻¹ᵁ V)).inverse.mapIso (unitIso (f ∣_ V)).symm

/-- The slice-site pullback is the restriction of the original pullback. -/
def overObjIso (f : X ⟶ Y) (V : Y.Opens) (M : Y.Modules) :
    (overPullback f V).obj (M.over V) ≅ ((pullback f).obj M).over (f ⁻¹ᵁ V) :=
  ((overEquiv (f ⁻¹ᵁ V)).inverse.mapIso
    ((overFunctorEquiv (f ⁻¹ᵁ V)).app _ ≪≫ restrictObjIso f V M ≪≫
      (pullback (f ∣_ V)).mapIso ((overFunctorEquiv V).app M).symm)).symm ≪≫
    ((overEquiv (f ⁻¹ᵁ V)).unitIso.app _).symm

/-- Pullback of sections is exactly the adjunction unit on that open. -/
def sections (f : X ⟶ Y) (M : Y.Modules) (U : Y.Opens) :
    Γ(M, U) →ₛₗ[(f.app U).hom] Γ((pullback f).obj M, f ⁻¹ᵁ U) where
  toFun := ((pullbackPushforwardAdjunction f).unit.app M).app U
  map_add' := map_add _
  map_smul' r s := ((pullbackPushforwardAdjunction f).unit.app M).app_smul r s

/-- Pullback of a section to any open contained in the inverse image. -/
def sectionsLE (f : X ⟶ Y) (M : Y.Modules) (U : Y.Opens)
    (V : X.Opens) (hV : V ≤ f ⁻¹ᵁ U) :
    Γ(M, U) →ₛₗ[(f.appLE U V hV).hom] Γ((pullback f).obj M, V) where
  toFun s := ((pullback f).obj M).presheaf.map (homOfLE hV).op (sections f M U s)
  map_add' := by simp
  map_smul' r s := by
    rw [map_smulₛₗ, map_smul]
    rfl

end PaperVerification.ModulePullbackLocal
end
end
end ComponentSource_3

run_cmd Lean.logInfo "COMPONENT_SOURCE_END: PaperVerification.ModulePullbackLocal"

section ComponentSource_4
/- Original module: PaperVerification.TwistingSheafPullback -/


/-!
# Pullback of actual twisting sheaves under generated graded maps

Suppose degree-one standard opens cover the source of a graded map. The
canonical map on the actual homogeneous-fraction sheaves induces an
isomorphism `Proj(f)^* O(n) ≅ O(n)` for every integer `n`.

On a standard open, the section `a^n` pulls back to `f(a)^n`. Every target
section is a regular multiple of that generator. Thus the pullback map
is surjective on a basis of opens, and a surjective morphism between
actual line bundles is invertible. In particular this applies to maps of
symmetric algebras induced by quotients or by coefficient localization;
no inverse graded map is required.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace PaperVerification.TwistingSheafMap

open AlgebraicGeometry CategoryTheory TopologicalSpace
open AlgebraicGeometry.ProjectiveSpectrum.TwistingSheaf

universe u

variable {A B σ τ : Type u} [CommRing A] [CommRing B]
  [SetLike σ A] [AddSubgroupClass σ A]
  [SetLike τ B] [AddSubgroupClass τ B]
  {𝒜 : ℕ → σ} {ℬ : ℕ → τ} [GradedRing 𝒜] [GradedRing ℬ]
  (f : 𝒜 →+*ᵍ ℬ)
  (hf : HomogeneousIdeal.irrelevant ℬ ≤ (HomogeneousIdeal.irrelevant 𝒜).map f)

/-- The adjoint pullback map sends a pulled-back section to its actual
fraction image. This is the defining adjunction identity on sections. -/
theorem pullbackHom_pullbackSections (n : ℤ) (U : (Proj 𝒜).Opens)
    (s : Γ(Proj.twistingSheaf 𝒜 n, U)) :
    (pullbackHom f hf n).app ((Proj.map f hf) ⁻¹ᵁ U)
      (ModulePullbackLocal.sections (Proj.map f hf) (Proj.twistingSheaf 𝒜 n) U s) =
        sectionsMap f hf n U s := by
  have h := ((Scheme.Modules.pullbackPushforwardAdjunction (Proj.map f hf)).homEquiv
    (Proj.twistingSheaf 𝒜 n) (Proj.twistingSheaf ℬ n)).apply_symm_apply
      (pushforwardHom f hf n)
  rw [Adjunction.homEquiv_unit] at h
  exact congrArg (fun q => q.app U s) h

/-- The same identity after restriction to an arbitrary smaller open. -/
theorem pullbackHom_pullbackSectionsLE (n : ℤ) (U : (Proj 𝒜).Opens)
    (V : (Proj ℬ).Opens) (hV : V ≤ (Proj.map f hf) ⁻¹ᵁ U)
    (s : Γ(Proj.twistingSheaf 𝒜 n, U)) :
    (pullbackHom f hf n).app V
      (ModulePullbackLocal.sectionsLE (Proj.map f hf) (Proj.twistingSheaf 𝒜 n) U V hV s) =
        (Proj.twistingSheaf ℬ n).presheaf.map (homOfLE hV).op
          (sectionsMap f hf n U s) := by
  have hn := PresheafOfModules.naturality_apply (pullbackHom f hf n).val
    (homOfLE hV).op
    (ModulePullbackLocal.sections (Proj.map f hf) (Proj.twistingSheaf 𝒜 n) U s)
  exact hn.trans (congrArg
    ((Proj.twistingSheaf ℬ n).presheaf.map (homOfLE hV).op)
    (pullbackHom_pullbackSections f hf n U s))

set_option backward.isDefEq.respectTransparency false in
/-- The standard generator is carried to the standard generator, including
negative twists and rings with zero divisors. -/
theorem pullbackHom_chartGenerator (n : ℤ) (a : A) (ha : a ∈ 𝒜 1)
    (V : (Proj ℬ).Opens) (hV : V ≤ Proj.basicOpen ℬ (f a)) :
    (pullbackHom f hf n).app V
      (ModulePullbackLocal.sectionsLE (Proj.map f hf) (Proj.twistingSheaf 𝒜 n)
        (Proj.basicOpen 𝒜 a) V hV
        (Proj.twistingSheaf.chartGenerator n a ha _ le_rfl)) =
      Proj.twistingSheaf.chartGenerator n (f a) (f.map_mem ha) V hV := by
  rw [pullbackHom_pullbackSectionsLE]
  apply Proj.twistingSheaf.ext
  intro x
  change Localization.localRingHom _ _ f.toRingHom rfl
    ((Proj.twistingSheaf.chartGenerator n a ha (Proj.basicOpen 𝒜 a) le_rfl).val
      ⟨ProjectiveSpectrum.comap f hf x.val, hV x.property⟩) = _
  simp only [Proj.twistingSheaf.chartGenerator_apply, Localization.localRingHom_mk,
    map_pow, GradedRingHom.coe_toRingHom]

/-- On every open inside an image coordinate chart, the actual pullback
map on sections is surjective. -/
theorem pullbackHom_app_surjective (n : ℤ) (a : A) (ha : a ∈ 𝒜 1)
    (V : (Proj ℬ).Opens) (hV : V ≤ Proj.basicOpen ℬ (f a)) :
    Function.Surjective ((pullbackHom f hf n).app V) := by
  intro s
  let c := (Proj.twistingSheaf.chartSectionsLinearEquiv
    n (f a) (f.map_mem ha) V hV).symm s
  refine ⟨c • ModulePullbackLocal.sectionsLE (Proj.map f hf) (Proj.twistingSheaf 𝒜 n)
    (Proj.basicOpen 𝒜 a) V hV
    (Proj.twistingSheaf.chartGenerator n a ha _ le_rfl), ?_⟩
  rw [(pullbackHom f hf n).app_smul, pullbackHom_chartGenerator]
  exact (Proj.twistingSheaf.chartSectionsLinearEquiv
    n (f a) (f.map_mem ha) V hV).apply_symm_apply s

include hf in
/-- A degree-one covering family remains a covering family after the
actual projective morphism. -/
theorem image_degreeOne_cover {ι : Type u} (a : ι → A)
    (hcover : ⨆ i, Proj.basicOpen 𝒜 (a i) = ⊤) :
    ⨆ i, Proj.basicOpen ℬ (f (a i)) = ⊤ := by
  apply top_unique
  intro x hx
  have hx' : ProjectiveSpectrum.comap f hf x ∈
      (⨆ i, Proj.basicOpen 𝒜 (a i)) := by rw [hcover]; trivial
  obtain ⟨i, hi⟩ := Opens.mem_iSup.mp hx'
  exact Opens.mem_iSup.mpr ⟨i, hi⟩

/-- The canonical pullback map is an isomorphism whenever degree-one
standard opens cover. This is a theorem about the original sheaves. -/
theorem pullbackHom_isIso_of_degreeOne_cover {ι : Type u} (a : ι → A)
    (ha : ∀ i, a i ∈ 𝒜 1)
    (hcover : ⨆ i, Proj.basicOpen 𝒜 (a i) = ⊤) (n : ℤ) :
    IsIso (pullbackHom f hf n) := by
  have htarget := image_degreeOne_cover f hf a hcover
  apply SheafOfModules.isIso_of_coversTop
    ((_root_.Opens.coversTop_iff _ _).mpr (IsOpenCover.mk htarget))
    (pullbackHom f hf n)
  intro i
  let p := Proj.map f hf
  let U := Proj.basicOpen 𝒜 (a i)
  let e : ((Scheme.Modules.pullback p).obj (Proj.twistingSheaf 𝒜 n)).over (p ⁻¹ᵁ U) ≅
      SheafOfModules.unit ((Proj ℬ).ringCatSheaf.over (p ⁻¹ᵁ U)) :=
    ((ModulePullbackLocal.overUnitIso p U) ≪≫
      (ModulePullbackLocal.overPullback p U).mapIso (Proj.twistingSheaf.chartIso n (a i) (ha i)) ≪≫
      ModulePullbackLocal.overObjIso p U (Proj.twistingSheaf 𝒜 n)).symm
  apply LineSheafSurjective.isIso_over_of_surjective (pullbackHom f hf n)
    (Proj.basicOpen ℬ (f (a i))) e
    (Proj.twistingSheaf.chartIso n (f (a i)) (f.map_mem (ha i))).symm
  intro V
  exact pullbackHom_app_surjective f hf n (a i) (ha i) V.left V.hom.le

/-- Canonical pullback of every integer twist under any generated graded
map. Inverse coordinates or an isomorphism hypothesis are unnecessary. -/
def pullbackIso_of_degreeOne_cover {ι : Type u} (a : ι → A)
    (ha : ∀ i, a i ∈ 𝒜 1)
    (hcover : ⨆ i, Proj.basicOpen 𝒜 (a i) = ⊤) (n : ℤ) :
    (Scheme.Modules.pullback (Proj.map f hf)).obj (Proj.twistingSheaf 𝒜 n) ≅
      Proj.twistingSheaf ℬ n := by
  letI := pullbackHom_isIso_of_degreeOne_cover f hf a ha hcover n
  exact asIso (pullbackHom f hf n)

end PaperVerification.TwistingSheafMap
end
end
end ComponentSource_4

run_cmd Lean.logInfo "COMPONENT_SOURCE_END: PaperVerification.TwistingSheafPullback"

section ComponentSource_5
/- Original module: PaperVerification.AlternatingFormsAmbientPolarization -/


/-!
# The polarization in the ambient zero-scheme comparison

The original Proj twisting sheaf is the pullback of the ambient twisting
sheaf under the actual graded quotient map.  The zero-scheme isomorphism
therefore respects every integer Plücker twist, including the polarization.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open AlgebraicGeometry CategoryTheory MvPolynomial

namespace PaperVerification.AlternatingForms

variable {K : Type} [Field K] {t n m : ℕ}

/-- Every original Proj twist is the restriction of the ambient Plücker twist. -/
def isotropicAmbientTwistingPullbackIso (forms : Fin m → StrictPairs n → K) (r : ℤ) :
    (Scheme.Modules.pullback (isotropicAmbientImmersion (t := t) forms)).obj
        (Proj.twistingSheaf (isotropicProjectiveGrading (t := t)
          (emptyAlternatingTuple (K := K) (n := n))) r) ≅
      Proj.twistingSheaf (isotropicProjectiveGrading (t := t) forms) r :=
  TwistingSheafMap.pullbackIso_of_degreeOne_cover (ambientGradedQuotient forms)
    (irrelevant_le_map_of_gradedSurjective _
      (HomogeneousQuotientProjective.quotientGradedHom_surjective _ _ _ _ _))
    (fun p : PluckerIndex (t + 2) n ↦ Ideal.Quotient.mk _ (X p))
    (HomogeneousQuotientProjective.quotient_X_mem_one _ _)
    (isotropicProjBasicOpen_cover_arbitraryChar emptyAlternatingTuple) r

/-- The usual Plücker twist on the independently constructed zero scheme. -/
def ambientSectionZeroTwist (forms : Fin m → StrictPairs n → K) (r : ℤ) :
    (ambientSectionZeroScheme (t := t) forms).Modules :=
  (Scheme.Modules.pullback (ambientSectionZeroIdeal forms).subschemeι).obj
    (Proj.twistingSheaf (isotropicProjectiveGrading (t := t)
      (emptyAlternatingTuple (K := K) (n := n))) r)

/-- The comparison of schemes is a comparison of their actual Plücker twists. -/
def isotropicSectionZeroTwistingIso (forms : Fin m → StrictPairs n → K) (r : ℤ) :
    (Scheme.Modules.pullback (isotropicSectionZeroIso (t := t) forms).hom).obj
        (ambientSectionZeroTwist forms r) ≅
      Proj.twistingSheaf (isotropicProjectiveGrading (t := t) forms) r :=
  (Scheme.Modules.pullbackComp (isotropicSectionZeroIso forms).hom
    (ambientSectionZeroIdeal forms).subschemeι).app _ ≪≫
      eqToIso (congrArg (fun f ↦ (Scheme.Modules.pullback f).obj
        (Proj.twistingSheaf (isotropicProjectiveGrading (t := t)
          (emptyAlternatingTuple (K := K) (n := n))) r))
          (isotropicSectionZeroIso_over_ambient forms)) ≪≫
      isotropicAmbientTwistingPullbackIso forms r

end PaperVerification.AlternatingForms
end
end
end ComponentSource_5

run_cmd Lean.logInfo "COMPONENT_SOURCE_END: PaperVerification.AlternatingFormsAmbientPolarization"


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
    (`PaperVerification.GradedSurjective, "definition"),
    (`PaperVerification.irrelevant_le_map_of_gradedSurjective, "theorem"),
    (`PaperVerification.gradedAwayMap_surjective, "theorem"),
    (`PaperVerification.gradedProjMap_chart_isPullback, "theorem"),
    (`PaperVerification.isClosedImmersion_projMap_of_gradedSurjective, "theorem"),
    (`PaperVerification.HomogeneousQuotientProjective.quotientGradedHom, "definition"),
    (`PaperVerification.HomogeneousQuotientProjective.quotientGradedHom_surjective, "theorem"),
    (`PaperVerification.HomogeneousQuotientProjective.quotientProjMap, "definition"),
    (`PaperVerification.AlternatingForms.emptyAlternatingTuple, "definition"),
    (`PaperVerification.AlternatingForms.isotropicPluckerIdeal_empty, "theorem"),
    (`PaperVerification.AlternatingForms.isotropicChartIdeal_empty, "theorem"),
    (`PaperVerification.AlternatingForms.ambientGrassmannian, "definition"),
    (`PaperVerification.AlternatingForms.isotropicAmbientImmersion, "definition"),
    (`PaperVerification.AlternatingForms.isotropicAmbientImmersion_preimage_chart, "theorem"),
    (`PaperVerification.AlternatingForms.ambientChartRingEquiv, "definition"),
    (`PaperVerification.AlternatingForms.ambientChartRing_commutes, "theorem"),
    (`PaperVerification.AlternatingForms.isotropicAffineChart_ambient_commutes, "theorem"),
    (`PaperVerification.AlternatingForms.isotropicAffineChart_ambient_isPullback, "theorem"),
    (`PaperVerification.AlternatingForms.isotropicAffineChartCover, "definition"),
    (`PaperVerification.AlternatingForms.isotropicChartSectionFunctional, "definition"),
    (`PaperVerification.AlternatingForms.isotropicChartSectionFunctional_range, "theorem"),
    (`PaperVerification.AlternatingForms.ambientSectionChartIdeal, "definition"),
    (`PaperVerification.AlternatingForms.ambientSectionZeroIdeal, "definition"),
    (`PaperVerification.AlternatingForms.ambientSectionZeroScheme, "definition"),
    (`PaperVerification.AlternatingForms.ambientSectionZeroIdeal_eq_kernel, "theorem"),
    (`PaperVerification.AlternatingForms.ambientSectionZeroIdeal_chart, "theorem"),
    (`PaperVerification.AlternatingForms.isotropicSectionZeroIso, "definition"),
    (`PaperVerification.AlternatingForms.isotropicSectionZeroIso_over_ambient, "theorem"),
    (`PaperVerification.AlternatingForms.tautologicalAlternatingFunctional, "definition"),
    (`PaperVerification.AlternatingForms.tautologicalFrameCoordinates, "definition"),
    (`PaperVerification.AlternatingForms.tautologicalRowSection_coordinates, "theorem"),
    (`PaperVerification.AlternatingForms.tautologicalAlternatingFunctional_row_wedge, "theorem"),
    (`PaperVerification.AlternatingForms.ambientAlternatingFunctional_row_wedge, "theorem"),
    (`PaperVerification.AlternatingForms.ambientChartPolynomialHom_bijective, "theorem"),
    (`PaperVerification.TwistingSheafMap.pullbackHom_chartGenerator, "theorem"),
    (`PaperVerification.TwistingSheafMap.pullbackHom_isIso_of_degreeOne_cover, "theorem"),
    (`PaperVerification.TwistingSheafMap.pullbackIso_of_degreeOne_cover, "definition"),
    (`PaperVerification.AlternatingForms.isotropicAmbientTwistingPullbackIso, "definition"),
    (`PaperVerification.AlternatingForms.ambientSectionZeroTwist, "definition"),
    (`PaperVerification.AlternatingForms.isotropicSectionZeroTwistingIso, "definition"),
    (`PaperVerification.AlternatingForms.isotropicPluckerIdeal_map_chart_eq_arbitraryChar, "theorem"),
    (`PaperVerification.AlternatingForms.isotropicChartEvaluation_kernel_arbitraryChar, "theorem"),
    (`PaperVerification.AlternatingForms.isotropicPluckerBigCellEquiv_arbitraryChar, "definition"),
    (`PaperVerification.AlternatingForms.isotropicProjChartRingEquiv_arbitraryChar, "definition"),
    (`PaperVerification.AlternatingForms.isotropicProjBasicOpenIso_arbitraryChar, "definition"),
    (`PaperVerification.AlternatingForms.isotropicProjBasicOpen_cover_arbitraryChar, "theorem"),
    (`PaperVerification.AlternatingForms.tautologicalFrameIso, "definition"),
    (`PaperVerification.AlternatingForms.tautologicalPivotMap_bijective, "theorem"),
    (`PaperVerification.AlternatingForms.tautologicalDefiningFunctional_eq_zero, "theorem")
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
    ("nonce", toJson "3d9ddbd796eb612b548a620f2d73ebb7"), ("declaration_count", toJson localNames.size),
    ("kernel_trust_level", toJson env.header.trustLevel.toNat),
    ("kernel_type_checking_enabled", toJson (!Lean.debug.skipKernelTC.get opts)),
    ("server_mode", toJson (Lean.Elab.inServer.get opts)),
    ("required_endpoint_count", toJson required.size),
    ("all_new_declarations_read_from_checked_environment", toJson true),
    ("declarations", toJson rows)]).pretty
  logInfo "LITERAL_COMPONENT_KERNEL_AUDIT_COMPLETE:3d9ddbd796eb612b548a620f2d73ebb7"
