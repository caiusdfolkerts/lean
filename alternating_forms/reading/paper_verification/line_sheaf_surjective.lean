module

public import TauCeti.Algebra.Category.ModuleCat.Sheaf.LocalIsomorphism
public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.Algebra.Category.ModuleCat.EpiMono

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
