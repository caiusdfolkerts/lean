module

public import PaperVerification.AlternatingSectionAlgebra
public import TauCeti.Algebra.Category.ModuleCat.Presheaf.ExteriorPower.Basic

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
