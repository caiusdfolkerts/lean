module

public import ToricPower.HomologyFunctorLinear
public import ToricPower.FiniteAffineIntersectionSections
public import ToricPower.SchemeModulesBaseLinear
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Cech

/-! # Actual scalar linearity of the Čech coefficient functor -/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite

namespace ToricPower.CechScalar

universe u v w

variable {C : Type v} [Category.{w} C] [HasFiniteProducts C]
  {A : Type*} [Category* A] [Preadditive A] [HasProducts.{u} A]
  {I : Type u} (opens : I → C)

instance cechComplexFunctor_additive :
    (cechComplexFunctor (A := A) opens).Additive where
  map_add {P Q} {f g} := by
    apply HomologicalComplex.hom_ext
    intro q
    change Limits.Pi.map (fun t : Fin (q+1) → I =>
        f.app (op (∏ᶜ (opens ∘ t))) + g.app (op (∏ᶜ (opens ∘ t)))) =
      Limits.Pi.map (fun t : Fin (q+1) → I => f.app (op (∏ᶜ (opens ∘ t)))) +
        Limits.Pi.map (fun t : Fin (q+1) → I => g.app (op (∏ᶜ (opens ∘ t))))
    apply Limits.Pi.hom_ext
    intro t
    simp only [Limits.Pi.map_π, Preadditive.comp_add, Preadditive.add_comp]

instance cechComplexFunctor_linear (R : Type*) [Semiring R] [Linear R A] :
    (cechComplexFunctor (A := A) opens).Linear R where
  map_smul f r := by
    apply HomologicalComplex.hom_ext
    intro q
    change Limits.Pi.map (fun t : Fin (q+1) → I =>
        r • f.app (op (∏ᶜ (opens ∘ t)))) =
      r • Limits.Pi.map (fun t : Fin (q+1) → I => f.app (op (∏ᶜ (opens ∘ t))))
    apply Limits.Pi.hom_ext
    intro t
    simp only [Limits.Pi.map_π, Linear.comp_smul, Linear.smul_comp]

variable (k : Type u) [Field k] (X : Scheme.{u}) [X.Over (Spec (.of k))]

instance schemeBasePresheaf_linear : (FiniteCover.schemeBasePresheaf k X).Linear k where
  map_smul f r := by
    ext U x
    exact Scheme.Modules.base_smul_app k X r f U.unop x

/-- Every term is the module of actual sections with the scalar action
restricted along the structure morphism. -/
abbrev linearComplexFunctor {J : Type u} (opens : J → X.Opens) :
    X.Modules ⥤ CochainComplex (ModuleCat.{u} k) ℕ :=
  FiniteCover.schemeBasePresheaf k X ⋙ cechComplexFunctor opens

/-- Actual scalar-linear Čech cohomology, functorial in all sheaves. -/
abbrev linearHomologyFunctor {J : Type u} (opens : J → X.Opens) (degree : ℕ) :
    X.Modules ⥤ ModuleCat.{u} k :=
  linearComplexFunctor k X opens ⋙
    HomologicalComplex.homologyFunctor (ModuleCat.{u} k) (.up ℕ) degree

end ToricPower.CechScalar

end
