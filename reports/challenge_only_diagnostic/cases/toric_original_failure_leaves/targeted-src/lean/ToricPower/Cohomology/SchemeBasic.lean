module

public import ToricPower.Cohomology.SheafTerminal
public import ToricPower.Cohomology.ModuleSheaf
public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.HasExt
public import Mathlib.Topology.Sheaves.Abelian

public section

section SchemeCohomologySource66
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/


/-!
# Cohomology of sheaves of modules on a scheme

Mathlib defines the cohomology `CategoryTheory.Sheaf.H` of an abelian sheaf on a site as an
`Ext` group from the constant sheaf `ℤ`. This file applies that construction to the underlying
abelian sheaf of an `𝒪_X`-module and packages the result in the scheme-module API.

For a scheme `X` and `M : X.Modules`, the main declarations are:

* `Scheme.Modules.Cohomology M i`, the group `Hⁱ(X, M)`;
* `Scheme.Modules.cohomologyFunctor X i`, functoriality in the coefficient sheaf;
* `Scheme.Modules.cohomologyZeroEquiv`, the canonical equivalence
  `H⁰(X, M) ≃+ Γ(M, ⊤)` with global sections;
* `Scheme.Modules.cohomologyOn M n U`, the cohomology `Hⁿ(U, M)` of an open subset,
  `Scheme.Modules.cohomologyOnRes` its restriction maps, and
  `Scheme.Modules.cohomologyOnTopIso` the identification of `Hⁿ(⊤, M)` with `Hⁿ(X, M)`.

The construction is stated for every sheaf of modules, which is the natural generality of sheaf
cohomology. In particular it applies to finitely presented sheaves through their underlying
objects, and hence supplies the `Hⁱ(X, ℱ)` used for coherent sheaves in
`TauCetiRoadmap/JacobianChallenge/README.md`, Layer B. Finite-dimensionality for proper schemes,
vanishing on curves, and the comparison with Čech cohomology remain later Layer B work.

No formalization is vendored. The definitions reuse Mathlib's `Sheaf.H`, `Sheaf.functorH`,
`Sheaf.H.equiv₀` and `Sheaf.H'`, and the comparison at the terminal open subset is
`TauCeti/CategoryTheory/Sites/SheafCohomology/Terminal.lean`.
-/

public section

open CategoryTheory Limits TopologicalSpace AlgebraicGeometry

namespace TauCeti

namespace AlgebraicGeometry

universe u

noncomputable section

namespace Scheme.Modules

variable {X : Scheme.{u}}

/-- Degree-`i` cohomology as an additive functor from sheaves of modules to abelian groups. -/
abbrev cohomologyFunctor (X : Scheme.{u}) (i : ℕ) : X.Modules ⥤ AddCommGrpCat.{u} :=
  toSheaf X ⋙
    CategoryTheory.Sheaf.functorH.{u} _ i

/-- The genuine `i`th sheaf cohomology group. Reading the underlying type
from the canonical additive functor makes its group structure share the
same expression as every induced cohomology map. -/
abbrev Cohomology (M : X.Modules) (i : ℕ) : Type u :=
  (cohomologyFunctor X i).obj M

/-- The functor-value presentation is definitionally ordinary Mathlib
sheaf cohomology on the small Zariski site. -/
theorem Cohomology_eq_sheafH (M : X.Modules) (i : ℕ) :
    Cohomology M i = CategoryTheory.Sheaf.H.{u}
      ((_root_.SheafOfModules.toSheaf.{u} X.ringCatSheaf).obj M) i := rfl

/-- Degreewise scheme-module cohomology preserves addition and zero morphisms. -/
instance (X : Scheme.{u}) (i : ℕ) : (cohomologyFunctor X i).Additive :=
  inferInstanceAs ((toSheaf X ⋙
    CategoryTheory.Sheaf.functorH.{u} _ i).Additive)

/-- Zeroth cohomology is canonically equivalent to the group of global sections.

Naturality in the coefficient sheaf follows from `CategoryTheory.Sheaf.H.equiv₀_naturality`
and `CategoryTheory.Sheaf.H.equiv₀_symm_naturality`, applied to `isTerminalTop` and the
underlying sheaf morphism. -/
def cohomologyZeroEquiv (M : X.Modules) :
    Cohomology M 0 ≃+ Γ(M, ⊤) :=
  CategoryTheory.Sheaf.H.equiv₀
    ((toSheaf X).obj M) isTerminalTop

/-- The degree-zero cohomology equivalence is natural in the coefficient sheaf. -/
lemma cohomologyZeroEquiv_naturality {M N : X.Modules} (f : M ⟶ N) (x : Cohomology M 0) :
    cohomologyZeroEquiv N ((cohomologyFunctor X 0).map f x) =
      f.app ⊤ (cohomologyZeroEquiv M x) :=
  (CategoryTheory.Sheaf.H.equiv₀_naturality isTerminalTop
    ((toSheaf X).map f) x).symm

section Opens

variable (M : X.Modules)

/-- The cohomology `Hⁿ(U, M)` of an open subset `U` of a scheme `X` with coefficients in a sheaf
of modules `M`, as an abelian group.

This is `CategoryTheory.Sheaf.H'` applied to the underlying abelian sheaf of `M`. At `U = ⊤` it
agrees with `Scheme.Modules.Cohomology`, by `Scheme.Modules.cohomologyOnTopIso`. -/
abbrev cohomologyOn (n : ℕ) (U : Opens X) : AddCommGrpCat.{u} :=
  CategoryTheory.Sheaf.H'.{u} ((toSheaf X).obj M) n U

/-- Restriction in cohomology along an inclusion of open subsets. -/
abbrev cohomologyOnRes (n : ℕ) {U V : Opens X} (h : U ≤ V) :
    cohomologyOn M n V ⟶ cohomologyOn M n U :=
  (CategoryTheory.Sheaf.cohomologyPresheaf.{u}
    ((toSheaf X).obj M) n).map (homOfLE h).op

@[simp]
lemma cohomologyOnRes_refl (n : ℕ) (U : Opens X) :
    cohomologyOnRes M n (le_refl U) = 𝟙 _ := by
  dsimp only [cohomologyOnRes]
  simp only [homOfLE_refl, op_id, CategoryTheory.Functor.map_id]

@[simp, reassoc]
lemma cohomologyOnRes_comp (n : ℕ) {U V W : Opens X} (hUV : U ≤ V) (hVW : V ≤ W) :
    cohomologyOnRes M n hVW ≫ cohomologyOnRes M n hUV =
      cohomologyOnRes M n (hUV.trans hVW) := by
  dsimp only [cohomologyOnRes]
  rw [← CategoryTheory.Functor.map_comp, ← op_comp, homOfLE_comp]

/-- The cohomology of the whole space is the cohomology of the scheme. -/
noncomputable abbrev cohomologyOnTopIso (n : ℕ) :
    cohomologyOn M n ⊤ ≅ AddCommGrpCat.of (Cohomology M n) :=
  ((toSheaf X).obj M).cohomologyPresheafObjIsoH
    n isTerminalTop

end Opens

end Scheme.Modules

end

end AlgebraicGeometry

end TauCeti

end
end SchemeCohomologySource66
