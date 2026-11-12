module

public import ToricPower.Cohomology.SchemeBasic
public import ToricPower.Cohomology.ModuleBase
public import ToricPower.Cohomology.ModuleSheaf
public import ToricPower.Cohomology.SheafLongExactSequence
public import ToricPower.Cohomology.LinearExact

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1000000

section SchemeCohomologySource72
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/


/-!
# The long exact cohomology sequence of a short exact sequence of sheaves of modules

`TauCeti/AlgebraicGeometry/Cohomology/Basic.lean` defines the cohomology `Hⁿ(X, M)` of a sheaf
of modules on a scheme. This file adds the long exact sequence attached to a short exact
sequence `0 ⟶ M₁ ⟶ M₂ ⟶ M₃ ⟶ 0` of `𝒪_X`-modules,

`0 ⟶ H⁰(X, M₁) ⟶ H⁰(X, M₂) ⟶ H⁰(X, M₃) ⟶ H¹(X, M₁) ⟶ H¹(X, M₂) ⟶ ⋯`

together with its consequences for global sections. Where
`TauCeti/AlgebraicGeometry/Cohomology/MayerVietoris.lean` varies the open subset, this file
varies the coefficients.

## Main declarations

* `Scheme.Modules.cohomologyMap`, a morphism of sheaves of modules as a map on cohomology;
* `Scheme.Modules.cohomologyδ`, the connecting map `Hⁿ⁰(X, M₃) ⟶ Hⁿ¹(X, M₁)`, together with the
  three exactness statements `Scheme.Modules.exact_cohomologyMap_cohomologyMap`,
  `Scheme.Modules.exact_cohomologyMap_cohomologyδ` and
  `Scheme.Modules.exact_cohomologyδ_cohomologyMap`;
* `Scheme.Modules.cohomologyMap_injective`, the injectivity in degree zero at which the sequence
  starts, and `Scheme.Modules.cohomologyMap_surjective`, the surjectivity it gives when the next
  cohomology group of `M₁` vanishes;
* `Scheme.Modules.subsingleton_cohomology_X₂`, `Scheme.Modules.subsingleton_cohomology_X₃` and
  `Scheme.Modules.subsingleton_cohomology_X₁`, the vanishing consequences;
* `Scheme.Modules.finiteDimensional_cohomology_X₂`: in a short exact sequence, `Hⁱ(X, M₂)` is
  finite-dimensional when `Hⁱ(X, M₁)` and `Hⁱ(X, M₃)` are, and
  `Scheme.Modules.finiteDimensional_cohomology_X₁`: `Hⁱ⁺¹(X, M₁)` is finite-dimensional when
  `Hⁱ(X, M₃)` and `Hⁱ⁺¹(X, M₂)` are;
* `Scheme.Modules.exact_sections` and `Scheme.Modules.sections_injective`: global sections are
  left exact, and `Scheme.Modules.sections_surjective`: they are exact on the right as soon as
  `H¹(X, M₁)` vanishes. This last statement is the form in which the sequence is normally used;
* `Scheme.Modules.cohomologyδ_naturality`, the naturality of the connecting map in the short
  exact sequence, and the linearity it gives: `Scheme.Modules.cohomologyδLinear` over the ring
  of global functions and `Scheme.Modules.cohomologyδBaseLinear` over the base ring of a scheme
  over a commutative ring. The maps induced by morphisms of sheaves are already linear, so this
  makes the whole long exact sequence one of modules; a dimension count in it needs that.

Additivity of the Euler characteristic, and with it Riemann-Roch, rest on this sequence. The
sequence itself is Mathlib's `CategoryTheory.Sheaf.H.longSequence`, repackaged in
`TauCeti.CategoryTheory.Sites.SheafCohomology.LongExactSequence`; exactness of forgetting the
module structures is in `TauCeti.AlgebraicGeometry.Modules.Sheaf`, and the comparison of
degree-zero cohomology with global sections is `Scheme.Modules.cohomologyZeroEquiv`.
-/

public section

open CategoryTheory Limits TopologicalSpace AlgebraicGeometry Scheme.Modules

namespace TauCeti

namespace AlgebraicGeometry

universe u

noncomputable section

namespace Scheme.Modules

variable {X : Scheme.{u}}

/-- A morphism of sheaves of modules on a scheme, as a map on degree-`n` cohomology. -/
abbrev cohomologyMap {M N : X.Modules} (f : M ⟶ N) (n : ℕ) :
    Cohomology M n →+ Cohomology N n :=
  cohomologyMapAddHom f n

/-- The additive coefficient map is exactly Mathlib's map on sheaf cohomology. -/
theorem cohomologyMap_eq_sheafH {M N : X.Modules} (f : M ⟶ N) (n : ℕ) :
    cohomologyMap f n = CategoryTheory.Sheaf.H.map ((toSheaf X).map f) n := by
  simp only [cohomologyMap, cohomologyMapAddHom, cohomologyFunctor,
    CategoryTheory.Functor.comp_map, CategoryTheory.Sheaf.functorH_map,
    AddCommGrpCat.hom_ofHom]

@[simp]
lemma cohomologyFunctor_map {M N : X.Modules} (f : M ⟶ N) (n : ℕ) :
    (cohomologyFunctor X n).map f = AddCommGrpCat.ofHom (cohomologyMap f n) :=
  by rfl

/-- Under the identification of degree-zero cohomology with global sections, the map induced on
cohomology by a morphism of sheaves of modules is the map induced on global sections. -/
@[simp]
lemma cohomologyZeroEquiv_cohomologyMap {M N : X.Modules} (f : M ⟶ N) (x : Cohomology M 0) :
    cohomologyZeroEquiv N (cohomologyMap f 0 x) = f.app ⊤ (cohomologyZeroEquiv M x) :=
  cohomologyZeroEquiv_naturality f x

lemma cohomologySections_ladder {M N : X.Modules} (f : M ⟶ N) :
    (f.app ⊤).hom.comp (cohomologyZeroEquiv M) =
      (cohomologyZeroEquiv N : Cohomology N 0 →+ Γ(N, ⊤)).comp (cohomologyMap f 0) := by
  ext x
  exact (cohomologyZeroEquiv_cohomologyMap f x).symm

end Scheme.Modules

end

end AlgebraicGeometry

end TauCeti

end
end SchemeCohomologySource72
