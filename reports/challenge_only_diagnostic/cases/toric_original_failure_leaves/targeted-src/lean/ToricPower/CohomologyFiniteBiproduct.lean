module

public import ToricPower.Cohomology.SchemeBasic
public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
public import Mathlib.Algebra.Category.Grp.Zero

/-!
# Vanishing for actual finite direct sums of module sheaves

The ordinary cohomology functor is additive. Consequently a genuine
finite splitting into acyclic summands gives an acyclic sheaf. The same
argument applies after ordinary restriction to an open subscheme.

The proof uses the categorical finite biproduct and its actual functorial
comparison; no independent direct-sum/cohomology comparison is assumed.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open TauCeti.AlgebraicGeometry.Scheme.Modules

namespace ToricPower

universe u v w

/-- An additive functor to abelian groups kills a finite biproduct when
it kills every summand, including a family presented by an actual iso. -/
theorem additiveFunctor_subsingleton_of_iso_biproduct
    {C : Type u} [Category.{v} C] [Preadditive C] [HasFiniteBiproducts C]
    (F : C ⥤ AddCommGrpCat.{w}) [F.Additive]
    {I : Type*} [Finite I] (family : I → C) (M : C)
    (e : M ≅ ⨁ family) (vanishes : ∀ index, Subsingleton (F.obj (family index))) :
    Subsingleton (F.obj M) := by
  classical
  letI : Fintype I := Fintype.ofFinite I
  -- Mathlib's finite-preservation class is indexed in `Type`; this direct
  -- total-map proof keeps finite indexing types in arbitrary universes.
  letI : PreservesBiproduct family F := by
    constructor
    intro b hb
    refine ⟨isBilimitOfTotal _ ?_⟩
    change (∑ index : I, F.map (b.π index) ≫ F.map (b.ι index)) = 𝟙 (F.obj b.pt)
    simp_rw [← F.map_comp]
    erw [← F.map_sum, ← F.map_id, IsBilimit.total hb]
  have sumZero : IsZero (⨁ fun index => F.obj (family index)) := by
    apply (IsZero.iff_id_eq_zero _).mpr
    apply biproduct.hom_ext
    intro index
    letI := vanishes index
    exact (AddCommGrpCat.isZero_of_subsingleton _).eq_of_tgt _ _
  have objectZero : IsZero (F.obj M) :=
    (F.mapIso e ≪≫ F.mapBiproduct family).isZero_iff.mpr sumZero
  exact AddCommGrpCat.subsingleton_of_isZero objectZero

attribute [local instance] HasFiniteBiproducts.of_hasFiniteProducts

/-- An actual isomorphism of module sheaves preserves vanishing in each
ordinary cohomological degree. -/
theorem cohomology_subsingleton_of_sheaf_iso {X : Scheme.{u}}
    {F G : X.Modules} (e : F ≅ G) (degree : ℕ)
    (vanishes : Subsingleton (Cohomology G degree)) :
    Subsingleton (Cohomology F degree) := by
  letI := vanishes
  exact ((cohomologyFunctor X degree).mapIso e).addCommGroupIsoToAddEquiv.injective.subsingleton

/-- Finite splitting into genuinely acyclic sheaves implies ordinary
cohomological vanishing, in every degree. -/
theorem cohomology_subsingleton_of_iso_biproduct {X : Scheme.{u}}
    {I : Type*} [Finite I] (family : I → X.Modules) (F : X.Modules)
    (e : F ≅ ⨁ family)
    (vanishes : ∀ index degree, Subsingleton (Cohomology (family index) degree)) :
    ∀ degree, Subsingleton (Cohomology F degree) := by
  intro degree
  exact additiveFunctor_subsingleton_of_iso_biproduct
    (cohomologyFunctor X degree) family F e (fun index => vanishes index degree)


end ToricPower

end
