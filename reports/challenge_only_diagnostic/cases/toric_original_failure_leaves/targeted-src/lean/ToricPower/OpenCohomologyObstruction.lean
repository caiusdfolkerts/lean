module

public import ToricPower.DerivedGlobalSectionsPlus
public import ToricPower.CohomologyFiniteBiproduct

/-!
# The structure sheaf witnesses a nonzero open cohomology functor

On a nonempty scheme, the global unit section is nonzero.
The actual degree-zero cohomology/sections equivalence therefore shows
that derived global sections do not kill the structure sheaf.

Combining this with the actual exact open-restriction functor gives a
generation obstruction for a coherent sheaf acyclic on that open set.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory
open TauCeti.AlgebraicGeometry.Scheme.Modules

namespace ToricPower

universe u

attribute [local instance] HasFiniteBiproducts.of_hasFiniteProducts

/-- The same finite-splitting calculation after actual open restriction. -/
theorem openCohomology_subsingleton_of_iso_biproduct
    {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
    {I : Type*} [Finite I] (family : I → X.Modules) (F : X.Modules)
    (e : F ≅ ⨁ family)
    (vanishes : ∀ index degree, Subsingleton
      (Cohomology ((Scheme.Modules.restrictFunctor j).obj (family index)) degree)) :
    ∀ degree, Subsingleton (Cohomology ((Scheme.Modules.restrictFunctor j).obj F) degree) := by
  intro degree
  exact additiveFunctor_subsingleton_of_iso_biproduct
    (Scheme.Modules.restrictFunctor j ⋙ cohomologyFunctor U degree)
    family F e (fun index => vanishes index degree)


/-- The actual structure sheaf as an object of the coherent category. -/
def coherentStructureSheaf (X : Scheme.{u}) : Coh X :=
  ⟨𝟙_ X.Modules,
    (SheafOfModules.isFinitePresentation X.ringCatSheaf).prop_of_iso
      (TauCeti.SheafOfModules.freePUnitIsoUnit X.ringCatSheaf) inferInstance⟩

/-- The global unit gives nonzero ordinary degree-zero cohomology on a
nonempty scheme. The scheme's local rings establish nontriviality. -/
theorem structureSheaf_cohomologyZero_nontrivial (X : Scheme.{u}) [Nonempty X] :
    Nontrivial (Cohomology (𝟙_ X.Modules) 0) := by
  have sectionsNontrivial : Nontrivial Γ(𝟙_ X.Modules, ⊤) := by
    change Nontrivial Γ(X, ⊤)
    infer_instance
  exact (cohomologyZeroEquiv (𝟙_ X.Modules)).toEquiv.nontrivial_congr.mpr
    sectionsNontrivial

/-- A coherent sheaf with zero cohomology on a nonempty open
subscheme cannot generate the literal bounded coherent derived category. -/
theorem not_generatesDbCoh_of_nonempty_open_cohomology_vanishes
    {U X : Scheme.{u}} [IsLocallyNoetherian U] [IsLocallyNoetherian X]
    [Nonempty U] (j : U ⟶ X) [IsOpenImmersion j] (G : Coh X)
    (vanishes : ∀ degree, Subsingleton
      (Cohomology ((Scheme.Modules.restrictFunctor j).obj G.obj) degree)) :
    ¬ generatesDbCoh (coherentSingle X G) := by
  apply not_generatesDbCoh_of_open_cohomology_vanishes
    j G (coherentStructureSheaf X) vanishes
  intro allZero
  have unitZero : Subsingleton (Cohomology (𝟙_ U.Modules) 0) :=
    cohomology_subsingleton_of_sheaf_iso (Scheme.Modules.restrictUnitIso j).symm
      0 (allZero 0)
  exact not_nontrivial_iff_subsingleton.mpr unitZero
    (structureSheaf_cohomologyZero_nontrivial U)

end ToricPower

end
