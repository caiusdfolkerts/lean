module

public import ToricPower.LinearRelativeCech
public import ToricPower.AdditiveAlternatingCoface
public import Mathlib.Algebra.Homology.ShortComplex.PreservesHomology
public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Colimits
public import Mathlib.Algebra.Category.Grp.Abelian

/-!
# The exact scalar-forgetting comparison for relative Čech cohomology

The complex isomorphism retains every tuple restriction and differential.
Exactness of the actual forgetful functor then identifies its cohomology
with that of the established additive relative complex.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits

namespace ToricPower.LinearRelativeCech

variable (k : Type) [Field k] {Ray : Type*} {Chart : Type}
  (incidence : Ray → Chart → Prop) (negative : Ray → Prop)

/-- The full relative complex with its actual scalar action forgets
to the independently proved additive complex. -/
def complexForgetIso :
    NegativeSupportCech.relativeComplex k incidence negative ≅
      ((forget₂ (ModuleCat k) AddCommGrpCat).mapHomologicalComplex (.up ℕ)).obj
        (complex k incidence negative) :=
  (AlgebraicTopology.alternatingCofaceMapComplex _).mapIso
      (cosimplicialForgetIso k incidence negative) ≪≫
    additiveAlternatingCofaceIso (forget₂ (ModuleCat k) AddCommGrpCat)
      (cosimplicial k incidence negative)

/-- The canonical actual homology comparison after forgetting scalars. -/
def homologyForgetIso (q : ℕ) :
    (NegativeSupportCech.relativeComplex k incidence negative).homology q ≅
      (forget₂ (ModuleCat k) AddCommGrpCat).obj ((complex k incidence negative).homology q) :=
  (HomologicalComplex.homologyFunctor AddCommGrpCat (.up ℕ) q).mapIso
      (complexForgetIso k incidence negative) ≪≫
    ((complex k incidence negative).sc q).mapHomologyIso (forget₂ (ModuleCat k) AddCommGrpCat)

/-- Vanishing and nonvanishing use the same underlying cohomology;
no vector-space dimension claim is inferred from an additive isomorphism. -/
theorem homology_nontrivial_iff (q : ℕ) :
    Nontrivial ((complex k incidence negative).homology q) ↔
      Nontrivial ((NegativeSupportCech.relativeComplex k incidence negative).homology q) :=
  (homologyForgetIso k incidence negative q).addCommGroupIsoToAddEquiv.toEquiv.nontrivial_congr.symm

end ToricPower.LinearRelativeCech

end
