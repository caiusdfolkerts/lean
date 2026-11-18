module

public import ToricPower.CohomologyFiniteDimensional
public import ToricPower.SchemeModulesBaseLinear
public import ToricPower.AdditiveFunctorLinearLift

/-!
# The actual base-linear ordinary cohomology functor

The scalar action is the canonical action of restricted global
functions. Its equality with the coefficient-functor scalar action is
proved explicitly, allowing natural additive comparisons to be lifted
without changing either mathematical module structure.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory
open TauCeti.AlgebraicGeometry.Scheme.Modules

namespace ToricPower

universe u
variable (k : Type u) [Field k] (X : Scheme.{u}) [X.Over (Spec (.of k))]

instance cohomologyBaseFunctor_linear (degree : ℕ) :
    (cohomologyBaseFunctor k X degree).Linear k where
  map_smul {M N} f r := by
    ext x
    simp only [cohomologyBaseFunctor, ModuleCat.hom_ofHom,
      ModuleCat.hom_smul, LinearMap.smul_apply,
      Scheme.Modules.cohomologyMapBaseLinear_apply]
    rw [Scheme.Modules.base_smul_eq,
      CategoryTheory.Functor.map_comp_apply,
      Scheme.Modules.base_smul_cohomology, Scheme.Modules.cohomology_smul]

/-- Forgetting the canonical base scalars leaves precisely the ordinary
sheaf-cohomology functor, including every coefficient map. -/
def cohomologyBaseFunctorForgetIso (degree : ℕ) :
    cohomologyBaseFunctor k X degree ⋙ forget₂ (ModuleCat.{u} k) AddCommGrpCat.{u} ≅
      cohomologyFunctor X degree :=
  NatIso.ofComponents (fun _ => Iso.refl _) (by
    intro M N f
    simp only [Iso.refl_hom, Category.id_comp, Category.comp_id]
    apply AddCommGrpCat.hom_ext
    apply AddMonoidHom.ext
    intro x
    exact Scheme.Modules.cohomologyMapBaseLinear_apply k X f degree x)

/-- The canonical scalar lift of ordinary cohomology is its genuine
base-linear cohomology, with identity on the underlying groups. -/
def cohomologyCanonicalLiftIso (degree : ℕ) :
    additiveLinearLift k (cohomologyFunctor X degree) ≅
      cohomologyBaseFunctor k X degree :=
  (additiveLinearLiftNatIso k (cohomologyBaseFunctorForgetIso k X degree)).symm ≪≫
    additiveLinearLiftForgetIso k (cohomologyBaseFunctor k X degree)

end ToricPower

end
