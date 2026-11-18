module

public import ToricPower.QuasicoherentCategory
public import ToricPower.SchemeModulesBaseLinear
public import Mathlib.CategoryTheory.Linear.LinearFunctor

/-!
# The actual base-ring linear structure on quasicoherent sheaves

The Hom modules are inherited from actual module-sheaf morphisms with
their proved base-ring scalar action. This explicit instance bridges the
unfolded sheaf category used by the full-subcategory definition of QCoh.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

namespace ToricPower

universe u

variable (R : Type u) [CommRing R] (X : Scheme.{u}) [X.Over (Spec (.of R))]

/-- The intrinsic quasicoherent category has exactly the inherited
actual base-ring Hom-module structure. -/
instance quasicoherentBaseLinear : Linear R (QCoh X) := by
  letI : Linear R (_root_.SheafOfModules X.ringCatSheaf) :=
    Scheme.Modules.baseLinear R X
  infer_instance

/-- The actual inclusion preserves that same scalar action. -/
instance quasicoherentInclusion_baseLinear : (quasicoherentInclusion X).Linear R where
  map_smul _ _ := rfl

end ToricPower
