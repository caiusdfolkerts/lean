module

public import ToricPower.ToricCoherentDerivedEmbedding
public import ToricPower.QuasicoherentBaseLinear
public import Mathlib.Algebra.Homology.DerivedCategory.Linear

/-! # The actual base-field linear coherent inclusion -/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory

namespace ToricPower

universe u
variable (k : Type u) [CommRing k] (X : Scheme.{u}) [X.Over (Spec (.of k))]

instance coherentBaseLinear : Linear k (Coh X) := by
  letI : Linear k (_root_.SheafOfModules X.ringCatSheaf) :=
    Scheme.Modules.baseLinear k X
  infer_instance

instance coherentToQuasicoherent_baseLinear : (coherentToQuasicoherent X).Linear k where
  map_smul _ _ := rfl

variable [IsLocallyNoetherian X]
local instance coherentBaseLinearInstance1 : HasDerivedCategory.{u+1} (Coh X) := HasDerivedCategory.standard _
local instance coherentBaseLinearInstance2 : HasDerivedCategory.{u+1} (QCoh X) := HasDerivedCategory.standard _

instance boundedCoherentToQuasicoherent_baseLinear :
    (boundedCoherentToQuasicoherent X).Linear k := by
  unfold boundedCoherentToQuasicoherent
  infer_instance

end ToricPower
end
