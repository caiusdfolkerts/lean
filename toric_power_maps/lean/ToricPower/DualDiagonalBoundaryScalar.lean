module

public import ToricPower.DualDiagonalBoundaryModule
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings

/-!
# The genuine coefficient-field action on the boundary module

Scalar restriction of the independently defined chart-ring action agrees
with the original coefficient-field action. The comparison is the
identity on finite Laurent coefficient functions; its linearity follows
from the defining algebra homomorphism of the monomial representation.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory

namespace ToricPower.IntegralArrangement

variable {n s : ℕ} (A : Fin s → Fin n → ℤ) (S T : Set (Fin s))
  (k : Type) [CommRing k]

/-- No scalar action is transported by fiat: this is the identity map
between the original two coefficient-field module structures. -/
def dualDiagonalBoundaryRestrictionIso :
    (ModuleCat.restrictScalars (algebraMap k (DiagonalChartRing k A S T))).obj
      (dualDiagonalBoundaryModule A S T k) ≅
        ModuleCat.of k (DualDiagonalBoundaryCoefficients A S T k) :=
  (show (ModuleCat.restrictScalars (algebraMap k (DiagonalChartRing k A S T))).obj
      (dualDiagonalBoundaryModule A S T k) ≃ₗ[k]
        DualDiagonalBoundaryCoefficients A S T k from
    { toAddEquiv := AddEquiv.refl _
      map_smul' := fun a v => by
        change (dualDiagonalBoundaryAction A S T k
          (algebraMap k (DiagonalChartRing k A S T) a)) v =
          (algebraMap k (Module.End k (DualDiagonalBoundaryCoefficients A S T k)) a) v
        rw [AlgHom.commutes] }).toModuleIso

end ToricPower.IntegralArrangement

end
