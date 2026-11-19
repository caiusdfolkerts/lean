module

public import TauCeti.LinearAlgebra.CliffordAlgebra.Contraction
public import Mathlib.LinearAlgebra.ExteriorAlgebra.Basic
public import Mathlib.Algebra.Algebra.Operations
public import Mathlib.Tactic.Abel

/-!
# Removing one coordinate in the actual exterior algebra

The algebra map induced by `v ↦ v - c(v)e` equals `x ↦ x - e ∧ (c ⌋ x)`.
This identity is valid over every commutative ring, without freeness or
nondegeneracy assumptions.  It supplies the explicit decomposition needed
to compare a central Lie exterior complex with its Koszul complex.
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace PaperVerification.ExteriorCoordinateProjection

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]

/-- The literal rank-one modification of the identity. -/
def removeCoordinate (e : M) (c : Module.Dual R M) : M →ₗ[R] M :=
  LinearMap.id - (LinearMap.toSpanSingleton R M e).comp c

@[simp] theorem removeCoordinate_apply (e : M) (c : Module.Dual R M) (v : M) :
    removeCoordinate e c v = v - c v • e := rfl

/-- An actual exterior map written using contraction. -/
theorem map_removeCoordinate (e : M) (c : Module.Dual R M)
    (x : ExteriorAlgebra R M) :
    ExteriorAlgebra.map (removeCoordinate e c) x =
      x - ExteriorAlgebra.ι R e *
        CliffordAlgebra.contractLeft (Q := (0 : QuadraticForm R M)) c x := by
  induction x using CliffordAlgebra.left_induction with
  | algebraMap r => simp [CliffordAlgebra.contractLeft_algebraMap]
  | add x y hx hy =>
      simp only [map_add, hx, hy, mul_add]
      abel
  | ι_mul x v hx =>
      change ExteriorAlgebra.map (removeCoordinate e c) (ExteriorAlgebra.ι R v * x) = _
      rw [map_mul, ExteriorAlgebra.map_apply_ι, removeCoordinate_apply, map_sub,
        map_smul, hx, CliffordAlgebra.contractLeft_ι_mul]
      have hswap : ExteriorAlgebra.ι R v * ExteriorAlgebra.ι R e =
          -(ExteriorAlgebra.ι R e * ExteriorAlgebra.ι R v) := by
        exact eq_neg_iff_add_eq_zero.mpr (ExteriorAlgebra.ι_add_mul_swap v e)
      simp only [sub_mul, mul_sub, mul_smul_comm, smul_mul_assoc, ← mul_assoc,
        hswap, ExteriorAlgebra.ι_sq_zero, zero_mul, smul_zero, sub_zero, neg_mul,
        sub_neg_eq_add]
      abel

end PaperVerification.ExteriorCoordinateProjection
