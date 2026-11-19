module

public import Mathlib.LinearAlgebra.ExteriorPower.Basic

/-!
# Centrality of actual exterior two-forms

The alternating relation in the exterior algebra implies that every homogeneous
two-form commutes with every exterior element, over an arbitrary commutative ring.
This is a direct prerequisite of the main straightening argument, independent of
the later complementary-degree duality development.
-/

@[expose] public section

set_option autoImplicit false

namespace PaperVerification.AlternatingForms

section ExteriorCentrality

variable {K M : Type*} [CommRing K] [AddCommGroup M] [Module K M]

/-- Every exterior two-form is central in the full exterior algebra.  The
proof uses the actual exterior multiplication and its alternating relations. -/
theorem twoForm_commute (f : ⋀[K]^2 M) (x : ExteriorAlgebra K M) :
    Commute (f : ExteriorAlgebra K M) x := by
  have hgenerator (v : M) : Commute (f : ExteriorAlgebra K M) (ExteriorAlgebra.ι K v) := by
    have hf : (f : ExteriorAlgebra K M) ∈
        Submodule.span K (Set.range (ExteriorAlgebra.ιMulti K 2)) := by
      rw [ExteriorAlgebra.ιMulti_span_fixedDegree]
      exact f.property
    refine Submodule.span_induction
      (p := fun y _ => Commute y (ExteriorAlgebra.ι K v)) ?_ ?_ ?_ ?_ hf
    · intro y hy
      rcases hy with ⟨a, rfl⟩
      exact (show Commute (ExteriorAlgebra.ι K v) (ExteriorAlgebra.ιMulti K 2 a) from by
        change ExteriorAlgebra.ι K v * ExteriorAlgebra.ιMulti K 2 a =
          ExteriorAlgebra.ιMulti K 2 a * ExteriorAlgebra.ι K v
        simpa only [pow_two, neg_mul_neg, one_mul, one_smul] using
          (ExteriorAlgebra.ι_mul_ιMulti_anticomm K v a)).symm
    · exact Commute.zero_left _
    · intro a b ha hb iha ihb
      exact iha.add_left ihb
    · intro c a ha iha
      exact iha.smul_left c
  induction x using ExteriorAlgebra.induction with
  | algebraMap r => exact (Algebra.commutes r (f : ExteriorAlgebra K M)).symm
  | ι v => exact hgenerator v
  | mul a b ha hb => exact ha.mul_right hb
  | add a b ha hb => exact ha.add_right hb

end ExteriorCentrality

end PaperVerification.AlternatingForms
