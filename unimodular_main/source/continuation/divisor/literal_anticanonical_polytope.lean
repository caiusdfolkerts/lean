module

public import Continuation.Divisor.FanoClosure
public import Continuation.Divisor.ReflectedPolytope

/-!
# The literal anticanonical section polytope

The original geometric presentation uses outward normals. The ordinary
Cartier-section inequalities use the opposite convention. The proved
reflection transport now gives deep monotonicity for the actual section
polytope itself, with its outward primitive normals explicitly identified.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
open scoped Classical

namespace Unimodular.Thomsen

variable {n : ℕ} (F : PaperVerification.ToricGeometry.SmoothCompleteFan n)

/-- The actual all-ones Cartier section polytope, already identified with
the intrinsic anticanonical bundle, has a deeply monotone smooth reflexive
presentation. This is an equality of the actual real polytopes. -/
theorem anticanonical_sectionPolytope_deeplyMonotone
    (h : ConeBases.PositiveCriterion (FanInterfaces.dictionaryToricFan F)) :
    ∃ Q : SmoothReflexivePresentation n,
      Q.carrier = F.fanPolytope (fun _ => (1 : ℝ)) ∧
      Q.DeeplyMonotone ∧ Q.normals = F.rays.image Neg.neg := by
  obtain ⟨P, hnormals, hdeep, hcarrier⟩ := anticanonical_polytope_deeplyMonotone F h
  refine ⟨P.reflected, ?_, P.deeplyMonotone_reflected_iff.mpr hdeep, ?_⟩
  · ext x
    rw [P.mem_reflected_carrier]
    simpa only [neg_neg] using hcarrier (-x)
  · rw [P.reflected_normals, hnormals]

#print axioms anticanonical_sectionPolytope_deeplyMonotone
end Unimodular.Thomsen
