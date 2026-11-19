module

public import Continuation.Divisor.PositiveThomsenEquivalence
public import Continuation.Divisor.LiteralAnticanonicalPolytope

/-!
# Proposition 6.3 for the literal anticanonical section polytope

The reflection comparison is composed explicitly with the all-character
ordinary-nef criterion. The conclusion is the actual section polytope,
with its primitive outward normals; it does not identify opposite normal
conventions by notation.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

namespace Unimodular.Thomsen

universe u
variable {n : ℕ} (F : PaperVerification.ToricGeometry.SmoothCompleteFan n)
  (k : Type u) [Field k]

/-- Nefness of every positive Thomsen bundle gives deep monotonicity of
the literal anticanonical section polytope on the same scheme. -/
theorem positiveThomsen_nef_implies_literal_anticanonical_polytope
    (hn : ∀ θ : PaperVerification.ToricGeometry.Lattice n →ₗ[ℤ] ℝ,
      AlgebraicGeometry.IsNef (baseField := k)
        (positiveThomsenLineBundle F k θ).obj) :
    ∃ Q : SmoothReflexivePresentation n,
      Q.carrier = F.fanPolytope (fun _ => (1 : ℝ)) ∧
      Q.DeeplyMonotone ∧ Q.normals = F.rays.image Neg.neg :=
  anticanonical_sectionPolytope_deeplyMonotone F
    ((proposition_6_3_positiveThomsen_iff F k).mp hn)

#print axioms positiveThomsen_nef_implies_literal_anticanonical_polytope
end Unimodular.Thomsen
