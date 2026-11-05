module

public import Continuation.Divisor.NormalizedWallDegrees
public import Continuation.Divisor.FanoClosure

/-!
# The literal normalized wall relations in Proposition 6.3

The vectors are the outside ray followed by the original full-cone basis.
The outside coefficient is one, the other outside coefficient is proved
one, the vector relation is proved, and normalization determines every
coefficient uniquely. Thus negative mass is computed on the actual relation,
not on a newly stipulated inequality with the same name.
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical BigOperators

namespace PaperVerification.ToricGeometry.SmoothCompleteFan

variable {n : ℕ} (F : SmoothCompleteFan n)

/-- For each normalized relation, its negative mass bound is equivalent to
nonnegativity of the actual rounded wall slack for every real character. -/
theorem normalizedWall_negativeMass_iff_roundedSlack (s : F.fullCones) (w : Lattice n) :
    (∑ i, max (-(F.normalizedWallCoefficients s w i)) 0) ≤ 1 ↔
      ∀ θ : Lattice n →ₗ[ℤ] ℝ,
        0 ≤ F.integerWallSlack (Unimodular.Thomsen.positiveCoefficients θ) s w := by
  rw [F.normalizedWall_negativeMass]
  constructor
  · intro hm θ
    have h := (Unimodular.Rounding.rounded_basis_inequality_iff
      (F.fullConeBasis s) w).mpr hm θ
    rw [F.integerWallSlack_eq_normalizedRelation]
    simp only [normalizedWallCoefficients, normalizedWallVectors, Fin.sum_univ_succ,
      Fin.cons_zero, Fin.cons_succ, Unimodular.Thomsen.positiveCoefficients,
      one_mul, neg_mul, Finset.sum_neg_distrib]
    omega
  · intro hs
    apply (Unimodular.Rounding.rounded_basis_inequality_iff (F.fullConeBasis s) w).mp
    intro θ
    have h := hs θ
    rw [F.integerWallSlack_eq_normalizedRelation] at h
    simp only [normalizedWallCoefficients, normalizedWallVectors, Fin.sum_univ_succ,
      Fin.cons_zero, Fin.cons_succ, Unimodular.Thomsen.positiveCoefficients,
      one_mul, neg_mul, Finset.sum_neg_distrib] at h
    omega

/-- Every actual wall relation, allowing any presented normalized coefficient
family, has total negative mass at most one. -/
def AllNormalizedWallsNegativeMass : Prop :=
  ∀ (s t : F.fullCones) (j : Fin n) (w : Lattice n),
    t.val = insert w ((F.wallIndices s j).image (F.fullConeBasis s)) →
    (F.fullConeBasis s).repr w j = -1 →
    ∀ c : Fin (n+1) → ℤ, c 0 = 1 →
      (∑ i, c i • F.normalizedWallVectors s w i = 0) →
      (∑ i, max (-c i) 0) ≤ 1

/-- The normalized-wall condition and the full positive-coordinate condition
are equivalent on every complete smooth fan, without assuming projectivity. -/
theorem normalizedWallCriterion_iff_positiveCriterion :
    F.AllNormalizedWallsNegativeMass ↔
      Unimodular.ConeBases.PositiveCriterion (Unimodular.FanInterfaces.dictionaryToricFan F) := by
  constructor
  · intro hw
    apply (Unimodular.Thomsen.positiveThomsen_convexSupport_iff_intrinsic F).mp
    intro θ
    apply F.isNef_of_integerWallSlack_nonneg
    intro s t j w ht hj
    exact (F.normalizedWall_negativeMass_iff_roundedSlack s w).mp
      (hw s t j w ht hj _ rfl (F.normalizedWallRelation s w)) θ
  · intro hc s t j w ht hj c hc0 hrel
    rw [F.normalizedWallRelation_unique s w c hc0 hrel,
      F.normalizedWall_negativeMass]
    apply ((Unimodular.FanInterfaces.dictionaryPositiveCriterion_iff F).mp hc) s w
    apply F.ray_mem_of_mem_cone (F.fullCones_mem t)
    rw [ht]
    exact Finset.mem_insert_self _ _

#print axioms normalizedWallRelation_unique
#print axioms normalizedWall_negativeMass
#print axioms normalizedWallCriterion_iff_positiveCriterion

end PaperVerification.ToricGeometry.SmoothCompleteFan
