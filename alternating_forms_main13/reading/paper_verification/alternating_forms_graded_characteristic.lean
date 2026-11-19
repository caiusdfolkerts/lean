module

public import PaperVerification.AlternatingFormsGradedDegenerations
public import PaperVerification.AlternatingFormsOddCharacteristicBoundary

/-!
# The graded flat family in the range of Theorem 7.1

The generic coefficient grading requires no characteristic assumption. The
only arithmetic input is the already proved initial-ideal equality. This
file applies it under the exact degree-dependent factorial condition and,
as a consequence, in the printed range `s < 2*p`, including characteristic
two. The one-plane boundary works over every field.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

open MvPolynomial PaperVerification.WeightedInitialFiber

namespace PaperVerification.AlternatingForms

variable {K : Type*} [Field K]

/-- The original odd Rees family is graded and flat whenever the exact
local factorial denominators are invertible. No additional geometric
hypothesis is needed. -/
def oddRichardsonGradedFlatDegeneration_of_degree_factorials
    (k t : ℕ) (hs : t + 2 ≤ k + 1) (hfac : DegreeFactorials K (t + 2)) :
    CoordinateGradedReesDegeneration
      (isotropicPluckerIdeal (K := K) (t := t) (oddPluckerForms k))
      (isotropicPluckerIdeal_isHomogeneous _)
      (pluckerVertexWeight (oddNatVertexWeight k))
      (isotropicPluckerIdeal (t := t) (oddPluckerForms k))
      (intervalPluckerIdeal (oddIntervalLower k (t + 2) hs)
        (oddIntervalUpper k (t + 2) hs)) where
  flat := inferInstance
  specialFiberEquiv := specialFiberEquivOfInitial _ _ _
    (odd_isotropic_initial_eq_interval_of_degree_factorials (K := K) k t hs hfac)
  specialFiber_piece := specialFiberEquivOfInitial_coordinate_piece _ _ _ _ _
  nonzeroFiberEquiv := nonzeroFiberEquiv _ _
  nonzeroFiber_piece := nonzeroFiberEquiv_coordinate_piece _ _ _

/-- The precise positive-characteristic range of Theorem 7.1, strengthened
to include the actual ordinary grading and every fiber isomorphism. -/
def paper_theorem_7_1_graded_flat_family (p k t : ℕ) [Fact p.Prime] [CharP K p]
    (hs : t + 2 ≤ k + 1) (hp : t + 2 < 2 * p) :=
  oddRichardsonGradedFlatDegeneration_of_degree_factorials (K := K) k t hs
    (degreeFactorials_of_lt_twice_characteristic p (t + 2) hp)

/-- Every line, over every field, including ambient dimension one. -/
def oddOnePlaneGradedFlatDegeneration_all_fields (k : ℕ) :
    CoordinateGradedReesDegeneration
      (matrixPluckerIdeal (K := K) (s := 1) (n := 2 * k + 1))
      (matrixPluckerIdeal_isHomogeneous (by decide : 0 < 1))
      (pluckerVertexWeight (oddNatVertexWeight k))
      (matrixPluckerIdeal (s := 1) (n := 2 * k + 1))
      (intervalPluckerIdeal (oddIntervalLower k 1 (by omega))
        (oddIntervalUpper k 1 (by omega))) where
  flat := inferInstance
  specialFiberEquiv := specialFiberEquivOfInitial _ _ _
    (paper_theorem_7_1_initial_ideal_one_plane (K := K) k)
  specialFiber_piece := specialFiberEquivOfInitial_coordinate_piece _ _ _ _ _
  nonzeroFiberEquiv := nonzeroFiberEquiv _ _
  nonzeroFiber_piece := nonzeroFiberEquiv_coordinate_piece _ _ _

end PaperVerification.AlternatingForms
