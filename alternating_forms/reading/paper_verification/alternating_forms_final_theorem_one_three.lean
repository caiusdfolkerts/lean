module

public import PaperVerification.AlternatingFormsGradedCharacteristic
public import PaperVerification.AlternatingFormsSectionPrincipal

/-!
# The full Theorem 1.3, with the actual graded flat families

The exterior basis is asserted in every degree. The complete-section-ring
conclusions retain the original coordinate equations, coordinate sections,
quadratic Gröbner basis, and actual graded Tor statement. The additional
fields below give the two explicit graded flat degenerations.

The first degeneration is stated once for rank one and once for rank
`s=t+2`. These disjoint branches exhaust the full positive range and include
`k=0`. The second degeneration is stated uniformly for every positive rank.
Every family type displays its literal ideals, weights, and original
homogeneous grading. No existence of a degeneration is assumed.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

open MvPolynomial PaperVerification.WeightedInitialFiber

namespace PaperVerification.AlternatingForms

universe u
variable {K : Type u} [Field K] [CharZero K]

/-- The complete algebraic statement of Theorem 1.3 with genuine ordinary
gradings on both actual flat families and all their fiber isomorphisms. -/
theorem paper_theorem_1_3_fully_graded (k : ℕ) :
    (∀ s, ∃ B : Module.Basis (GoodOddIndex k s) K
        (OddExteriorQuotientDegree (K := K) k s),
      ∀ I, B I = Submodule.Quotient.mk
        (exteriorPower.ιMulti K s
          (fun i ↦ Pi.basisFun K (Fin (2 * k + 1)) (I.val.val i)))) ∧
    (∀ s (hpos : 0 < s) (hs : s ≤ k + 1),
      OddCompleteSectionConclusions (K := K) k s hs) ∧
    Nonempty (CoordinateGradedReesDegeneration
      (matrixPluckerIdeal (K := K) (s := 1) (n := 2 * k + 1))
      (matrixPluckerIdeal_isHomogeneous (by decide : 0 < 1))
      (pluckerVertexWeight (oddNatVertexWeight k))
      (matrixPluckerIdeal (s := 1) (n := 2 * k + 1))
      (intervalPluckerIdeal (oddIntervalLower k 1 (by omega))
        (oddIntervalUpper k 1 (by omega)))) ∧
    (∀ (t : ℕ) (hs : t + 2 ≤ k + 1),
      Nonempty (CoordinateGradedReesDegeneration
        (isotropicPluckerIdeal (K := K) (t := t) (oddPluckerForms k))
        (isotropicPluckerIdeal_isHomogeneous _)
        (pluckerVertexWeight (oddNatVertexWeight k))
        (isotropicPluckerIdeal (t := t) (oddPluckerForms k))
        (intervalPluckerIdeal (oddIntervalLower k (t + 2) hs)
          (oddIntervalUpper k (t + 2) hs)))) ∧
    (∀ (s : ℕ) (hpos : 0 < s) (hs : s ≤ k + 1),
      Nonempty (CoordinateGradedReesDegeneration
        (Hibi.goodBandIdeal (K := K) (oddIntervalLower k s hs) (oddIntervalUpper k s hs))
        (Hibi.goodBandIdeal_coordinate_homogeneous _ _
          (oddIntervalLower_strictMono k s hs).monotone
          (oddIntervalUpper_strictMono k s hs).monotone hpos)
        (Hibi.diagonalWeight (oddIntervalLower k s hs) (oddIntervalUpper k s hs))
        (intervalPluckerIdeal (oddIntervalLower k s hs) (oddIntervalUpper k s hs))
        (Hibi.relationIdeal (oddIntervalLower k s hs) (oddIntervalUpper k s hs)))) := by
  refine ⟨(paper_theorem_1_3_complete_section_ring (K := K) k).1,
    (paper_theorem_1_3_complete_section_ring (K := K) k).2,
    ⟨onePlaneOddRichardsonGradedFlatDegeneration (K := K) k⟩,
    ?_, ?_⟩
  · intro t hs
    exact ⟨oddRichardsonGradedFlatDegeneration (K := K) k t hs⟩
  · intro s hpos hs
    exact ⟨Hibi.hibiGradedFlatDegeneration (K := K)
      (oddIntervalLower k s hs) (oddIntervalUpper k s hs)
      (oddIntervalLower_strictMono k s hs).monotone
      (oddIntervalUpper_strictMono k s hs).monotone hpos⟩

end PaperVerification.AlternatingForms
