module

public import ToricPower.SubfanPowerGeneratorRestriction
public import ToricPower.SubfanBoundaryCriterion

/-!
# The complete-to-noncomplete implication with its genuine inputs

For an actual complete regular divisorial extension, the proved boundary
argument and actual coherent restriction transfer the all-large-powers
statement to the original fan. This is a dependency lemma: it does not
assert existence of that extension or the complete-fan generator theorem.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory TauCeti.Toric

namespace ToricPower

variable {N : Type} {V : Type*} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {i : N →+ V} (fan extension : Fan i) (included : fan.cones ⊆ extension.cones)
  (hne : fan.cones.Nonempty) (regular : extension.IsRegular)
  (complete : extension.IsComplete) (rayFull : IsFullOnRays fan extension)

include complete rayFull in
/-- The uniform all-large-integers clause descends from an actual
complete extension, retaining the original line bundle and exponent. -/
theorem subfan_eventual_generation_of_complete_extension
    (completeSufficiency : letI := toricScheme_isIntegral extension (hne.mono included)
      ∀ b : extension.Ray → ℤ,
        linearCohomologyCriterion extension (hne.mono included)
          (invariantCartierDivisor extension (hne.mono included).coe_sort regular b) →
        ∃ threshold : ℕ, ∃ positiveThreshold : 0 < threshold,
          ∀ ell : ℕ, ∀ large : threshold ≤ ell,
            toricPowerGeneratesDbCoh extension regular (hne.mono included)
              (invariantCartierDivisor extension (hne.mono included).coe_sort regular b)
              ell (positiveThreshold.trans_le large))
    (b : fan.Ray → ℤ)
    (criterion : letI := toricScheme_isIntegral fan hne
      linearCohomologyCriterion fan hne (invariantCartierDivisor fan hne.coe_sort
        (subfan_isRegular fan extension included regular) b)) :
    letI := toricScheme_isIntegral fan hne
    ∃ threshold : ℕ, ∃ positiveThreshold : 0 < threshold,
      ∀ ell : ℕ, ∀ large : threshold ≤ ell,
        toricPowerGeneratesDbCoh fan (subfan_isRegular fan extension included regular) hne
          (invariantCartierDivisor fan hne.coe_sort
            (subfan_isRegular fan extension included regular) b)
          ell (positiveThreshold.trans_le large) := by
  letI := toricScheme_isIntegral fan hne
  letI := toricScheme_isIntegral extension (hne.mono included)
  obtain ⟨boundaryBound,boundaryCriterion⟩ := subfanBoundaryCriterion_eventually
    fan extension included hne regular complete rayFull b criterion
  obtain ⟨threshold,positiveThreshold,eventual⟩ := completeSufficiency
    (subfanBoundaryTwist fan extension b boundaryBound)
    (boundaryCriterion boundaryBound le_rfl)
  refine ⟨threshold,positiveThreshold,?_⟩
  intro ell large
  exact subfan_boundary_power_generates fan extension included hne regular rayFull
    b boundaryBound ell (positiveThreshold.trans_le large) (eventual ell large)

end ToricPower

end
