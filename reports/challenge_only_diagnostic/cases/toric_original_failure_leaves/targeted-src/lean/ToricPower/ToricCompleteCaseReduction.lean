module

public import ToricPower.SmoothFanCompletion
public import ToricPower.SubfanSufficiencyTransfer
public import ToricPower.PrincipalInvariantTransport

/-!
# Reduction of the full sufficiency theorem to complete fans

The smooth divisorial completion is now constructed unconditionally.
The actual boundary-cohomology and coherent-restriction theorems therefore
reduce the general all-large-powers statement to precisely that statement
on complete regular fans in the same lattice. The original arbitrary
Cartier divisor, every rational linear test, and every sufficiently large
positive integer are retained.

The complete-case sufficiency proof remains an explicit input here. This
file removes the former independent completion hypothesis; it does not
claim to replace the categorical complete-case proof.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory TauCeti.Toric

namespace ToricPower

variable {N : Type} {V : Type*} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {i : N →+ V}

variable (completeSufficiency :
  ∀ (extension : Fan i) (regular : extension.IsRegular)
    (nonempty : extension.cones.Nonempty), extension.IsComplete →
    ∀ D : toricCartierDivisor extension nonempty,
      linearCohomologyCriterion extension nonempty D →
      ∃ threshold : ℕ, ∃ positiveThreshold : 0 < threshold,
        ∀ ell : ℕ, ∀ large : threshold ≤ ell,
          toricPowerGeneratesDbCoh extension regular nonempty D ell
            (positiveThreshold.trans_le large))

include completeSufficiency in
theorem toricInvariant_eventual_generation_of_complete_case (fan : Fan i)
    (regular : fan.IsRegular) (nonempty : fan.cones.Nonempty)
    (b : fan.Ray → ℤ)
    (criterion : letI := toricScheme_isIntegral fan nonempty
      linearCohomologyCriterion fan nonempty
        (invariantCartierDivisor fan nonempty.coe_sort regular b)) :
    letI := toricScheme_isIntegral fan nonempty
    ∃ threshold : ℕ, ∃ positiveThreshold : 0 < threshold,
      ∀ ell : ℕ, ∀ large : threshold ≤ ell,
        toricPowerGeneratesDbCoh fan regular nonempty
          (invariantCartierDivisor fan nonempty.coe_sort regular b) ell
          (positiveThreshold.trans_le large) := by
  let completion := FanSubdivision.smoothDivisorialCompletion fan nonempty regular
  have rayFull : IsFullOnRays fan completion.fan :=
    (isFullOnRays_iff_local fan completion.fan).mpr completion.oldRayClosed
  apply subfan_eventual_generation_of_complete_extension fan completion.fan
    completion.contains nonempty completion.regular completion.complete rayFull
    (fun b criterion => completeSufficiency completion.fan completion.regular
      (nonempty.mono completion.contains) completion.complete _ criterion) b criterion

include completeSufficiency in
/-- The exact all-large-integers sufficiency clause for an arbitrary
Cartier divisor follows solely from the same clause on complete fans. -/
theorem toric_eventual_generation_of_complete_case (fan : Fan i)
    (regular : fan.IsRegular) (nonempty : fan.cones.Nonempty)
    (D : toricCartierDivisor fan nonempty)
    (criterion : linearCohomologyCriterion fan nonempty D) :
    ∃ threshold : ℕ, ∃ positiveThreshold : 0 < threshold,
      ∀ ell : ℕ, ∀ large : threshold ≤ ell,
        toricPowerGeneratesDbCoh fan regular nonempty D ell
          (positiveThreshold.trans_le large) := by
  letI := toricScheme_isIntegral fan nonempty
  letI := D.isInvertible_sheaf
  let b := toricLineBundleInvariantCoefficients fan nonempty.coe_sort regular D.sheaf
  let comparison := toricCartierInvariantRepresentativeIso fan regular nonempty D
  have representativeCriterion :=
    (linearCohomologyCriterion_iff_of_sheaf_iso fan nonempty comparison).mp criterion
  obtain ⟨threshold,positiveThreshold,eventual⟩ :=
    toricInvariant_eventual_generation_of_complete_case completeSufficiency
      fan regular nonempty b representativeCriterion
  refine ⟨threshold,positiveThreshold,?_⟩
  intro ell large
  exact (toricPowerGeneratesDbCoh_iff_of_sheaf_iso fan regular nonempty comparison
    ell (positiveThreshold.trans_le large)).mpr (eventual ell large)

end ToricPower
end
