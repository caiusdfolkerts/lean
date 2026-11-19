module

public import ToricPower.ToricPowerNecessity
public import ToricPower.ToricFiniteCriterionCohomology
public import ToricPower.ToricPeriodicGeneration
public import ToricPower.PrincipalTransport
public import ToricPower.ToricCompleteCaseReduction

/-!
# The principal theorem and its finite and effective consequences

This file assembles the exact statements of Sections 5--7 in the literal
bounded derived category of coherent sheaves. Proposition 6.2 is unconditional:
its actual sheaf splitting and generator transfer are already proved.

Theorems whose names end in `of_sufficiency` explicitly take the full eventual
sufficiency direction of Theorem 1.1 as input. The necessity direction is the
proved geometric theorem. These assembly lemmas do not claim that the remaining
complete-case sufficiency proof has been supplied. The final reduction explains
precisely how an actual complete-case proof supplies that input on every fan.

The invariant versions retain the given coefficients, ray enumeration, and
character basis. In particular, the final bound in Theorem 7.2 is literally
`periodicityBound A (b ∘ rays)`; no change of invariant representative changes it.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TauCeti.Toric

namespace ToricPower

variable {N : Type} {V : Type*} [AddCommGroup N] [AddCommGroup V]
  [Module ℝ V] {i : N →+ V}

/-- Agreement with the principal predicate for the given invariant divisor.
Both sides are classical generation by the same actual coherent direct image
placed in degree zero in `DbCoh`. -/
theorem toricPowerGeneratesDbCoh_iff_invariantPowerGenerates (fan : Fan i)
    (regular : fan.IsRegular) (hne : fan.cones.Nonempty)
    (b : fan.Ray → ℤ) (ell : ℕ) (positive : 0 < ell) :
    letI := toricScheme_isIntegral fan hne
    toricPowerGeneratesDbCoh fan regular hne
        (invariantCartierDivisor fan hne.coe_sort regular b) ell positive ↔
      toricInvariantPowerGenerates fan hne.coe_sort regular b ell positive := by
  letI := toricScheme_isIntegral fan hne
  rfl

section Effective

variable {κ : Type} [Fintype κ] {s n : ℕ}

/-- **Proposition 6.2, literal principal-category statement.** The exponent is
exactly `R * max K_b C_b` for the given invariant coefficients. This result
does not use the cohomological sufficiency direction of Theorem 1.1. -/
theorem paper_proposition_6_2_DbCoh_invariant (fan : Fan i)
    (regular : fan.IsRegular) (hne : fan.cones.Nonempty)
    (rays : Fin s ≃ fan.Ray) (basis : Module.Basis κ ℤ (N →+ ℤ))
    (coordinates : Fin n ≃ κ) (b : fan.Ray → ℤ) :
    letI := toricScheme_isIntegral fan hne
    toricPowerGeneratesDbCoh fan regular hne
        (invariantCartierDivisor fan hne.coe_sort regular b)
        (stableMultipleExponent
          (enumeratedFanRayMatrix fan rays (basis.reindex coordinates.symm)) (b ∘ rays))
        (stableMultipleExponent_pos _ _) ↔
      ∃ ell : ℕ, ∃ positive : 0 < ell,
        toricPowerGeneratesDbCoh fan regular hne
          (invariantCartierDivisor fan hne.coe_sort regular b) ell positive := by
  letI := toricScheme_isIntegral fan hne
  simpa only [toricPowerGeneratesDbCoh_iff_invariantPowerGenerates] using
    paper_proposition_6_2_generates_invariant fan hne.coe_sort regular
      rays basis coordinates b

/-- **Proposition 6.2 for every Cartier divisor.** Its stable exponent uses the
proved invariant representative of the actual divisor sheaf; no equivariant
structure or invariant-presentation hypothesis is imposed. -/
theorem paper_proposition_6_2_DbCoh_cartier (fan : Fan i)
    (regular : fan.IsRegular) (hne : fan.cones.Nonempty)
    (D : toricCartierDivisor fan hne) :
    letI := toricScheme_isIntegral fan hne
    toricPowerGeneratesDbCoh fan regular hne D
        (toricLineBundleStableExponent fan hne.coe_sort regular D.toInvertibleSheaf)
        (toricLineBundleStableExponent_pos fan hne.coe_sort regular D.toInvertibleSheaf) ↔
      ∃ ell : ℕ, ∃ positive : 0 < ell,
        toricPowerGeneratesDbCoh fan regular hne D ell positive := by
  letI := toricScheme_isIntegral fan hne
  simpa only [toricPowerGeneratesDbCoh_iff_lineBundlePowerGenerates] using
    paper_proposition_6_2_generates_cartier fan hne.coe_sort regular D

/-- The paper's height formula, with the proved uniform choice `T_A = n`.
The empty maximum is zero, so this formula also includes rank and ray count
zero. The positive constant `rayThresholdCoefficient A` depends only on `A`. -/
theorem periodicityBound_eq_paper_formula (A : Matrix (Fin s) (Fin n) ℤ)
    (b : Fin s → ℤ) :
    periodicityBound A b =
      (1 + Finset.univ.sup (fun ray => (b ray).natAbs)) * rayThresholdCoefficient A +
        1 + rayPeriod A * n := rfl

theorem executableStableExponent_pos (A : Matrix (Fin s) (Fin n) ℤ)
    (b : Fin s → ℤ) : 0 < executableStableExponent A b :=
  Nat.mul_pos (universalDenominator_pos A) (periodicityBound_pos A b)

/-- An additional computable version of the one-exponent test. The exponent
`R * N(b)` uses only the certified finite integer computations of `Effectivity`;
its proof avoids extracting the classical witnesses defining `K_b`. This is
stated separately from the paper's exact exponent `R * max K_b C_b`. -/
theorem toricPowerGeneratesDbCoh_executableStableExponent_iff (fan : Fan i)
    (regular : fan.IsRegular) (hne : fan.cones.Nonempty)
    (rays : Fin s ≃ fan.Ray) (basis : Module.Basis κ ℤ (N →+ ℤ))
    (coordinates : Fin n ≃ κ) (b : fan.Ray → ℤ) :
    letI := toricScheme_isIntegral fan hne
    toricPowerGeneratesDbCoh fan regular hne
        (invariantCartierDivisor fan hne.coe_sort regular b)
        (executableStableExponent
          (enumeratedFanRayMatrix fan rays (basis.reindex coordinates.symm)) (b ∘ rays))
        (executableStableExponent_pos _ _) ↔
      ∃ ell : ℕ, ∃ positive : 0 < ell,
        toricPowerGeneratesDbCoh fan regular hne
          (invariantCartierDivisor fan hne.coe_sort regular b) ell positive := by
  letI := toricScheme_isIntegral fan hne
  let A := enumeratedFanRayMatrix fan rays (basis.reindex coordinates.symm)
  have classes :
      frobeniusClasses A (b ∘ rays) (executableStableExponent A (b ∘ rays) : ℤ) =
        frobeniusClasses A (b ∘ rays) (stableMultipleExponent A (b ∘ rays) : ℤ) :=
    (classes_at_executableStableExponent A (b ∘ rays)).trans
      (classes_at_stableMultipleExponent A (b ∘ rays)).symm
  have same := toricInvariantPowerGenerates_iff_of_classes_eq fan hne.coe_sort regular
    rays basis coordinates b b _ _ (executableStableExponent_pos A (b ∘ rays))
      (stableMultipleExponent_pos A (b ∘ rays)) classes
  exact (toricPowerGeneratesDbCoh_iff_invariantPowerGenerates fan regular hne b _ _).trans
    (same.trans ((toricPowerGeneratesDbCoh_iff_invariantPowerGenerates
      fan regular hne b _ _).symm.trans
        (paper_proposition_6_2_DbCoh_invariant fan regular hne rays basis coordinates b)))

/-- Eventual generation and the proved class-set period give generation at
every exponent at least the exact threshold of the given coefficients. -/
theorem toricInvariantPowerGenerates_at_periodicityBound_of_eventually
    (fan : Fan i) (hne : fan.cones.Nonempty) (regular : fan.IsRegular)
    (rays : Fin s ≃ fan.Ray) (basis : Module.Basis κ ℤ (N →+ ℤ))
    (coordinates : Fin n ≃ κ) (b : fan.Ray → ℤ)
    (eventually : ∃ K : ℕ, ∀ (ell : ℕ) (positive : 0 < ell), K ≤ ell →
      toricInvariantPowerGenerates fan hne.coe_sort regular b ell positive)
    (ell : ℕ)
    (large : periodicityBound
      (enumeratedFanRayMatrix fan rays (basis.reindex coordinates.symm)) (b ∘ rays) ≤ ell) :
    toricInvariantPowerGenerates fan hne.coe_sort regular b ell
      ((periodicityBound_pos _ _).trans_le large) := by
  obtain ⟨K, eventual⟩ := eventually
  let A := enumeratedFanRayMatrix fan rays (basis.reindex coordinates.symm)
  have periodPositive := rayPeriod_pos A
  have beyond : K ≤ ell + K * rayPeriod A := by nlinarith
  exact (toricInvariantPowerGenerates_add_period_mul fan hne.coe_sort regular
    rays basis coordinates b ell large K).mp
      (eventual _ (Nat.add_pos_left ((periodicityBound_pos _ _).trans_le large) _) beyond)

end Effective

section FromSufficiency

variable (fan : Fan i) (regular : fan.IsRegular) (hne : fan.cones.Nonempty)

/- The full sufficiency input retains every actual Cartier divisor, every
rational linear test in the original criterion, and all sufficiently large
positive integers. It is an explicit argument of the following lemmas. -/
variable (sufficiency : ∀ D : toricCartierDivisor fan hne,
  linearCohomologyCriterion fan hne D →
    ∃ threshold : ℕ, ∃ positiveThreshold : 0 < threshold,
      ∀ ell : ℕ, ∀ large : threshold ≤ ell,
        toricPowerGeneratesDbCoh fan regular hne D ell
          (positiveThreshold.trans_le large))

include sufficiency in
/-- The existence equivalence uses the proved necessity direction and the
explicit all-large-integers sufficiency input. -/
theorem toricPowerGeneratesDbCoh_exists_iff_of_sufficiency
    (D : toricCartierDivisor fan hne) :
    (∃ ell : ℕ, ∃ positive : 0 < ell,
      toricPowerGeneratesDbCoh fan regular hne D ell positive) ↔
      linearCohomologyCriterion fan hne D := by
  constructor
  · rintro ⟨ell, positive, generates⟩
    exact paper_theorem_1_1_necessity fan regular hne D ell positive generates
  · intro criterion
    obtain ⟨threshold, positive, eventual⟩ := sufficiency D criterion
    exact ⟨threshold, positive, eventual threshold le_rfl⟩

include sufficiency in
/-- Assembly of both clauses of the exact principal proposition. The name
records that the sufficiency proof remains an argument. -/
theorem principalTheoremDbCohClaim_of_sufficiency (D : toricCartierDivisor fan hne) :
    principalTheoremDbCohClaim fan regular hne D :=
  ⟨toricPowerGeneratesDbCoh_exists_iff_of_sufficiency fan regular hne sufficiency D,
    sufficiency D⟩

include sufficiency in
/-- **Theorem 5.2, for the given invariant divisor.** The right side is exactly
the finite set of retained ray spans, the finite negative-ray subsets with
nonzero augmented reduced cohomology, and their unrestricted integral character
feasibility inequalities. In degree zero the augmented convention retains the
paper's reduced degree `-1`. -/
theorem paper_theorem_5_2_of_sufficiency (b : fan.Ray → ℤ) :
    letI := toricScheme_isIntegral fan hne
    (∃ ell : ℕ, ∃ positive : 0 < ell,
      toricPowerGeneratesDbCoh fan regular hne
        (invariantCartierDivisor fan hne.coe_sort regular b) ell positive) ↔
      ∀ W ∈ rayGeneratedLinearTests fan,
        toricFiniteCohomologyPatternCriterion (restrictedFan fan W.space W.rational)
          (restrictedFanRayCoefficients fan W.space W.rational b) := by
  letI := toricScheme_isIntegral fan hne
  exact (toricPowerGeneratesDbCoh_exists_iff_of_sufficiency fan regular hne sufficiency
    (invariantCartierDivisor fan hne.coe_sort regular b)).trans
      (linearCohomologyCriterion_invariant_iff_finitePattern fan hne regular b)

include sufficiency in
/-- The finite-generation criterion for every actual Cartier divisor, using
the proved invariant representative of its associated line bundle. -/
theorem paper_theorem_5_2_cartier_of_sufficiency (D : toricCartierDivisor fan hne) :
    letI := toricDivisorSheaf_invertible fan hne D
    (∃ ell : ℕ, ∃ positive : 0 < ell,
      toricPowerGeneratesDbCoh fan regular hne D ell positive) ↔
      ∀ W ∈ rayGeneratedLinearTests fan,
        toricFiniteCohomologyPatternCriterion (restrictedFan fan W.space W.rational)
          (restrictedFanRayCoefficients fan W.space W.rational
            (toricLineBundleInvariantCoefficients fan hne.coe_sort regular
              (toricDivisorSheaf fan hne D))) := by
  letI := toricDivisorSheaf_invertible fan hne D
  exact (toricPowerGeneratesDbCoh_exists_iff_of_sufficiency fan regular hne sufficiency
    D).trans (linearCohomologyCriterion_cartier_iff_finitePattern fan hne regular D)

include sufficiency in
/-- The explicit threshold also applies to every actual Cartier divisor,
using the constructed invariant representative of its genuine line bundle.
The given-coefficient version below keeps the sharper statement with its
specified coefficient vector and coordinates. -/
theorem paper_theorem_7_2_cartier_generation_of_sufficiency
    (D : toricCartierDivisor fan hne)
    (criterion : linearCohomologyCriterion fan hne D) (ell : ℕ)
    (large : letI := toricScheme_isIntegral fan hne
      toricLineBundlePeriodicityBound fan hne.coe_sort regular D.toInvertibleSheaf ≤ ell) :
    letI := toricScheme_isIntegral fan hne
    toricPowerGeneratesDbCoh fan regular hne D ell
      ((toricLineBundlePeriodicityBound_pos fan hne.coe_sort regular
        D.toInvertibleSheaf).trans_le large) := by
  letI := toricScheme_isIntegral fan hne
  obtain ⟨threshold, positiveThreshold, eventual⟩ := sufficiency D criterion
  apply (toricPowerGeneratesDbCoh_iff_lineBundlePowerGenerates fan regular hne D ell _).mpr
  apply toricLineBundlePowerGenerates_at_periodicityBound_of_eventually
    fan hne.coe_sort regular D.toInvertibleSheaf _ ell large
  refine ⟨threshold, fun power positive beyond => ?_⟩
  exact (toricPowerGeneratesDbCoh_iff_lineBundlePowerGenerates fan regular hne D power
    positive).mp (eventual power beyond)

variable {κ : Type} [Fintype κ] {s n : ℕ}

include sufficiency in
/-- **Theorem 7.2, the final generation clause.** Every integer exponent at
least the explicit bound for the original coefficient vector generates once
the full linear cohomological criterion holds. The proof uses the actual
coherent residue decomposition and exact periodicity, not a bounded search. -/
theorem paper_theorem_7_2_generation_of_sufficiency
    (rays : Fin s ≃ fan.Ray) (basis : Module.Basis κ ℤ (N →+ ℤ))
    (coordinates : Fin n ≃ κ) (b : fan.Ray → ℤ)
    (criterion : letI := toricScheme_isIntegral fan hne
      linearCohomologyCriterion fan hne
        (invariantCartierDivisor fan hne.coe_sort regular b))
    (ell : ℕ)
    (large : periodicityBound
      (enumeratedFanRayMatrix fan rays (basis.reindex coordinates.symm)) (b ∘ rays) ≤ ell) :
    letI := toricScheme_isIntegral fan hne
    toricPowerGeneratesDbCoh fan regular hne
      (invariantCartierDivisor fan hne.coe_sort regular b) ell
      ((periodicityBound_pos _ _).trans_le large) := by
  letI := toricScheme_isIntegral fan hne
  obtain ⟨threshold, positiveThreshold, eventual⟩ :=
    sufficiency (invariantCartierDivisor fan hne.coe_sort regular b) criterion
  apply (toricPowerGeneratesDbCoh_iff_invariantPowerGenerates fan regular hne
    b ell _).mpr
  apply toricInvariantPowerGenerates_at_periodicityBound_of_eventually
    fan hne regular rays basis coordinates b _ ell large
  refine ⟨threshold, fun power positive beyond => ?_⟩
  exact (toricPowerGeneratesDbCoh_iff_invariantPowerGenerates fan regular hne
    b power positive).mp (eventual power beyond)

include sufficiency in
/-- **Theorem 7.2, both literal conclusions.** Raw coefficient sets are periodic
without any cohomological assumption. The additional criterion implies actual
`DbCoh` generation at every exponent beyond the same explicit bound. -/
theorem paper_theorem_7_2_of_sufficiency
    (rays : Fin s ≃ fan.Ray) (basis : Module.Basis κ ℤ (N →+ ℤ))
    (coordinates : Fin n ≃ κ) (b : fan.Ray → ℤ) (ell : ℕ)
    (large : periodicityBound
      (enumeratedFanRayMatrix fan rays (basis.reindex coordinates.symm)) (b ∘ rays) ≤ ell) :
    let A := enumeratedFanRayMatrix fan rays (basis.reindex coordinates.symm)
    letI := toricScheme_isIntegral fan hne
    rawCoefficients A (b ∘ rays) ((ell + rayPeriod A : ℕ) : ℤ) =
        rawCoefficients A (b ∘ rays) (ell : ℤ) ∧
      (linearCohomologyCriterion fan hne
          (invariantCartierDivisor fan hne.coe_sort regular b) →
        toricPowerGeneratesDbCoh fan regular hne
          (invariantCartierDivisor fan hne.coe_sort regular b) ell
          ((periodicityBound_pos _ _).trans_le large)) := by
  letI := toricScheme_isIntegral fan hne
  exact ⟨paper_theorem_7_2_raw _ _ ell large,
    fun criterion => paper_theorem_7_2_generation_of_sufficiency fan regular hne sufficiency
      rays basis coordinates b criterion ell large⟩

end FromSufficiency

/-- Actual smooth divisorial completion and the proved noncomplete transfer
reduce the entire principal proposition to precisely the eventual sufficiency
statement on complete fans. No completion existence hypothesis remains. -/
theorem principalTheoremDbCohClaim_of_complete_case
    (completeSufficiency :
      ∀ (extension : Fan i) (regular : extension.IsRegular)
        (nonempty : extension.cones.Nonempty), extension.IsComplete →
        ∀ D : toricCartierDivisor extension nonempty,
          linearCohomologyCriterion extension nonempty D →
          ∃ threshold : ℕ, ∃ positiveThreshold : 0 < threshold,
            ∀ ell : ℕ, ∀ large : threshold ≤ ell,
              toricPowerGeneratesDbCoh extension regular nonempty D ell
                (positiveThreshold.trans_le large))
    (fan : Fan i) (regular : fan.IsRegular) (hne : fan.cones.Nonempty)
    (D : toricCartierDivisor fan hne) :
    principalTheoremDbCohClaim fan regular hne D :=
  principalTheoremDbCohClaim_of_sufficiency fan regular hne
    (toric_eventual_generation_of_complete_case completeSufficiency fan regular hne) D

end ToricPower
end
