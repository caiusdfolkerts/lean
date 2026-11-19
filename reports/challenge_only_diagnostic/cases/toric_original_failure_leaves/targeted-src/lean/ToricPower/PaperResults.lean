module

public import ToricPower.ReconstructionCompletionFullFaithfulness
public import ToricPower.ArrangementCompleteActualModels
public import ToricPower.PrincipalTheoremConsequences

/-!
# Principal results of Frobenius generators for smooth toric varieties

The geometric reconstruction, actual Morse model, and actual closed-slice
comparison supply the complete-fan argument. Smooth divisorial completion
and isomorphism invariance then retain every Cartier divisor on every
nonempty smooth finite fan. All eventual statements concern every large
integer, and generation is in the literal bounded coherent category.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory TauCeti.Toric

namespace ToricPower

variable {N : Type} {V : Type*} [AddCommGroup N] [AddCommGroup V]
  [Module ℝ V] {i : N →+ V}

/-- Complete-case sufficiency for an invariant divisor, with all
geometric and categorical inputs supplied by the actual constructions. -/
theorem toric_complete_invariant_eventual_generation (fan : Fan i)
    (regular : fan.IsRegular) (hne : fan.cones.Nonempty)
    (complete : fan.IsComplete) (b : fan.Ray → ℤ)
    (criterion : letI := toricScheme_isIntegral fan hne
      linearCohomologyCriterion fan hne
        (invariantCartierDivisor fan hne.coe_sort regular b)) :
    letI := toricScheme_isIntegral fan hne
    ∃ threshold : ℕ, ∃ positiveThreshold : 0 < threshold,
      ∀ ell : ℕ, ∀ large : threshold ≤ ell,
        toricPowerGeneratesDbCoh fan regular hne
          (invariantCartierDivisor fan hne.coe_sort regular b) ell
          (positiveThreshold.trans_le large) := by
  classical
  letI : Nonempty fan.cones := hne.coe_sort
  letI := toricScheme_isIntegral fan hne
  letI := Fintype.ofFinite fan.Ray
  let basis := latticeCharacterBasis fan.lattice
  let rays : Fin (Fintype.card fan.Ray) ≃ fan.Ray := (Fintype.equivFin fan.Ray).symm
  exact eventual_toric_DbCoh_generation_of_complete_geometric_models fan regular basis rays complete b
    (arrangementNormalizedDerivedHom_fullyFaithful fan regular basis rays)
    criterion

/-- Complete-case sufficiency for an arbitrary Cartier divisor. Its
invariant representative is constructed from the actual line bundle. -/
theorem toric_complete_cartier_eventual_generation (fan : Fan i)
    (regular : fan.IsRegular) (hne : fan.cones.Nonempty)
    (complete : fan.IsComplete) (D : toricCartierDivisor fan hne)
    (criterion : linearCohomologyCriterion fan hne D) :
    ∃ threshold : ℕ, ∃ positiveThreshold : 0 < threshold,
      ∀ ell : ℕ, ∀ large : threshold ≤ ell,
        toricPowerGeneratesDbCoh fan regular hne D ell
          (positiveThreshold.trans_le large) := by
  letI := toricScheme_isIntegral fan hne
  letI := D.isInvertible_sheaf
  let b := toricLineBundleInvariantCoefficients fan hne.coe_sort regular D.sheaf
  let comparison := toricCartierInvariantRepresentativeIso fan regular hne D
  have representativeCriterion :=
    (linearCohomologyCriterion_iff_of_sheaf_iso fan hne comparison).mp criterion
  obtain ⟨threshold,positiveThreshold,eventual⟩ :=
    toric_complete_invariant_eventual_generation fan regular hne complete b representativeCriterion
  refine ⟨threshold,positiveThreshold,?_⟩
  intro ell large
  exact (toricPowerGeneratesDbCoh_iff_of_sheaf_iso fan regular hne comparison
    ell (positiveThreshold.trans_le large)).mpr (eventual ell large)

/-- **Theorem 1.1, sufficiency.** Every sufficiently large positive
integer power generates, for every Cartier divisor on every smooth fan. -/
theorem paper_theorem_1_1_sufficiency (fan : Fan i)
    (regular : fan.IsRegular) (hne : fan.cones.Nonempty)
    (D : toricCartierDivisor fan hne)
    (criterion : linearCohomologyCriterion fan hne D) :
    ∃ threshold : ℕ, ∃ positiveThreshold : 0 < threshold,
      ∀ ell : ℕ, ∀ large : threshold ≤ ell,
        toricPowerGeneratesDbCoh fan regular hne D ell
          (positiveThreshold.trans_le large) :=
  toric_eventual_generation_of_complete_case
    (fun extension regular nonempty complete D criterion =>
      toric_complete_cartier_eventual_generation extension regular nonempty complete D criterion)
    fan regular hne D criterion

/-- **Theorem 1.1.** The existence equivalence and the all-large-integers
clause in the literal bounded derived category of coherent sheaves. -/
theorem paper_theorem_1_1 (fan : Fan i)
    (regular : fan.IsRegular) (hne : fan.cones.Nonempty)
    (D : toricCartierDivisor fan hne) :
    principalTheoremDbCohClaim fan regular hne D :=
  principalTheoremDbCohClaim_of_sufficiency fan regular hne
    (paper_theorem_1_1_sufficiency fan regular hne) D

/-- **Theorem 5.2.** The exact finite ray-span and integral-character
criterion, with the given invariant divisor coefficients. -/
theorem paper_theorem_5_2 (fan : Fan i)
    (regular : fan.IsRegular) (hne : fan.cones.Nonempty) (b : fan.Ray → ℤ) :
    letI := toricScheme_isIntegral fan hne
    (∃ ell : ℕ, ∃ positive : 0 < ell,
      toricPowerGeneratesDbCoh fan regular hne
        (invariantCartierDivisor fan hne.coe_sort regular b) ell positive) ↔
      ∀ W ∈ rayGeneratedLinearTests fan,
        toricFiniteCohomologyPatternCriterion (restrictedFan fan W.space W.rational)
          (restrictedFanRayCoefficients fan W.space W.rational b) :=
  paper_theorem_5_2_of_sufficiency fan regular hne
    (paper_theorem_1_1_sufficiency fan regular hne) b

/-- The same finite generation criterion for every actual Cartier
divisor, using its constructed invariant representative. -/
theorem paper_theorem_5_2_cartier (fan : Fan i)
    (regular : fan.IsRegular) (hne : fan.cones.Nonempty)
    (D : toricCartierDivisor fan hne) :
    letI := toricDivisorSheaf_invertible fan hne D
    (∃ ell : ℕ, ∃ positive : 0 < ell,
      toricPowerGeneratesDbCoh fan regular hne D ell positive) ↔
      ∀ W ∈ rayGeneratedLinearTests fan,
        toricFiniteCohomologyPatternCriterion (restrictedFan fan W.space W.rational)
          (restrictedFanRayCoefficients fan W.space W.rational
            (toricLineBundleInvariantCoefficients fan hne.coe_sort regular
              (toricDivisorSheaf fan hne D))) :=
  paper_theorem_5_2_cartier_of_sufficiency fan regular hne
    (paper_theorem_1_1_sufficiency fan regular hne) D

/-- **Theorem 7.2, arbitrary Cartier divisor.** The explicit bound of its
constructed representative suffices for every integer exponent. -/
theorem paper_theorem_7_2_cartier_generation (fan : Fan i)
    (regular : fan.IsRegular) (hne : fan.cones.Nonempty)
    (D : toricCartierDivisor fan hne)
    (criterion : linearCohomologyCriterion fan hne D) (ell : ℕ)
    (large : letI := toricScheme_isIntegral fan hne
      toricLineBundlePeriodicityBound fan hne.coe_sort regular D.toInvertibleSheaf ≤ ell) :
    letI := toricScheme_isIntegral fan hne
    toricPowerGeneratesDbCoh fan regular hne D ell
      ((toricLineBundlePeriodicityBound_pos fan hne.coe_sort regular
        D.toInvertibleSheaf).trans_le large) :=
  paper_theorem_7_2_cartier_generation_of_sufficiency fan regular hne
    (paper_theorem_1_1_sufficiency fan regular hne) D criterion ell large

/-- **Theorem 7.2, both conclusions.** The raw coefficient sets are
periodic at the exact height-linear bound for the original coefficients,
and the cohomological criterion gives actual generation at that bound. -/
theorem paper_theorem_7_2 (fan : Fan i)
    (regular : fan.IsRegular) (hne : fan.cones.Nonempty)
    {κ : Type} [Fintype κ] {s n : ℕ}
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
          ((periodicityBound_pos _ _).trans_le large)) :=
  paper_theorem_7_2_of_sufficiency fan regular hne
    (paper_theorem_1_1_sufficiency fan regular hne) rays basis coordinates b ell large

end ToricPower

end
