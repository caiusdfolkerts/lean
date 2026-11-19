module

public import ToricPower.ArrangementDerivedMorseSupport
public import ToricPower.ClosedSliceCompletionTests
public import ToricPower.ArrangementDbCohSufficiencyAssembly

/-! # Complete-fan generation using the proved geometric models

The original normalized Morse representative and the original closed-slice
tests are supplied here. The remaining categorical input is full faithfulness
of the actual normalized right adjoint, supplied by reconstruction in the
unconditional paper interface.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TauCeti.Toric
open ToricPower.IntegralArrangement

namespace ToricPower

variable {N : Type} {V : Type*} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {i : N →+ V} (fan : Fan i) [nonempty : Nonempty fan.cones] (regular : fan.IsRegular)
  {n s : ℕ} (basis : Module.Basis (Fin n) ℤ (N →+ ℤ)) (rays : Fin s ≃ fan.Ray)

local notation "hne" => (Set.Nonempty.of_subtype (s := fan.cones))
local instance completeModelsNoetherian : IsNoetherian fan.algebraicRealization :=
  toricScheme_isNoetherian fan
local instance completeModelsIntegral : IsIntegral fan.algebraicRealization :=
  toricScheme_isIntegral fan hne
local instance completeModelsDerivedCoh : HasDerivedCategory.{1} (Coh fan.algebraicRealization) :=
  HasDerivedCategory.standard _
local instance completeModelsDerivedQCoh : HasDerivedCategory.{1} (QCoh fan.algebraicRealization) :=
  HasDerivedCategory.standard _
local instance completeModelsDerivedIncidence : HasDerivedCategory.{1}
    (IncidenceObject (fanArrangementMatrix fan basis rays) ⥤ ModuleCat.{0} ℂ) :=
  HasDerivedCategory.standard _

/-- The paper's literal cohomological criterion supplies all geometric
inputs for every sufficiently large integer exponent. -/
theorem eventual_toric_DbCoh_generation_of_complete_geometric_models
    (complete : fan.IsComplete) (b : fan.Ray → ℤ)
    (fullyFaithful : (arrangementNormalizedDerivedHom fan regular basis rays).FullyFaithful)
    (criterion : linearCohomologyCriterion fan hne
      (invariantCartierDivisor fan nonempty regular b)) :
    ∃ threshold : ℕ, ∃ positiveThreshold : 0 < threshold,
      ∀ ell : ℕ, ∀ large : threshold ≤ ell,
        toricPowerGeneratesDbCoh fan regular hne
          (invariantCartierDivisor fan nonempty regular b)
          ell (positiveThreshold.trans_le large) :=
  eventual_toric_DbCoh_generation_of_actual_models fan regular basis rays complete b
    fullyFaithful
    (fun M => normalizedDerivedMorseModel fan regular basis rays M)
    (fun M => normalizedDerivedMorseModelIso fan regular basis rays M)
    (fun M => normalizedDerivedMorseModel_hasFanLocalMorseSupport fan regular basis rays M)
    (normal_scalar_slice_tests_of_linearCohomology fan regular basis rays complete b criterion)

end ToricPower

end
