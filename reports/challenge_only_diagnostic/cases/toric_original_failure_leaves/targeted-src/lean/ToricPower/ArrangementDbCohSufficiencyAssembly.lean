module

public import ToricPower.ArrangementDbCohDetection
public import ToricPower.ToricPowerDerivedObject
public import ToricPower.ArrangementLeftDetectionAssembly

/-!
# The literal eventual-generation conclusion from the geometric models

This assembly discharges every categorical generation step using the
proved actual inverse-Serre bridge. Its remaining inputs are the actual
reconstruction, normalized Morse model, and closed-slice tests. These
geometric inputs remain explicit until their separate constructions
are supplied; this dependency lemma is not itself the principal theorem.
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
local instance dbAssemblyNoetherian : IsNoetherian fan.algebraicRealization := toricScheme_isNoetherian fan
local instance dbAssemblyIntegral : IsIntegral fan.algebraicRealization := toricScheme_isIntegral fan hne
local instance dbAssemblyDerivedCoh : HasDerivedCategory.{1} (Coh fan.algebraicRealization) := HasDerivedCategory.standard _
local instance dbAssemblyDerivedQCoh : HasDerivedCategory.{1} (QCoh fan.algebraicRealization) := HasDerivedCategory.standard _
local instance dbAssemblyDerivedIncidence : HasDerivedCategory.{1}
    (IncidenceObject (fanArrangementMatrix fan basis rays) ⥤ ModuleCat.{0} ℂ) :=
  HasDerivedCategory.standard _

/-- Every sufficiently large integer power generates the original
bounded coherent category once the actual geometric models and tests
have been established. The threshold is independent of the tested object. -/
theorem eventual_toric_DbCoh_generation_of_actual_models
    (complete : fan.IsComplete) (b : fan.Ray → ℤ)
    (fullyFaithful : (arrangementNormalizedDerivedHom fan regular basis rays).FullyFaithful)
    (model : DerivedQCoh fan.algebraicRealization →
      CochainComplex (IncidenceObject (fanArrangementMatrix fan basis rays) ⥤ ModuleCat.{0} ℂ) ℤ)
    (factors : ∀ M, (arrangementNormalizedDerivedHom fan regular basis rays).obj M ≅
      DerivedCategory.Q.obj (model M))
    (morse : ∀ M, HasFanLocalMorseSupport fan regular basis rays
      (universalPeriodicComplex (fanArrangementMatrix fan basis rays) ℂ (model M)))
    (tests : ∀ c : NormalCoveredNormalizedCell fan regular basis rays,
      ∃ m : Fin n → ℤ, NormalizedScalarSliceTest fan regular basis rays b c m) :
    ∃ threshold : ℕ, ∃ positiveThreshold : 0 < threshold,
      ∀ ell : ℕ, ∀ large : threshold ≤ ell,
        toricPowerGeneratesDbCoh fan regular hne
          (invariantCartierDivisor fan nonempty regular b)
          ell (positiveThreshold.trans_le large) := by
  obtain ⟨threshold,positiveThreshold,detect⟩ := eventual_toric_left_detection_of_actual_models
    fan regular basis rays complete b fullyFaithful model factors morse tests
  refine ⟨threshold,positiveThreshold,?_⟩
  intro ell large
  let positive := positiveThreshold.trans_le large
  letI := toricPowerMap_finite fan regular ell positive
  let G := toricDbPowerObject fan regular hne
    (invariantCartierDivisor fan nonempty regular b) ell positive
  apply arrangementDbCoh_generator_of_targetDetection fan regular basis rays complete fullyFaithful G
  intro Y nonzero
  obtain ⟨q,f,hf⟩ := detect ell large Y nonzero
  let comparison := (shiftFunctor (DerivedQCoh fan.algebraicRealization) q).mapIso
    (toricDbPowerInvariantQuasicoherentIso fan regular hne b ell positive).symm
  refine ⟨q,f ≫ comparison.hom,?_⟩
  intro zero
  apply hf
  exact (cancel_mono comparison.hom).mp (by simpa only [zero_comp] using zero)

end ToricPower

end
