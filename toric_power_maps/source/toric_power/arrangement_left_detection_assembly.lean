module

public import ToricPower.ArrangementUniformDetection
public import ToricPower.ArrangementPowerSheafDetection

/-!
# The complete-fan detection assembly on the actual quasicoherent category

This theorem isolates the precise geometric inputs: reconstruction,
the actual normalized right-adjoint model and its Morse support, and
nonzero tests on the genuine affine slices. Its conclusion concerns
every nonzero unbounded quasicoherent object and every sufficiently
large integer power. The input proofs must be supplied separately;
this assembly theorem is not itself Theorem 1.1.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TauCeti.Toric
open ToricPower.IntegralArrangement

namespace ToricPower

variable {N : Type} {V : Type*} [AddCommGroup N] [AddCommGroup V]
  [Module ℝ V] {i : N →+ V} (fan : Fan i)
  [nonempty : Nonempty fan.cones] (regular : fan.IsRegular)
  {n s : ℕ} (basis : Module.Basis (Fin n) ℤ (N →+ ℤ)) (rays : Fin s ≃ fan.Ray)

local notation "A" => fanArrangementMatrix fan basis rays

local instance leftDetectionAssemblyDerivedQCoh :
    HasDerivedCategory.{1} (QCoh fan.algebraicRealization) := HasDerivedCategory.standard _
local instance leftDetectionAssemblyDerivedCells :
    HasDerivedCategory.{1} (IncidenceObject A ⥤ ModuleCat.{0} ℂ) :=
  HasDerivedCategory.standard _

/-- The final detection statement is about the genuine finite toric
pushforward, and its source is any nonzero unbounded quasicoherent object. -/
theorem eventual_toric_left_detection_of_actual_models
    (complete : fan.IsComplete) (b : fan.Ray → ℤ)
    (fullyFaithful : (arrangementNormalizedDerivedHom fan regular basis rays).FullyFaithful)
    (model : DerivedCategory (QCoh fan.algebraicRealization) →
      CochainComplex (IncidenceObject A ⥤ ModuleCat.{0} ℂ) ℤ)
    (factors : ∀ M, (arrangementNormalizedDerivedHom fan regular basis rays).obj M ≅
      DerivedCategory.Q.obj (model M))
    (morse : ∀ M, HasFanLocalMorseSupport fan regular basis rays
      (universalPeriodicComplex A ℂ (model M)))
    (tests : ∀ c : NormalCoveredNormalizedCell fan regular basis rays,
      ∃ m : Fin n → ℤ, NormalizedScalarSliceTest fan regular basis rays b c m) :
    ∃ threshold : ℕ, ∃ positiveThreshold : 0 < threshold,
      ∀ ell : ℕ, ∀ large : threshold ≤ ell,
        letI := toricPowerMap_finite fan regular ell (positiveThreshold.trans_le large)
        ∀ M : DerivedCategory (QCoh fan.algebraicRealization), ¬ IsZero M →
          ∃ q : ℤ, ∃ f : M ⟶
            (((quasicoherentAffinePushforward (toricPowerMap fan ell)).mapDerivedCategory).obj
              ((DerivedCategory.singleFunctor (QCoh fan.algebraicRealization) 0).obj
                (arrangementCartierCoefficient fan regular b)))⟦q⟧, f ≠ 0 := by
  let B := arrangementNormalizedDerivedHom fan regular basis rays
  letI : B.Faithful := fullyFaithful.faithful
  obtain ⟨threshold,positiveThreshold,detect⟩ := eventual_diagram_detection_of_slice_tests
    fan regular basis rays complete b tests
  refine ⟨threshold,positiveThreshold,?_⟩
  intro ell large
  letI := toricPowerMap_finite fan regular ell (positiveThreshold.trans_le large)
  intro M nonzero
  have nonacyclic : ¬ (model M).Acyclic := by
    intro acyclic
    have zeroB : IsZero (B.obj M) := (factors M).isZero_iff.mpr
      (derivedComplex_isZero_of_acyclic (model M) acyclic)
    apply nonzero
    apply (IsZero.iff_id_eq_zero M).mpr
    apply B.map_injective
    simpa only [B.map_id,B.map_zero] using (IsZero.iff_id_eq_zero (B.obj M)).mp zeroB
  obtain ⟨positive,q,f,hf⟩ := detect ell large (model M) nonacyclic (morse M)
  let source := (powerDerivedPushdown A ell positive ℂ).mapIso (factors M)
  have nonzeroDiagram : source.hom ≫ f ≠ 0 := by
    intro zero
    apply hf
    rw [← cancel_epi source.hom,comp_zero]
    exact zero
  obtain ⟨g,hg⟩ := exists_nonzero_toric_power_pushforward_of_diagram
    fan regular basis rays fullyFaithful ell positive M
    ((DerivedCategory.singleFunctor (QCoh fan.algebraicRealization) 0).obj
      (arrangementCartierCoefficient fan regular b)) q (source.hom ≫ f) nonzeroDiagram
  exact ⟨q,g,hg⟩

end ToricPower

end
