module
prelude
public import RootedSubsumedForest0724DispositionData

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0724
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness
theorem disposition_at_3424 : dispositionTest 3424 = true := by decide +kernel

theorem disposition_at_3425 : dispositionTest 3425 = true := by decide +kernel

theorem disposition_at_3426 : dispositionTest 3426 = true := by decide +kernel

theorem disposition_at_3427 : dispositionTest 3427 = true := by decide +kernel

theorem disposition_interval_3424 : Interval dispositionTest 3424 3425 := by
  intro i hlo hhi
  have h : i = 3424 := by omega
  subst i
  exact disposition_at_3424


theorem disposition_interval_3425 : Interval dispositionTest 3425 3426 := by
  intro i hlo hhi
  have h : i = 3425 := by omega
  subst i
  exact disposition_at_3425


theorem disposition_interval_3426 : Interval dispositionTest 3426 3427 := by
  intro i hlo hhi
  have h : i = 3426 := by omega
  subst i
  exact disposition_at_3426


theorem disposition_interval_3427 : Interval dispositionTest 3427 3428 := by
  intro i hlo hhi
  have h : i = 3427 := by omega
  subst i
  exact disposition_at_3427

end Papers.RationalityTen.RootedForests.RootedSubsumedForest0724
