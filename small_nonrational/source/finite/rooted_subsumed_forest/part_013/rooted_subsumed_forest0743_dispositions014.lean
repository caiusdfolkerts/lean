module
prelude
public import RootedSubsumedForest0743DispositionData

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0743
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness
theorem disposition_at_448 : dispositionTest 448 = true := by decide +kernel

theorem disposition_at_449 : dispositionTest 449 = true := by decide +kernel

theorem disposition_at_450 : dispositionTest 450 = true := by decide +kernel

theorem disposition_interval_448 : Interval dispositionTest 448 449 := by
  intro i hlo hhi
  have h : i = 448 := by omega
  subst i
  exact disposition_at_448


theorem disposition_interval_449 : Interval dispositionTest 449 450 := by
  intro i hlo hhi
  have h : i = 449 := by omega
  subst i
  exact disposition_at_449


theorem disposition_interval_450 : Interval dispositionTest 450 451 := by
  intro i hlo hhi
  have h : i = 450 := by omega
  subst i
  exact disposition_at_450

end Papers.RationalityTen.RootedForests.RootedSubsumedForest0743
