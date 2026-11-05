module
prelude
public import RootedSubsumedForest0870DispositionData

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0870
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness
theorem disposition_at_832 : dispositionTest 832 = true := by decide +kernel

theorem disposition_at_833 : dispositionTest 833 = true := by decide +kernel

theorem disposition_at_834 : dispositionTest 834 = true := by decide +kernel

theorem disposition_interval_832 : Interval dispositionTest 832 833 := by
  intro i hlo hhi
  have h : i = 832 := by omega
  subst i
  exact disposition_at_832


theorem disposition_interval_833 : Interval dispositionTest 833 834 := by
  intro i hlo hhi
  have h : i = 833 := by omega
  subst i
  exact disposition_at_833


theorem disposition_interval_834 : Interval dispositionTest 834 835 := by
  intro i hlo hhi
  have h : i = 834 := by omega
  subst i
  exact disposition_at_834

end Papers.RationalityTen.RootedForests.RootedSubsumedForest0870
