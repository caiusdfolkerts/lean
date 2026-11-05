module
prelude
public import RootedSubsumedForest0722DispositionData

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0722
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness
theorem disposition_at_640 : dispositionTest 640 = true := by decide +kernel

theorem disposition_at_641 : dispositionTest 641 = true := by decide +kernel

theorem disposition_at_642 : dispositionTest 642 = true := by decide +kernel

theorem disposition_at_643 : dispositionTest 643 = true := by decide +kernel

theorem disposition_interval_640 : Interval dispositionTest 640 641 := by
  intro i hlo hhi
  have h : i = 640 := by omega
  subst i
  exact disposition_at_640


theorem disposition_interval_641 : Interval dispositionTest 641 642 := by
  intro i hlo hhi
  have h : i = 641 := by omega
  subst i
  exact disposition_at_641


theorem disposition_interval_642 : Interval dispositionTest 642 643 := by
  intro i hlo hhi
  have h : i = 642 := by omega
  subst i
  exact disposition_at_642


theorem disposition_interval_643 : Interval dispositionTest 643 644 := by
  intro i hlo hhi
  have h : i = 643 := by omega
  subst i
  exact disposition_at_643

end Papers.RationalityTen.RootedForests.RootedSubsumedForest0722
