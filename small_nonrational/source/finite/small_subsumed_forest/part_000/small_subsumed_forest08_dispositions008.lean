module
prelude
public import SmallSubsumedForest08DispositionData

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.SmallRawForests.SmallSubsumedForest08
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness
theorem disposition_at_256 : dispositionTest 256 = true := by decide +kernel

theorem disposition_interval_256 : Interval dispositionTest 256 257 := by
  intro i hlo hhi
  have h : i = 256 := by omega
  subst i
  exact disposition_at_256

end Papers.RationalityTen.SmallRawForests.SmallSubsumedForest08
