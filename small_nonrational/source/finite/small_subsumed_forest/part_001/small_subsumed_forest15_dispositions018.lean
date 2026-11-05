module
prelude
public import SmallSubsumedForest15DispositionData

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.SmallRawForests.SmallSubsumedForest15
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness
theorem disposition_at_576 : dispositionTest 576 = true := by decide +kernel

theorem disposition_at_577 : dispositionTest 577 = true := by decide +kernel

theorem disposition_interval_576 : Interval dispositionTest 576 577 := by
  intro i hlo hhi
  have h : i = 576 := by omega
  subst i
  exact disposition_at_576


theorem disposition_interval_577 : Interval dispositionTest 577 578 := by
  intro i hlo hhi
  have h : i = 577 := by omega
  subst i
  exact disposition_at_577

end Papers.RationalityTen.SmallRawForests.SmallSubsumedForest15
