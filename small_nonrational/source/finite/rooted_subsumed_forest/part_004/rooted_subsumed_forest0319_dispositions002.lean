module
prelude
public import RootedSubsumedForest0319DispositionData

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0319
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness
theorem disposition_at_64 : dispositionTest 64 = true := by decide +kernel

theorem disposition_at_65 : dispositionTest 65 = true := by decide +kernel

theorem disposition_at_66 : dispositionTest 66 = true := by decide +kernel

theorem disposition_at_67 : dispositionTest 67 = true := by decide +kernel

theorem disposition_at_68 : dispositionTest 68 = true := by decide +kernel

theorem disposition_interval_64 : Interval dispositionTest 64 65 := by
  intro i hlo hhi
  have h : i = 64 := by omega
  subst i
  exact disposition_at_64


theorem disposition_interval_65 : Interval dispositionTest 65 66 := by
  intro i hlo hhi
  have h : i = 65 := by omega
  subst i
  exact disposition_at_65


theorem disposition_interval_66 : Interval dispositionTest 66 67 := by
  intro i hlo hhi
  have h : i = 66 := by omega
  subst i
  exact disposition_at_66


theorem disposition_interval_67 : Interval dispositionTest 67 68 := by
  intro i hlo hhi
  have h : i = 67 := by omega
  subst i
  exact disposition_at_67


theorem disposition_interval_68 : Interval dispositionTest 68 69 := by
  intro i hlo hhi
  have h : i = 68 := by omega
  subst i
  exact disposition_at_68

end Papers.RationalityTen.RootedForests.RootedSubsumedForest0319
