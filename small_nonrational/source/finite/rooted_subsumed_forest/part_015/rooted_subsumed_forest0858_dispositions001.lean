module
prelude
public import RootedSubsumedForest0858DispositionData

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0858
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness
theorem disposition_at_32 : dispositionTest 32 = true := by decide +kernel

theorem disposition_at_33 : dispositionTest 33 = true := by decide +kernel

theorem disposition_at_34 : dispositionTest 34 = true := by decide +kernel

theorem disposition_at_35 : dispositionTest 35 = true := by decide +kernel

theorem disposition_at_36 : dispositionTest 36 = true := by decide +kernel

theorem disposition_at_37 : dispositionTest 37 = true := by decide +kernel

theorem disposition_at_38 : dispositionTest 38 = true := by decide +kernel

theorem disposition_at_39 : dispositionTest 39 = true := by decide +kernel

theorem disposition_at_40 : dispositionTest 40 = true := by decide +kernel

theorem disposition_at_41 : dispositionTest 41 = true := by decide +kernel

theorem disposition_at_42 : dispositionTest 42 = true := by decide +kernel

theorem disposition_at_43 : dispositionTest 43 = true := by decide +kernel

theorem disposition_at_44 : dispositionTest 44 = true := by decide +kernel

theorem disposition_at_45 : dispositionTest 45 = true := by decide +kernel

theorem disposition_at_46 : dispositionTest 46 = true := by decide +kernel

theorem disposition_at_47 : dispositionTest 47 = true := by decide +kernel

theorem disposition_at_48 : dispositionTest 48 = true := by decide +kernel

theorem disposition_at_49 : dispositionTest 49 = true := by decide +kernel

theorem disposition_interval_32 : Interval dispositionTest 32 33 := by
  intro i hlo hhi
  have h : i = 32 := by omega
  subst i
  exact disposition_at_32


theorem disposition_interval_33 : Interval dispositionTest 33 34 := by
  intro i hlo hhi
  have h : i = 33 := by omega
  subst i
  exact disposition_at_33


theorem disposition_interval_34 : Interval dispositionTest 34 35 := by
  intro i hlo hhi
  have h : i = 34 := by omega
  subst i
  exact disposition_at_34


theorem disposition_interval_35 : Interval dispositionTest 35 36 := by
  intro i hlo hhi
  have h : i = 35 := by omega
  subst i
  exact disposition_at_35


theorem disposition_interval_36 : Interval dispositionTest 36 37 := by
  intro i hlo hhi
  have h : i = 36 := by omega
  subst i
  exact disposition_at_36


theorem disposition_interval_37 : Interval dispositionTest 37 38 := by
  intro i hlo hhi
  have h : i = 37 := by omega
  subst i
  exact disposition_at_37


theorem disposition_interval_38 : Interval dispositionTest 38 39 := by
  intro i hlo hhi
  have h : i = 38 := by omega
  subst i
  exact disposition_at_38


theorem disposition_interval_39 : Interval dispositionTest 39 40 := by
  intro i hlo hhi
  have h : i = 39 := by omega
  subst i
  exact disposition_at_39


theorem disposition_interval_40 : Interval dispositionTest 40 41 := by
  intro i hlo hhi
  have h : i = 40 := by omega
  subst i
  exact disposition_at_40


theorem disposition_interval_41 : Interval dispositionTest 41 42 := by
  intro i hlo hhi
  have h : i = 41 := by omega
  subst i
  exact disposition_at_41


theorem disposition_interval_42 : Interval dispositionTest 42 43 := by
  intro i hlo hhi
  have h : i = 42 := by omega
  subst i
  exact disposition_at_42


theorem disposition_interval_43 : Interval dispositionTest 43 44 := by
  intro i hlo hhi
  have h : i = 43 := by omega
  subst i
  exact disposition_at_43


theorem disposition_interval_44 : Interval dispositionTest 44 45 := by
  intro i hlo hhi
  have h : i = 44 := by omega
  subst i
  exact disposition_at_44


theorem disposition_interval_45 : Interval dispositionTest 45 46 := by
  intro i hlo hhi
  have h : i = 45 := by omega
  subst i
  exact disposition_at_45


theorem disposition_interval_46 : Interval dispositionTest 46 47 := by
  intro i hlo hhi
  have h : i = 46 := by omega
  subst i
  exact disposition_at_46


theorem disposition_interval_47 : Interval dispositionTest 47 48 := by
  intro i hlo hhi
  have h : i = 47 := by omega
  subst i
  exact disposition_at_47


theorem disposition_interval_48 : Interval dispositionTest 48 49 := by
  intro i hlo hhi
  have h : i = 48 := by omega
  subst i
  exact disposition_at_48


theorem disposition_interval_49 : Interval dispositionTest 49 50 := by
  intro i hlo hhi
  have h : i = 49 := by omega
  subst i
  exact disposition_at_49

end Papers.RationalityTen.RootedForests.RootedSubsumedForest0858
