module
prelude
public import RootedSubsumedForest0708DispositionData

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0708
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness
theorem disposition_at_0 : dispositionTest 0 = true := by decide +kernel


theorem disposition_at_1 : dispositionTest 1 = true := by
  change (RawLeafCertificate.boundaryCheck
    ((rawLeaves 1).map Papers.RationalityTen.RootedCaches.RootedSixBase02.rawCells) Nonrational.OldTerminalMatches.M019.r1230.boundary &&
    Nonrational.InducedTerminalMatches.check Nonrational.OldTerminalMatches.M019.r1230) = true
  rw [Nonrational.OldTerminalMatches.M019.r1230_checked, Bool.and_true]
  decide +kernel

theorem disposition_at_2 : dispositionTest 2 = true := by decide +kernel


theorem disposition_at_3 : dispositionTest 3 = true := by
  change (RawLeafCertificate.boundaryCheck
    ((rawLeaves 3).map Papers.RationalityTen.RootedCaches.RootedSixBase02.rawCells) Nonrational.OldTerminalMatches.M019.r1231.boundary &&
    Nonrational.InducedTerminalMatches.check Nonrational.OldTerminalMatches.M019.r1231) = true
  rw [Nonrational.OldTerminalMatches.M019.r1231_checked, Bool.and_true]
  decide +kernel

theorem disposition_at_4 : dispositionTest 4 = true := by decide +kernel

theorem disposition_at_5 : dispositionTest 5 = true := by decide +kernel

theorem disposition_at_6 : dispositionTest 6 = true := by decide +kernel

theorem disposition_at_7 : dispositionTest 7 = true := by decide +kernel

theorem disposition_at_8 : dispositionTest 8 = true := by decide +kernel

theorem disposition_at_9 : dispositionTest 9 = true := by decide +kernel

theorem disposition_at_10 : dispositionTest 10 = true := by decide +kernel

theorem disposition_at_11 : dispositionTest 11 = true := by decide +kernel

theorem disposition_at_12 : dispositionTest 12 = true := by decide +kernel

theorem disposition_at_13 : dispositionTest 13 = true := by decide +kernel

theorem disposition_at_14 : dispositionTest 14 = true := by decide +kernel

theorem disposition_at_15 : dispositionTest 15 = true := by decide +kernel

theorem disposition_at_16 : dispositionTest 16 = true := by decide +kernel

theorem disposition_at_17 : dispositionTest 17 = true := by decide +kernel

theorem disposition_at_18 : dispositionTest 18 = true := by decide +kernel

theorem disposition_at_19 : dispositionTest 19 = true := by decide +kernel

theorem disposition_at_20 : dispositionTest 20 = true := by decide +kernel

theorem disposition_at_21 : dispositionTest 21 = true := by decide +kernel

theorem disposition_at_22 : dispositionTest 22 = true := by decide +kernel

theorem disposition_at_23 : dispositionTest 23 = true := by decide +kernel

theorem disposition_at_24 : dispositionTest 24 = true := by decide +kernel

theorem disposition_at_25 : dispositionTest 25 = true := by decide +kernel

theorem disposition_at_26 : dispositionTest 26 = true := by decide +kernel

theorem disposition_at_27 : dispositionTest 27 = true := by decide +kernel

theorem disposition_at_28 : dispositionTest 28 = true := by decide +kernel

theorem disposition_at_29 : dispositionTest 29 = true := by decide +kernel

theorem disposition_at_30 : dispositionTest 30 = true := by decide +kernel

theorem disposition_at_31 : dispositionTest 31 = true := by decide +kernel

theorem disposition_interval_0 : Interval dispositionTest 0 1 := by
  intro i hlo hhi
  have h : i = 0 := by omega
  subst i
  exact disposition_at_0


theorem disposition_interval_1 : Interval dispositionTest 1 2 := by
  intro i hlo hhi
  have h : i = 1 := by omega
  subst i
  exact disposition_at_1


theorem disposition_interval_2 : Interval dispositionTest 2 3 := by
  intro i hlo hhi
  have h : i = 2 := by omega
  subst i
  exact disposition_at_2


theorem disposition_interval_3 : Interval dispositionTest 3 4 := by
  intro i hlo hhi
  have h : i = 3 := by omega
  subst i
  exact disposition_at_3


theorem disposition_interval_4 : Interval dispositionTest 4 5 := by
  intro i hlo hhi
  have h : i = 4 := by omega
  subst i
  exact disposition_at_4


theorem disposition_interval_5 : Interval dispositionTest 5 6 := by
  intro i hlo hhi
  have h : i = 5 := by omega
  subst i
  exact disposition_at_5


theorem disposition_interval_6 : Interval dispositionTest 6 7 := by
  intro i hlo hhi
  have h : i = 6 := by omega
  subst i
  exact disposition_at_6


theorem disposition_interval_7 : Interval dispositionTest 7 8 := by
  intro i hlo hhi
  have h : i = 7 := by omega
  subst i
  exact disposition_at_7


theorem disposition_interval_8 : Interval dispositionTest 8 9 := by
  intro i hlo hhi
  have h : i = 8 := by omega
  subst i
  exact disposition_at_8


theorem disposition_interval_9 : Interval dispositionTest 9 10 := by
  intro i hlo hhi
  have h : i = 9 := by omega
  subst i
  exact disposition_at_9


theorem disposition_interval_10 : Interval dispositionTest 10 11 := by
  intro i hlo hhi
  have h : i = 10 := by omega
  subst i
  exact disposition_at_10


theorem disposition_interval_11 : Interval dispositionTest 11 12 := by
  intro i hlo hhi
  have h : i = 11 := by omega
  subst i
  exact disposition_at_11


theorem disposition_interval_12 : Interval dispositionTest 12 13 := by
  intro i hlo hhi
  have h : i = 12 := by omega
  subst i
  exact disposition_at_12


theorem disposition_interval_13 : Interval dispositionTest 13 14 := by
  intro i hlo hhi
  have h : i = 13 := by omega
  subst i
  exact disposition_at_13


theorem disposition_interval_14 : Interval dispositionTest 14 15 := by
  intro i hlo hhi
  have h : i = 14 := by omega
  subst i
  exact disposition_at_14


theorem disposition_interval_15 : Interval dispositionTest 15 16 := by
  intro i hlo hhi
  have h : i = 15 := by omega
  subst i
  exact disposition_at_15


theorem disposition_interval_16 : Interval dispositionTest 16 17 := by
  intro i hlo hhi
  have h : i = 16 := by omega
  subst i
  exact disposition_at_16


theorem disposition_interval_17 : Interval dispositionTest 17 18 := by
  intro i hlo hhi
  have h : i = 17 := by omega
  subst i
  exact disposition_at_17


theorem disposition_interval_18 : Interval dispositionTest 18 19 := by
  intro i hlo hhi
  have h : i = 18 := by omega
  subst i
  exact disposition_at_18


theorem disposition_interval_19 : Interval dispositionTest 19 20 := by
  intro i hlo hhi
  have h : i = 19 := by omega
  subst i
  exact disposition_at_19


theorem disposition_interval_20 : Interval dispositionTest 20 21 := by
  intro i hlo hhi
  have h : i = 20 := by omega
  subst i
  exact disposition_at_20


theorem disposition_interval_21 : Interval dispositionTest 21 22 := by
  intro i hlo hhi
  have h : i = 21 := by omega
  subst i
  exact disposition_at_21


theorem disposition_interval_22 : Interval dispositionTest 22 23 := by
  intro i hlo hhi
  have h : i = 22 := by omega
  subst i
  exact disposition_at_22


theorem disposition_interval_23 : Interval dispositionTest 23 24 := by
  intro i hlo hhi
  have h : i = 23 := by omega
  subst i
  exact disposition_at_23


theorem disposition_interval_24 : Interval dispositionTest 24 25 := by
  intro i hlo hhi
  have h : i = 24 := by omega
  subst i
  exact disposition_at_24


theorem disposition_interval_25 : Interval dispositionTest 25 26 := by
  intro i hlo hhi
  have h : i = 25 := by omega
  subst i
  exact disposition_at_25


theorem disposition_interval_26 : Interval dispositionTest 26 27 := by
  intro i hlo hhi
  have h : i = 26 := by omega
  subst i
  exact disposition_at_26


theorem disposition_interval_27 : Interval dispositionTest 27 28 := by
  intro i hlo hhi
  have h : i = 27 := by omega
  subst i
  exact disposition_at_27


theorem disposition_interval_28 : Interval dispositionTest 28 29 := by
  intro i hlo hhi
  have h : i = 28 := by omega
  subst i
  exact disposition_at_28


theorem disposition_interval_29 : Interval dispositionTest 29 30 := by
  intro i hlo hhi
  have h : i = 29 := by omega
  subst i
  exact disposition_at_29


theorem disposition_interval_30 : Interval dispositionTest 30 31 := by
  intro i hlo hhi
  have h : i = 30 := by omega
  subst i
  exact disposition_at_30


theorem disposition_interval_31 : Interval dispositionTest 31 32 := by
  intro i hlo hhi
  have h : i = 31 := by omega
  subst i
  exact disposition_at_31

end Papers.RationalityTen.RootedForests.RootedSubsumedForest0708
