module
prelude
public import SmallSubsumedForest13Data
public import RawLeafCertificate
public import OldTerminalMatches.M000

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.SmallRawForests.SmallSubsumedForest13
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness

def dispositionTable : Table RawLeafCertificate.Certificate :=
(.branch 5
 (.branch 2
 (.branch 1
 (.leaf (.matching Nonrational.OldTerminalMatches.M000.r0029))
 (.leaf (.quota 2)))
 (.branch 3
 (.leaf (.matching Nonrational.OldTerminalMatches.M000.r0030))
 (.branch 4
 (.leaf (.matching Nonrational.OldTerminalMatches.M000.r0031))
 (.leaf (.quota 2)))))
 (.leaf (.quota 2)))
def disposition (j : Fin leafCount) := dispositionTable.get j.val
def dispositionTest (i : Nat) : Bool := RawLeafCertificate.check quota
  ((rawLeaves i).map RootedSmallCache.rawCells) (dispositionTable.get i)

theorem disposition_at_0 : dispositionTest 0 = true := by
  change (RawLeafCertificate.boundaryCheck
    ((rawLeaves 0).map RootedSmallCache.rawCells) Nonrational.OldTerminalMatches.M000.r0029.boundary &&
    Nonrational.InducedTerminalMatches.check Nonrational.OldTerminalMatches.M000.r0029) = true
  rw [Nonrational.OldTerminalMatches.M000.r0029_checked, Bool.and_true]
  decide +kernel

theorem disposition_at_1 : dispositionTest 1 = true := by decide +kernel


theorem disposition_at_2 : dispositionTest 2 = true := by
  change (RawLeafCertificate.boundaryCheck
    ((rawLeaves 2).map RootedSmallCache.rawCells) Nonrational.OldTerminalMatches.M000.r0030.boundary &&
    Nonrational.InducedTerminalMatches.check Nonrational.OldTerminalMatches.M000.r0030) = true
  rw [Nonrational.OldTerminalMatches.M000.r0030_checked, Bool.and_true]
  decide +kernel


theorem disposition_at_3 : dispositionTest 3 = true := by
  change (RawLeafCertificate.boundaryCheck
    ((rawLeaves 3).map RootedSmallCache.rawCells) Nonrational.OldTerminalMatches.M000.r0031.boundary &&
    Nonrational.InducedTerminalMatches.check Nonrational.OldTerminalMatches.M000.r0031) = true
  rw [Nonrational.OldTerminalMatches.M000.r0031_checked, Bool.and_true]
  decide +kernel

theorem disposition_at_4 : dispositionTest 4 = true := by decide +kernel

theorem disposition_at_5 : dispositionTest 5 = true := by decide +kernel

theorem disposition_at_6 : dispositionTest 6 = true := by decide +kernel

theorem disposition_at_7 : dispositionTest 7 = true := by decide +kernel

theorem disposition_at_8 : dispositionTest 8 = true := by decide +kernel

theorem disposition_at_9 : dispositionTest 9 = true := by decide +kernel

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

theorem dispositionTest_complete : Interval dispositionTest 0 leafCount := (interval_append dispositionTest 0 5 10 (interval_append dispositionTest 0 2 5 (interval_append dispositionTest 0 1 2 disposition_interval_0 disposition_interval_1) (interval_append dispositionTest 2 3 5 disposition_interval_2 (interval_append dispositionTest 3 4 5 disposition_interval_3 disposition_interval_4))) (interval_append dispositionTest 5 7 10 (interval_append dispositionTest 5 6 7 disposition_interval_5 disposition_interval_6) (interval_append dispositionTest 7 8 10 disposition_interval_7 (interval_append dispositionTest 8 9 10 disposition_interval_8 disposition_interval_9))))
theorem disposition_checked (j : Fin leafCount) :
    RawLeafCertificate.check quota ((rawLeaves j.val).map RootedSmallCache.rawCells)
      (disposition j) = true :=
  dispositionTest_complete j.val (Nat.zero_le _) j.isLt

end Papers.RationalityTen.SmallRawForests.SmallSubsumedForest13
