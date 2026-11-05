module
prelude
public import RootedSubsumedForest0248Data
public import RawLeafCertificate
public import OldTerminalMatches.M005

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0248
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness

def dispositionTable : Table RawLeafCertificate.Certificate :=
(.branch 8
 (.branch 4
 (.branch 2
 (.branch 1
 (.leaf (.incidence 5))
 (.leaf (.incidence 8)))
 (.leaf (.quota 1)))
 (.branch 6
 (.branch 5
 (.leaf (.matching Nonrational.OldTerminalMatches.M005.r0341))
 (.leaf (.quota 2)))
 (.leaf (.incidence 5))))
 (.branch 12
 (.branch 10
 (.branch 9
 (.leaf (.incidence 0))
 (.leaf (.incidence 5)))
 (.branch 11
 (.leaf (.matching Nonrational.OldTerminalMatches.M005.r0342))
 (.leaf (.matching Nonrational.OldTerminalMatches.M005.r0343))))
 (.branch 14
 (.leaf (.quota 2))
 (.branch 15
 (.leaf (.quota 2))
 (.leaf (.incidence 4))))))
def disposition (j : Fin leafCount) := dispositionTable.get j.val
def dispositionTest (i : Nat) : Bool := RawLeafCertificate.check quota
  ((rawLeaves i).map Papers.RationalityTen.RootedCaches.RootedSixBase02.rawCells) (dispositionTable.get i)
theorem disposition_at_0 : dispositionTest 0 = true := by decide +kernel

theorem disposition_at_1 : dispositionTest 1 = true := by decide +kernel

theorem disposition_at_2 : dispositionTest 2 = true := by decide +kernel

theorem disposition_at_3 : dispositionTest 3 = true := by decide +kernel


theorem disposition_at_4 : dispositionTest 4 = true := by
  change (RawLeafCertificate.boundaryCheck
    ((rawLeaves 4).map Papers.RationalityTen.RootedCaches.RootedSixBase02.rawCells) Nonrational.OldTerminalMatches.M005.r0341.boundary &&
    Nonrational.InducedTerminalMatches.check Nonrational.OldTerminalMatches.M005.r0341) = true
  rw [Nonrational.OldTerminalMatches.M005.r0341_checked, Bool.and_true]
  decide +kernel

theorem disposition_at_5 : dispositionTest 5 = true := by decide +kernel

theorem disposition_at_6 : dispositionTest 6 = true := by decide +kernel

theorem disposition_at_7 : dispositionTest 7 = true := by decide +kernel

theorem disposition_at_8 : dispositionTest 8 = true := by decide +kernel

theorem disposition_at_9 : dispositionTest 9 = true := by decide +kernel


theorem disposition_at_10 : dispositionTest 10 = true := by
  change (RawLeafCertificate.boundaryCheck
    ((rawLeaves 10).map Papers.RationalityTen.RootedCaches.RootedSixBase02.rawCells) Nonrational.OldTerminalMatches.M005.r0342.boundary &&
    Nonrational.InducedTerminalMatches.check Nonrational.OldTerminalMatches.M005.r0342) = true
  rw [Nonrational.OldTerminalMatches.M005.r0342_checked, Bool.and_true]
  decide +kernel


theorem disposition_at_11 : dispositionTest 11 = true := by
  change (RawLeafCertificate.boundaryCheck
    ((rawLeaves 11).map Papers.RationalityTen.RootedCaches.RootedSixBase02.rawCells) Nonrational.OldTerminalMatches.M005.r0343.boundary &&
    Nonrational.InducedTerminalMatches.check Nonrational.OldTerminalMatches.M005.r0343) = true
  rw [Nonrational.OldTerminalMatches.M005.r0343_checked, Bool.and_true]
  decide +kernel

theorem disposition_at_12 : dispositionTest 12 = true := by decide +kernel

theorem disposition_at_13 : dispositionTest 13 = true := by decide +kernel

theorem disposition_at_14 : dispositionTest 14 = true := by decide +kernel

theorem disposition_at_15 : dispositionTest 15 = true := by decide +kernel

theorem disposition_at_16 : dispositionTest 16 = true := by decide +kernel

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

theorem dispositionTest_complete : Interval dispositionTest 0 leafCount := (interval_append dispositionTest 0 8 17 (interval_append dispositionTest 0 4 8 (interval_append dispositionTest 0 2 4 (interval_append dispositionTest 0 1 2 disposition_interval_0 disposition_interval_1) (interval_append dispositionTest 2 3 4 disposition_interval_2 disposition_interval_3)) (interval_append dispositionTest 4 6 8 (interval_append dispositionTest 4 5 6 disposition_interval_4 disposition_interval_5) (interval_append dispositionTest 6 7 8 disposition_interval_6 disposition_interval_7))) (interval_append dispositionTest 8 12 17 (interval_append dispositionTest 8 10 12 (interval_append dispositionTest 8 9 10 disposition_interval_8 disposition_interval_9) (interval_append dispositionTest 10 11 12 disposition_interval_10 disposition_interval_11)) (interval_append dispositionTest 12 14 17 (interval_append dispositionTest 12 13 14 disposition_interval_12 disposition_interval_13) (interval_append dispositionTest 14 15 17 disposition_interval_14 (interval_append dispositionTest 15 16 17 disposition_interval_15 disposition_interval_16)))))
theorem disposition_checked (j : Fin leafCount) :
    RawLeafCertificate.check quota ((rawLeaves j.val).map Papers.RationalityTen.RootedCaches.RootedSixBase02.rawCells)
      (disposition j) = true :=
  dispositionTest_complete j.val (Nat.zero_le _) j.isLt

end Papers.RationalityTen.RootedForests.RootedSubsumedForest0248
