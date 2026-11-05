module
prelude
public import RootedSubsumedForest0247Data
public import RawLeafCertificate
public import OldTerminalMatches.M005

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0247
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness

def dispositionTable : Table RawLeafCertificate.Certificate :=
(.branch 6
 (.branch 3
 (.branch 1
 (.leaf (.incidence 5))
 (.branch 2
 (.leaf (.incidence 5))
 (.leaf (.quota 2))))
 (.branch 4
 (.leaf (.quota 2))
 (.branch 5
 (.leaf (.matching Nonrational.OldTerminalMatches.M005.r0337))
 (.leaf (.matching Nonrational.OldTerminalMatches.M005.r0338)))))
 (.branch 9
 (.branch 7
 (.leaf (.incidence 8))
 (.branch 8
 (.leaf (.quota 1))
 (.leaf (.matching Nonrational.OldTerminalMatches.M005.r0339))))
 (.branch 11
 (.branch 10
 (.leaf (.matching Nonrational.OldTerminalMatches.M005.r0340))
 (.leaf (.incidence 0)))
 (.leaf (.quota 2)))))
def disposition (j : Fin leafCount) := dispositionTable.get j.val
def dispositionTest (i : Nat) : Bool := RawLeafCertificate.check quota
  ((rawLeaves i).map Papers.RationalityTen.RootedCaches.RootedSixBase02.rawCells) (dispositionTable.get i)
theorem disposition_at_0 : dispositionTest 0 = true := by decide +kernel

theorem disposition_at_1 : dispositionTest 1 = true := by decide +kernel

theorem disposition_at_2 : dispositionTest 2 = true := by decide +kernel

theorem disposition_at_3 : dispositionTest 3 = true := by decide +kernel


theorem disposition_at_4 : dispositionTest 4 = true := by
  change (RawLeafCertificate.boundaryCheck
    ((rawLeaves 4).map Papers.RationalityTen.RootedCaches.RootedSixBase02.rawCells) Nonrational.OldTerminalMatches.M005.r0337.boundary &&
    Nonrational.InducedTerminalMatches.check Nonrational.OldTerminalMatches.M005.r0337) = true
  rw [Nonrational.OldTerminalMatches.M005.r0337_checked, Bool.and_true]
  decide +kernel


theorem disposition_at_5 : dispositionTest 5 = true := by
  change (RawLeafCertificate.boundaryCheck
    ((rawLeaves 5).map Papers.RationalityTen.RootedCaches.RootedSixBase02.rawCells) Nonrational.OldTerminalMatches.M005.r0338.boundary &&
    Nonrational.InducedTerminalMatches.check Nonrational.OldTerminalMatches.M005.r0338) = true
  rw [Nonrational.OldTerminalMatches.M005.r0338_checked, Bool.and_true]
  decide +kernel

theorem disposition_at_6 : dispositionTest 6 = true := by decide +kernel

theorem disposition_at_7 : dispositionTest 7 = true := by decide +kernel


theorem disposition_at_8 : dispositionTest 8 = true := by
  change (RawLeafCertificate.boundaryCheck
    ((rawLeaves 8).map Papers.RationalityTen.RootedCaches.RootedSixBase02.rawCells) Nonrational.OldTerminalMatches.M005.r0339.boundary &&
    Nonrational.InducedTerminalMatches.check Nonrational.OldTerminalMatches.M005.r0339) = true
  rw [Nonrational.OldTerminalMatches.M005.r0339_checked, Bool.and_true]
  decide +kernel


theorem disposition_at_9 : dispositionTest 9 = true := by
  change (RawLeafCertificate.boundaryCheck
    ((rawLeaves 9).map Papers.RationalityTen.RootedCaches.RootedSixBase02.rawCells) Nonrational.OldTerminalMatches.M005.r0340.boundary &&
    Nonrational.InducedTerminalMatches.check Nonrational.OldTerminalMatches.M005.r0340) = true
  rw [Nonrational.OldTerminalMatches.M005.r0340_checked, Bool.and_true]
  decide +kernel

theorem disposition_at_10 : dispositionTest 10 = true := by decide +kernel

theorem disposition_at_11 : dispositionTest 11 = true := by decide +kernel

theorem disposition_at_12 : dispositionTest 12 = true := by decide +kernel

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

theorem dispositionTest_complete : Interval dispositionTest 0 leafCount := (interval_append dispositionTest 0 6 13 (interval_append dispositionTest 0 3 6 (interval_append dispositionTest 0 1 3 disposition_interval_0 (interval_append dispositionTest 1 2 3 disposition_interval_1 disposition_interval_2)) (interval_append dispositionTest 3 4 6 disposition_interval_3 (interval_append dispositionTest 4 5 6 disposition_interval_4 disposition_interval_5))) (interval_append dispositionTest 6 9 13 (interval_append dispositionTest 6 7 9 disposition_interval_6 (interval_append dispositionTest 7 8 9 disposition_interval_7 disposition_interval_8)) (interval_append dispositionTest 9 11 13 (interval_append dispositionTest 9 10 11 disposition_interval_9 disposition_interval_10) (interval_append dispositionTest 11 12 13 disposition_interval_11 disposition_interval_12))))
theorem disposition_checked (j : Fin leafCount) :
    RawLeafCertificate.check quota ((rawLeaves j.val).map Papers.RationalityTen.RootedCaches.RootedSixBase02.rawCells)
      (disposition j) = true :=
  dispositionTest_complete j.val (Nat.zero_le _) j.isLt

end Papers.RationalityTen.RootedForests.RootedSubsumedForest0247
