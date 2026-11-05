module
prelude
public import RootedSubsumedForest0310Data
public import RawLeafCertificate
public import OldTerminalMatches.M007

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0310
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness

def dispositionTable : Table RawLeafCertificate.Certificate :=
(.branch 9
 (.branch 4
 (.branch 2
 (.leaf (.quota 2))
 (.branch 3
 (.leaf (.quota 2))
 (.leaf (.matching Nonrational.OldTerminalMatches.M007.r0462))))
 (.branch 6
 (.leaf (.quota 2))
 (.branch 7
 (.leaf (.matching Nonrational.OldTerminalMatches.M007.r0463))
 (.branch 8
 (.leaf (.matching Nonrational.OldTerminalMatches.M007.r0464))
 (.leaf (.matching Nonrational.OldTerminalMatches.M007.r0465))))))
 (.branch 13
 (.branch 11
 (.branch 10
 (.leaf (.quota 2))
 (.leaf (.matching Nonrational.OldTerminalMatches.M007.r0466)))
 (.branch 12
 (.leaf (.matching Nonrational.OldTerminalMatches.M007.r0467))
 (.leaf (.matching Nonrational.OldTerminalMatches.M007.r0468))))
 (.branch 15
 (.branch 14
 (.leaf (.matching Nonrational.OldTerminalMatches.M007.r0469))
 (.leaf (.incidence 5)))
 (.branch 16
 (.leaf (.incidence 5))
 (.leaf (.quota 2))))))
def disposition (j : Fin leafCount) := dispositionTable.get j.val
def dispositionTest (i : Nat) : Bool := RawLeafCertificate.check quota
  ((rawLeaves i).map Papers.RationalityTen.RootedCaches.RootedSixBase00.rawCells) (dispositionTable.get i)
theorem disposition_at_0 : dispositionTest 0 = true := by decide +kernel

theorem disposition_at_1 : dispositionTest 1 = true := by decide +kernel

theorem disposition_at_2 : dispositionTest 2 = true := by decide +kernel


theorem disposition_at_3 : dispositionTest 3 = true := by
  change (RawLeafCertificate.boundaryCheck
    ((rawLeaves 3).map Papers.RationalityTen.RootedCaches.RootedSixBase00.rawCells) Nonrational.OldTerminalMatches.M007.r0462.boundary &&
    Nonrational.InducedTerminalMatches.check Nonrational.OldTerminalMatches.M007.r0462) = true
  rw [Nonrational.OldTerminalMatches.M007.r0462_checked, Bool.and_true]
  decide +kernel

theorem disposition_at_4 : dispositionTest 4 = true := by decide +kernel

theorem disposition_at_5 : dispositionTest 5 = true := by decide +kernel


theorem disposition_at_6 : dispositionTest 6 = true := by
  change (RawLeafCertificate.boundaryCheck
    ((rawLeaves 6).map Papers.RationalityTen.RootedCaches.RootedSixBase00.rawCells) Nonrational.OldTerminalMatches.M007.r0463.boundary &&
    Nonrational.InducedTerminalMatches.check Nonrational.OldTerminalMatches.M007.r0463) = true
  rw [Nonrational.OldTerminalMatches.M007.r0463_checked, Bool.and_true]
  decide +kernel


theorem disposition_at_7 : dispositionTest 7 = true := by
  change (RawLeafCertificate.boundaryCheck
    ((rawLeaves 7).map Papers.RationalityTen.RootedCaches.RootedSixBase00.rawCells) Nonrational.OldTerminalMatches.M007.r0464.boundary &&
    Nonrational.InducedTerminalMatches.check Nonrational.OldTerminalMatches.M007.r0464) = true
  rw [Nonrational.OldTerminalMatches.M007.r0464_checked, Bool.and_true]
  decide +kernel


theorem disposition_at_8 : dispositionTest 8 = true := by
  change (RawLeafCertificate.boundaryCheck
    ((rawLeaves 8).map Papers.RationalityTen.RootedCaches.RootedSixBase00.rawCells) Nonrational.OldTerminalMatches.M007.r0465.boundary &&
    Nonrational.InducedTerminalMatches.check Nonrational.OldTerminalMatches.M007.r0465) = true
  rw [Nonrational.OldTerminalMatches.M007.r0465_checked, Bool.and_true]
  decide +kernel

theorem disposition_at_9 : dispositionTest 9 = true := by decide +kernel


theorem disposition_at_10 : dispositionTest 10 = true := by
  change (RawLeafCertificate.boundaryCheck
    ((rawLeaves 10).map Papers.RationalityTen.RootedCaches.RootedSixBase00.rawCells) Nonrational.OldTerminalMatches.M007.r0466.boundary &&
    Nonrational.InducedTerminalMatches.check Nonrational.OldTerminalMatches.M007.r0466) = true
  rw [Nonrational.OldTerminalMatches.M007.r0466_checked, Bool.and_true]
  decide +kernel


theorem disposition_at_11 : dispositionTest 11 = true := by
  change (RawLeafCertificate.boundaryCheck
    ((rawLeaves 11).map Papers.RationalityTen.RootedCaches.RootedSixBase00.rawCells) Nonrational.OldTerminalMatches.M007.r0467.boundary &&
    Nonrational.InducedTerminalMatches.check Nonrational.OldTerminalMatches.M007.r0467) = true
  rw [Nonrational.OldTerminalMatches.M007.r0467_checked, Bool.and_true]
  decide +kernel


theorem disposition_at_12 : dispositionTest 12 = true := by
  change (RawLeafCertificate.boundaryCheck
    ((rawLeaves 12).map Papers.RationalityTen.RootedCaches.RootedSixBase00.rawCells) Nonrational.OldTerminalMatches.M007.r0468.boundary &&
    Nonrational.InducedTerminalMatches.check Nonrational.OldTerminalMatches.M007.r0468) = true
  rw [Nonrational.OldTerminalMatches.M007.r0468_checked, Bool.and_true]
  decide +kernel


theorem disposition_at_13 : dispositionTest 13 = true := by
  change (RawLeafCertificate.boundaryCheck
    ((rawLeaves 13).map Papers.RationalityTen.RootedCaches.RootedSixBase00.rawCells) Nonrational.OldTerminalMatches.M007.r0469.boundary &&
    Nonrational.InducedTerminalMatches.check Nonrational.OldTerminalMatches.M007.r0469) = true
  rw [Nonrational.OldTerminalMatches.M007.r0469_checked, Bool.and_true]
  decide +kernel

theorem disposition_at_14 : dispositionTest 14 = true := by decide +kernel

theorem disposition_at_15 : dispositionTest 15 = true := by decide +kernel

theorem disposition_at_16 : dispositionTest 16 = true := by decide +kernel

theorem disposition_at_17 : dispositionTest 17 = true := by decide +kernel

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

theorem dispositionTest_complete : Interval dispositionTest 0 leafCount := (interval_append dispositionTest 0 9 18 (interval_append dispositionTest 0 4 9 (interval_append dispositionTest 0 2 4 (interval_append dispositionTest 0 1 2 disposition_interval_0 disposition_interval_1) (interval_append dispositionTest 2 3 4 disposition_interval_2 disposition_interval_3)) (interval_append dispositionTest 4 6 9 (interval_append dispositionTest 4 5 6 disposition_interval_4 disposition_interval_5) (interval_append dispositionTest 6 7 9 disposition_interval_6 (interval_append dispositionTest 7 8 9 disposition_interval_7 disposition_interval_8)))) (interval_append dispositionTest 9 13 18 (interval_append dispositionTest 9 11 13 (interval_append dispositionTest 9 10 11 disposition_interval_9 disposition_interval_10) (interval_append dispositionTest 11 12 13 disposition_interval_11 disposition_interval_12)) (interval_append dispositionTest 13 15 18 (interval_append dispositionTest 13 14 15 disposition_interval_13 disposition_interval_14) (interval_append dispositionTest 15 16 18 disposition_interval_15 (interval_append dispositionTest 16 17 18 disposition_interval_16 disposition_interval_17)))))
theorem disposition_checked (j : Fin leafCount) :
    RawLeafCertificate.check quota ((rawLeaves j.val).map Papers.RationalityTen.RootedCaches.RootedSixBase00.rawCells)
      (disposition j) = true :=
  dispositionTest_complete j.val (Nat.zero_le _) j.isLt

end Papers.RationalityTen.RootedForests.RootedSubsumedForest0310
