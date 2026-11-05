module
prelude
public import RootedSubsumedForest0854Data
public import RawLeafCertificate
public import OldTerminalMatches.M025

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0854
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness

def dispositionTable : Table RawLeafCertificate.Certificate :=
(.branch 3
 (.branch 1
 (.leaf (.quota 1))
 (.branch 2
 (.leaf (.quota 3))
 (.leaf (.quota 9))))
 (.branch 5
 (.branch 4
 (.leaf (.quota 9))
 (.leaf (.matching Nonrational.OldTerminalMatches.M025.r1636)))
 (.branch 6
 (.leaf (.quota 3))
 (.leaf (.matching Nonrational.OldTerminalMatches.M025.r1637)))))
def disposition (j : Fin leafCount) := dispositionTable.get j.val
def dispositionTest (i : Nat) : Bool := RawLeafCertificate.check quota
  ((rawLeaves i).map Papers.RationalityTen.RootedCaches.RootedSixExtra05.rawCells) (dispositionTable.get i)
theorem disposition_at_0 : dispositionTest 0 = true := by decide +kernel

theorem disposition_at_1 : dispositionTest 1 = true := by decide +kernel

theorem disposition_at_2 : dispositionTest 2 = true := by decide +kernel

theorem disposition_at_3 : dispositionTest 3 = true := by decide +kernel


theorem disposition_at_4 : dispositionTest 4 = true := by
  change (RawLeafCertificate.boundaryCheck
    ((rawLeaves 4).map Papers.RationalityTen.RootedCaches.RootedSixExtra05.rawCells) Nonrational.OldTerminalMatches.M025.r1636.boundary &&
    Nonrational.InducedTerminalMatches.check Nonrational.OldTerminalMatches.M025.r1636) = true
  rw [Nonrational.OldTerminalMatches.M025.r1636_checked, Bool.and_true]
  decide +kernel

theorem disposition_at_5 : dispositionTest 5 = true := by decide +kernel


theorem disposition_at_6 : dispositionTest 6 = true := by
  change (RawLeafCertificate.boundaryCheck
    ((rawLeaves 6).map Papers.RationalityTen.RootedCaches.RootedSixExtra05.rawCells) Nonrational.OldTerminalMatches.M025.r1637.boundary &&
    Nonrational.InducedTerminalMatches.check Nonrational.OldTerminalMatches.M025.r1637) = true
  rw [Nonrational.OldTerminalMatches.M025.r1637_checked, Bool.and_true]
  decide +kernel

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

theorem dispositionTest_complete : Interval dispositionTest 0 leafCount := (interval_append dispositionTest 0 3 7 (interval_append dispositionTest 0 1 3 disposition_interval_0 (interval_append dispositionTest 1 2 3 disposition_interval_1 disposition_interval_2)) (interval_append dispositionTest 3 5 7 (interval_append dispositionTest 3 4 5 disposition_interval_3 disposition_interval_4) (interval_append dispositionTest 5 6 7 disposition_interval_5 disposition_interval_6)))
theorem disposition_checked (j : Fin leafCount) :
    RawLeafCertificate.check quota ((rawLeaves j.val).map Papers.RationalityTen.RootedCaches.RootedSixExtra05.rawCells)
      (disposition j) = true :=
  dispositionTest_complete j.val (Nat.zero_le _) j.isLt

end Papers.RationalityTen.RootedForests.RootedSubsumedForest0854
