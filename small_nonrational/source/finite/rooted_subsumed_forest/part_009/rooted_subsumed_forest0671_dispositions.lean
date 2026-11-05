module
prelude
public import RootedSubsumedForest0671Data
public import RawLeafCertificate
public import OldTerminalMatches.M018

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0671
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness

def dispositionTable : Table RawLeafCertificate.Certificate :=
(.branch 3
 (.branch 1
 (.leaf (.incidence 4))
 (.branch 2
 (.leaf (.matching Nonrational.OldTerminalMatches.M018.r1212))
 (.leaf (.matching Nonrational.OldTerminalMatches.M018.r1213))))
 (.branch 4
 (.leaf (.matching Nonrational.OldTerminalMatches.M018.r1214))
 (.branch 5
 (.leaf (.incidence 4))
 (.leaf (.matching Nonrational.OldTerminalMatches.M018.r1215)))))
def disposition (j : Fin leafCount) := dispositionTable.get j.val
def dispositionTest (i : Nat) : Bool := RawLeafCertificate.check quota
  ((rawLeaves i).map Papers.RationalityTen.RootedCaches.RootedSixBase03.rawCells) (dispositionTable.get i)
theorem disposition_at_0 : dispositionTest 0 = true := by decide +kernel


theorem disposition_at_1 : dispositionTest 1 = true := by
  change (RawLeafCertificate.boundaryCheck
    ((rawLeaves 1).map Papers.RationalityTen.RootedCaches.RootedSixBase03.rawCells) Nonrational.OldTerminalMatches.M018.r1212.boundary &&
    Nonrational.InducedTerminalMatches.check Nonrational.OldTerminalMatches.M018.r1212) = true
  rw [Nonrational.OldTerminalMatches.M018.r1212_checked, Bool.and_true]
  decide +kernel


theorem disposition_at_2 : dispositionTest 2 = true := by
  change (RawLeafCertificate.boundaryCheck
    ((rawLeaves 2).map Papers.RationalityTen.RootedCaches.RootedSixBase03.rawCells) Nonrational.OldTerminalMatches.M018.r1213.boundary &&
    Nonrational.InducedTerminalMatches.check Nonrational.OldTerminalMatches.M018.r1213) = true
  rw [Nonrational.OldTerminalMatches.M018.r1213_checked, Bool.and_true]
  decide +kernel


theorem disposition_at_3 : dispositionTest 3 = true := by
  change (RawLeafCertificate.boundaryCheck
    ((rawLeaves 3).map Papers.RationalityTen.RootedCaches.RootedSixBase03.rawCells) Nonrational.OldTerminalMatches.M018.r1214.boundary &&
    Nonrational.InducedTerminalMatches.check Nonrational.OldTerminalMatches.M018.r1214) = true
  rw [Nonrational.OldTerminalMatches.M018.r1214_checked, Bool.and_true]
  decide +kernel

theorem disposition_at_4 : dispositionTest 4 = true := by decide +kernel


theorem disposition_at_5 : dispositionTest 5 = true := by
  change (RawLeafCertificate.boundaryCheck
    ((rawLeaves 5).map Papers.RationalityTen.RootedCaches.RootedSixBase03.rawCells) Nonrational.OldTerminalMatches.M018.r1215.boundary &&
    Nonrational.InducedTerminalMatches.check Nonrational.OldTerminalMatches.M018.r1215) = true
  rw [Nonrational.OldTerminalMatches.M018.r1215_checked, Bool.and_true]
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

theorem dispositionTest_complete : Interval dispositionTest 0 leafCount := (interval_append dispositionTest 0 3 6 (interval_append dispositionTest 0 1 3 disposition_interval_0 (interval_append dispositionTest 1 2 3 disposition_interval_1 disposition_interval_2)) (interval_append dispositionTest 3 4 6 disposition_interval_3 (interval_append dispositionTest 4 5 6 disposition_interval_4 disposition_interval_5)))
theorem disposition_checked (j : Fin leafCount) :
    RawLeafCertificate.check quota ((rawLeaves j.val).map Papers.RationalityTen.RootedCaches.RootedSixBase03.rawCells)
      (disposition j) = true :=
  dispositionTest_complete j.val (Nat.zero_le _) j.isLt

end Papers.RationalityTen.RootedForests.RootedSubsumedForest0671
