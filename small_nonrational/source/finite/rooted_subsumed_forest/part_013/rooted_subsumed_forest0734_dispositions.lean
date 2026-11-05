module
prelude
public import RootedSubsumedForest0734Data
public import RawLeafCertificate
public import OldTerminalMatches.M024

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0734
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness

def dispositionTable : Table RawLeafCertificate.Certificate :=
(.branch 1
 (.leaf (.quota 2))
 (.branch 2
 (.leaf (.quota 2))
 (.leaf (.matching Nonrational.OldTerminalMatches.M024.r1586))))
def disposition (j : Fin leafCount) := dispositionTable.get j.val
def dispositionTest (i : Nat) : Bool := RawLeafCertificate.check quota
  ((rawLeaves i).map Papers.RationalityTen.RootedCaches.RootedSixBase04.rawCells) (dispositionTable.get i)
theorem disposition_at_0 : dispositionTest 0 = true := by decide +kernel

theorem disposition_at_1 : dispositionTest 1 = true := by decide +kernel


theorem disposition_at_2 : dispositionTest 2 = true := by
  change (RawLeafCertificate.boundaryCheck
    ((rawLeaves 2).map Papers.RationalityTen.RootedCaches.RootedSixBase04.rawCells) Nonrational.OldTerminalMatches.M024.r1586.boundary &&
    Nonrational.InducedTerminalMatches.check Nonrational.OldTerminalMatches.M024.r1586) = true
  rw [Nonrational.OldTerminalMatches.M024.r1586_checked, Bool.and_true]
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

theorem dispositionTest_complete : Interval dispositionTest 0 leafCount := (interval_append dispositionTest 0 1 3 disposition_interval_0 (interval_append dispositionTest 1 2 3 disposition_interval_1 disposition_interval_2))
theorem disposition_checked (j : Fin leafCount) :
    RawLeafCertificate.check quota ((rawLeaves j.val).map Papers.RationalityTen.RootedCaches.RootedSixBase04.rawCells)
      (disposition j) = true :=
  dispositionTest_complete j.val (Nat.zero_le _) j.isLt

end Papers.RationalityTen.RootedForests.RootedSubsumedForest0734
