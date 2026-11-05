module
prelude
public import RootedSubsumedForest0363Data
public import RawLeafCertificate
public import OldTerminalMatches.M017

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0363
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness

def dispositionTable : Table RawLeafCertificate.Certificate :=
(.leaf (.matching Nonrational.OldTerminalMatches.M017.r1120))
def disposition (j : Fin leafCount) := dispositionTable.get j.val
def dispositionTest (i : Nat) : Bool := RawLeafCertificate.check quota
  ((rawLeaves i).map Papers.RationalityTen.RootedCaches.RootedSixBase02.rawCells) (dispositionTable.get i)

theorem disposition_at_0 : dispositionTest 0 = true := by
  change (RawLeafCertificate.boundaryCheck
    ((rawLeaves 0).map Papers.RationalityTen.RootedCaches.RootedSixBase02.rawCells) Nonrational.OldTerminalMatches.M017.r1120.boundary &&
    Nonrational.InducedTerminalMatches.check Nonrational.OldTerminalMatches.M017.r1120) = true
  rw [Nonrational.OldTerminalMatches.M017.r1120_checked, Bool.and_true]
  decide +kernel

theorem disposition_interval_0 : Interval dispositionTest 0 1 := by
  intro i hlo hhi
  have h : i = 0 := by omega
  subst i
  exact disposition_at_0

theorem dispositionTest_complete : Interval dispositionTest 0 leafCount := disposition_interval_0
theorem disposition_checked (j : Fin leafCount) :
    RawLeafCertificate.check quota ((rawLeaves j.val).map Papers.RationalityTen.RootedCaches.RootedSixBase02.rawCells)
      (disposition j) = true :=
  dispositionTest_complete j.val (Nat.zero_le _) j.isLt

end Papers.RationalityTen.RootedForests.RootedSubsumedForest0363
