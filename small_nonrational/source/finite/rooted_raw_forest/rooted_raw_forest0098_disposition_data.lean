module
prelude
public import RootedRawForest0098Data
public import RawLeafCertificate
public import OldTerminalMatches.M000

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedRawForest0098
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness

def dispositionTable : Table RawLeafCertificate.Certificate :=
(.branch 18
 (.branch 9
 (.branch 4
 (.branch 2
 (.branch 1
 (.leaf (.quota 2))
 (.leaf (.incidence 0)))
 (.branch 3
 (.leaf (.matching Nonrational.OldTerminalMatches.M000.r0000))
 (.leaf (.quota 2))))
 (.branch 6
 (.branch 5
 (.leaf (.matching Nonrational.OldTerminalMatches.M000.r0001))
 (.leaf (.incidence 6)))
 (.branch 7
 (.leaf (.quota 2))
 (.branch 8
 (.leaf (.incidence 0))
 (.leaf (.matching Nonrational.OldTerminalMatches.M000.r0002))))))
 (.branch 13
 (.branch 11
 (.branch 10
 (.leaf (.quota 2))
 (.leaf (.matching Nonrational.OldTerminalMatches.M000.r0003)))
 (.branch 12
 (.leaf (.incidence 6))
 (.leaf (.quota 2))))
 (.branch 15
 (.branch 14
 (.leaf (.incidence 0))
 (.leaf (.matching Nonrational.OldTerminalMatches.M000.r0004)))
 (.branch 16
 (.leaf (.quota 2))
 (.branch 17
 (.leaf (.matching Nonrational.OldTerminalMatches.M000.r0005))
 (.leaf (.incidence 6)))))))
 (.branch 27
 (.branch 22
 (.branch 20
 (.branch 19
 (.leaf (.matching Nonrational.OldTerminalMatches.M000.r0006))
 (.leaf (.incidence 6)))
 (.branch 21
 (.leaf (.quota 2))
 (.leaf (.incidence 0))))
 (.branch 24
 (.branch 23
 (.leaf (.matching Nonrational.OldTerminalMatches.M000.r0007))
 (.leaf (.quota 2)))
 (.branch 25
 (.leaf (.matching Nonrational.OldTerminalMatches.M000.r0008))
 (.branch 26
 (.leaf (.incidence 6))
 (.leaf (.quota 2))))))
 (.branch 31
 (.branch 29
 (.branch 28
 (.leaf (.incidence 0))
 (.leaf (.matching Nonrational.OldTerminalMatches.M000.r0009)))
 (.branch 30
 (.leaf (.quota 2))
 (.leaf (.matching Nonrational.OldTerminalMatches.M000.r0010))))
 (.branch 33
 (.branch 32
 (.leaf (.incidence 6))
 (.leaf (.quota 2)))
 (.branch 34
 (.leaf (.incidence 0))
 (.branch 35
 (.leaf (.matching Nonrational.OldTerminalMatches.M000.r0011))
 (.leaf (.quota 2))))))))
def disposition (j : Fin leafCount) := dispositionTable.get j.val
def dispositionTest (i : Nat) : Bool := RawLeafCertificate.check quota
  ((rawLeaves i).map Papers.RationalityTen.RootedCaches.RootedSevenPure064.rawCells) (dispositionTable.get i)

end Papers.RationalityTen.RootedForests.RootedRawForest0098
