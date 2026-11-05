module
prelude
public import RootedSubsumedForest0305Data
public import RawLeafCertificate
public import OldTerminalMatches.M006

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0305
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness

def dispositionTable : Table RawLeafCertificate.Certificate :=
(.branch 46
 (.branch 23
 (.branch 11
 (.branch 5
 (.branch 2
 (.leaf (.quota 6))
 (.leaf (.quota 2)))
 (.branch 8
 (.branch 6
 (.leaf (.quota 2))
 (.leaf (.quota 6)))
 (.leaf (.quota 6))))
 (.branch 17
 (.branch 14
 (.branch 12
 (.leaf (.quota 6))
 (.leaf (.quota 1)))
 (.leaf (.quota 2)))
 (.leaf (.quota 2))))
 (.branch 34
 (.branch 28
 (.branch 25
 (.leaf (.quota 1))
 (.leaf (.quota 2)))
 (.leaf (.quota 2)))
 (.branch 40
 (.branch 37
 (.branch 35
 (.leaf (.quota 2))
 (.branch 36
 (.leaf (.quota 1))
 (.leaf (.quota 2))))
 (.branch 38
 (.leaf (.quota 2))
 (.branch 39
 (.leaf (.quota 1))
 (.leaf (.quota 2)))))
 (.leaf (.quota 2)))))
 (.branch 69
 (.branch 57
 (.branch 51
 (.leaf (.quota 2))
 (.branch 54
 (.leaf (.quota 2))
 (.branch 55
 (.leaf (.quota 2))
 (.branch 56
 (.leaf (.quota 2))
 (.leaf (.quota 1))))))
 (.branch 63
 (.branch 60
 (.leaf (.quota 2))
 (.branch 61
 (.leaf (.quota 1))
 (.branch 62
 (.leaf (.quota 2))
 (.leaf (.matching Nonrational.OldTerminalMatches.M006.r0444)))))
 (.branch 66
 (.branch 64
 (.leaf (.matching Nonrational.OldTerminalMatches.M006.r0445))
 (.branch 65
 (.leaf (.matching Nonrational.OldTerminalMatches.M006.r0446))
 (.leaf (.matching Nonrational.OldTerminalMatches.M006.r0447))))
 (.leaf (.quota 1)))))
 (.branch 81
 (.leaf (.quota 2))
 (.branch 87
 (.leaf (.quota 2))
 (.branch 90
 (.leaf (.quota 2))
 (.branch 91
 (.leaf (.quota 1))
 (.branch 92
 (.leaf (.quota 1))
 (.leaf (.quota 2)))))))))
def disposition (j : Fin leafCount) := dispositionTable.get j.val
def dispositionTest (i : Nat) : Bool := RawLeafCertificate.check quota
  ((rawLeaves i).map Papers.RationalityTen.RootedCaches.RootedSixBase02.rawCells) (dispositionTable.get i)

end Papers.RationalityTen.RootedForests.RootedSubsumedForest0305
