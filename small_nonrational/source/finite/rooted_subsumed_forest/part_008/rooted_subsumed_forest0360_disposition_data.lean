module
prelude
public import RootedSubsumedForest0360Data
public import RawLeafCertificate
public import OldTerminalMatches.M017

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0360
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness

def dispositionTable : Table RawLeafCertificate.Certificate :=
(.branch 27
 (.branch 13
 (.branch 6
 (.branch 3
 (.branch 1
 (.leaf (.matching Nonrational.OldTerminalMatches.M017.r1103))
 (.branch 2
 (.leaf (.incidence 0))
 (.leaf (.incidence 5))))
 (.branch 4
 (.leaf (.incidence 5))
 (.branch 5
 (.leaf (.quota 2))
 (.leaf (.incidence 5)))))
 (.branch 9
 (.branch 7
 (.leaf (.incidence 5))
 (.branch 8
 (.leaf (.incidence 7))
 (.leaf (.incidence 9))))
 (.branch 11
 (.leaf (.incidence 5))
 (.branch 12
 (.leaf (.incidence 5))
 (.leaf (.quota 2))))))
 (.branch 20
 (.branch 16
 (.branch 14
 (.leaf (.incidence 5))
 (.branch 15
 (.leaf (.incidence 5))
 (.leaf (.quota 1))))
 (.branch 18
 (.leaf (.incidence 5))
 (.branch 19
 (.leaf (.incidence 5))
 (.leaf (.quota 1)))))
 (.branch 23
 (.leaf (.incidence 5))
 (.branch 25
 (.branch 24
 (.leaf (.incidence 5))
 (.leaf (.quota 1)))
 (.leaf (.quota 1))))))
 (.branch 41
 (.branch 34
 (.branch 30
 (.branch 28
 (.leaf (.quota 2))
 (.branch 29
 (.leaf (.quota 2))
 (.leaf (.incidence 5))))
 (.branch 32
 (.leaf (.quota 1))
 (.branch 33
 (.leaf (.incidence 5))
 (.leaf (.matching Nonrational.OldTerminalMatches.M017.r1104)))))
 (.branch 37
 (.branch 35
 (.leaf (.quota 2))
 (.branch 36
 (.leaf (.incidence 6))
 (.leaf (.matching Nonrational.OldTerminalMatches.M017.r1105))))
 (.branch 39
 (.branch 38
 (.leaf (.matching Nonrational.OldTerminalMatches.M017.r1106))
 (.leaf (.quota 2)))
 (.branch 40
 (.leaf (.incidence 0))
 (.leaf (.incidence 5))))))
 (.branch 48
 (.branch 44
 (.branch 42
 (.leaf (.incidence 5))
 (.branch 43
 (.leaf (.incidence 5))
 (.leaf (.incidence 0))))
 (.branch 46
 (.branch 45
 (.leaf (.matching Nonrational.OldTerminalMatches.M017.r1107))
 (.leaf (.matching Nonrational.OldTerminalMatches.M017.r1108)))
 (.branch 47
 (.leaf (.matching Nonrational.OldTerminalMatches.M017.r1109))
 (.leaf (.matching Nonrational.OldTerminalMatches.M017.r1110)))))
 (.branch 51
 (.branch 49
 (.leaf (.matching Nonrational.OldTerminalMatches.M017.r1111))
 (.leaf (.quota 2)))
 (.leaf (.quota 2))))))
def disposition (j : Fin leafCount) := dispositionTable.get j.val
def dispositionTest (i : Nat) : Bool := RawLeafCertificate.check quota
  ((rawLeaves i).map Papers.RationalityTen.RootedCaches.RootedSixBase02.rawCells) (dispositionTable.get i)

end Papers.RationalityTen.RootedForests.RootedSubsumedForest0360
