module
prelude
public import RootedSubsumedForest0857Data
public import RawLeafCertificate
public import OldTerminalMatches.M025

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0857
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness

def dispositionTable : Table RawLeafCertificate.Certificate :=
(.branch 26
 (.branch 13
 (.branch 6
 (.branch 3
 (.branch 1
 (.leaf (.quota 2))
 (.branch 2
 (.leaf (.quota 1))
 (.leaf (.matching Nonrational.OldTerminalMatches.M025.r1638))))
 (.branch 4
 (.leaf (.matching Nonrational.OldTerminalMatches.M025.r1639))
 (.branch 5
 (.leaf (.quota 2))
 (.leaf (.matching Nonrational.OldTerminalMatches.M025.r1640)))))
 (.branch 9
 (.branch 7
 (.leaf (.matching Nonrational.OldTerminalMatches.M025.r1641))
 (.branch 8
 (.leaf (.matching Nonrational.OldTerminalMatches.M025.r1642))
 (.leaf (.matching Nonrational.OldTerminalMatches.M025.r1643))))
 (.branch 11
 (.branch 10
 (.leaf (.matching Nonrational.OldTerminalMatches.M025.r1644))
 (.leaf (.matching Nonrational.OldTerminalMatches.M025.r1645)))
 (.branch 12
 (.leaf (.matching Nonrational.OldTerminalMatches.M025.r1646))
 (.leaf (.quota 2))))))
 (.branch 19
 (.leaf (.quota 2))
 (.branch 22
 (.branch 20
 (.leaf (.quota 2))
 (.leaf (.incidence 4)))
 (.leaf (.quota 2)))))
 (.branch 39
 (.branch 32
 (.branch 29
 (.leaf (.quota 2))
 (.branch 30
 (.leaf (.quota 1))
 (.branch 31
 (.leaf (.quota 1))
 (.leaf (.quota 2)))))
 (.branch 35
 (.leaf (.quota 2))
 (.branch 37
 (.leaf (.quota 2))
 (.branch 38
 (.leaf (.quota 2))
 (.leaf (.incidence 8))))))
 (.branch 45
 (.leaf (.quota 2))
 (.branch 48
 (.branch 46
 (.leaf (.quota 2))
 (.branch 47
 (.leaf (.quota 1))
 (.leaf (.quota 2))))
 (.leaf (.quota 1))))))
def disposition (j : Fin leafCount) := dispositionTable.get j.val
def dispositionTest (i : Nat) : Bool := RawLeafCertificate.check quota
  ((rawLeaves i).map Papers.RationalityTen.RootedCaches.RootedSixExtra05.rawCells) (dispositionTable.get i)

end Papers.RationalityTen.RootedForests.RootedSubsumedForest0857
