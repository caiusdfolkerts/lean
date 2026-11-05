module
prelude
public import RootedSubsumedForest0865Data
public import RawLeafCertificate
public import OldTerminalMatches.M025

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0865
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
 (.leaf (.quota 9))
 (.leaf (.quota 1)))
 (.branch 3
 (.leaf (.quota 1))
 (.leaf (.quota 2))))
 (.branch 6
 (.branch 5
 (.leaf (.quota 1))
 (.leaf (.quota 2)))
 (.branch 7
 (.leaf (.quota 2))
 (.branch 8
 (.leaf (.quota 1))
 (.leaf (.quota 2))))))
 (.branch 13
 (.branch 11
 (.branch 10
 (.leaf (.quota 9))
 (.leaf (.quota 1)))
 (.leaf (.quota 9)))
 (.branch 15
 (.leaf (.quota 9))
 (.branch 16
 (.leaf (.quota 2))
 (.branch 17
 (.leaf (.quota 3))
 (.leaf (.quota 2)))))))
 (.branch 27
 (.branch 22
 (.branch 20
 (.branch 19
 (.leaf (.quota 1))
 (.leaf (.quota 3)))
 (.branch 21
 (.leaf (.quota 1))
 (.leaf (.matching Nonrational.OldTerminalMatches.M025.r1649))))
 (.branch 24
 (.branch 23
 (.leaf (.quota 2))
 (.leaf (.quota 1)))
 (.branch 25
 (.leaf (.matching Nonrational.OldTerminalMatches.M025.r1650))
 (.branch 26
 (.leaf (.quota 2))
 (.leaf (.quota 1))))))
 (.branch 31
 (.branch 29
 (.branch 28
 (.leaf (.quota 3))
 (.leaf (.quota 1)))
 (.branch 30
 (.leaf (.quota 2))
 (.leaf (.quota 3))))
 (.branch 33
 (.leaf (.quota 1))
 (.branch 34
 (.leaf (.quota 2))
 (.branch 35
 (.leaf (.quota 1))
 (.leaf (.matching Nonrational.OldTerminalMatches.M025.r1651))))))))
def disposition (j : Fin leafCount) := dispositionTable.get j.val
def dispositionTest (i : Nat) : Bool := RawLeafCertificate.check quota
  ((rawLeaves i).map Papers.RationalityTen.RootedCaches.RootedSixExtra05.rawCells) (dispositionTable.get i)

end Papers.RationalityTen.RootedForests.RootedSubsumedForest0865
