module
prelude
public import RootedSubsumedForest0858Data
public import RawLeafCertificate
public import OldTerminalMatches.M025

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0858
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness

def dispositionTable : Table RawLeafCertificate.Certificate :=
(.branch 25
 (.branch 12
 (.branch 6
 (.branch 3
 (.branch 1
 (.leaf (.matching Nonrational.OldTerminalMatches.M025.r1647))
 (.branch 2
 (.leaf (.matching Nonrational.OldTerminalMatches.M025.r1648))
 (.leaf (.quota 1))))
 (.leaf (.quota 2)))
 (.leaf (.quota 2)))
 (.branch 18
 (.branch 15
 (.branch 13
 (.leaf (.quota 1))
 (.leaf (.quota 2)))
 (.branch 16
 (.leaf (.quota 2))
 (.branch 17
 (.leaf (.quota 2))
 (.leaf (.quota 1)))))
 (.branch 21
 (.branch 19
 (.leaf (.quota 2))
 (.branch 20
 (.leaf (.quota 3))
 (.leaf (.quota 2))))
 (.branch 23
 (.branch 22
 (.leaf (.quota 3))
 (.leaf (.quota 2)))
 (.leaf (.quota 2))))))
 (.branch 37
 (.leaf (.quota 2))
 (.branch 43
 (.branch 40
 (.leaf (.quota 2))
 (.branch 41
 (.leaf (.quota 2))
 (.branch 42
 (.leaf (.quota 2))
 (.leaf (.quota 3)))))
 (.branch 46
 (.branch 44
 (.leaf (.quota 2))
 (.branch 45
 (.leaf (.quota 3))
 (.leaf (.quota 2))))
 (.leaf (.quota 2))))))
def disposition (j : Fin leafCount) := dispositionTable.get j.val
def dispositionTest (i : Nat) : Bool := RawLeafCertificate.check quota
  ((rawLeaves i).map Papers.RationalityTen.RootedCaches.RootedSixExtra06.rawCells) (dispositionTable.get i)

end Papers.RationalityTen.RootedForests.RootedSubsumedForest0858
