module
prelude
public import RootedSubsumedForest0311Data
public import RawLeafCertificate
public import OldTerminalMatches.M007

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0311
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness

def dispositionTable : Table RawLeafCertificate.Certificate :=
(.branch 21
 (.branch 10
 (.branch 5
 (.branch 2
 (.branch 1
 (.leaf (.quota 2))
 (.leaf (.quota 3)))
 (.branch 3
 (.leaf (.quota 3))
 (.branch 4
 (.leaf (.quota 2))
 (.leaf (.matching Nonrational.OldTerminalMatches.M007.r0470)))))
 (.branch 7
 (.branch 6
 (.leaf (.quota 2))
 (.leaf (.quota 1)))
 (.leaf (.quota 2))))
 (.branch 15
 (.branch 12
 (.leaf (.quota 2))
 (.branch 13
 (.leaf (.quota 1))
 (.leaf (.quota 2))))
 (.branch 18
 (.leaf (.quota 2))
 (.branch 19
 (.leaf (.quota 2))
 (.branch 20
 (.leaf (.incidence 4))
 (.leaf (.matching Nonrational.OldTerminalMatches.M007.r0471)))))))
 (.branch 31
 (.branch 26
 (.branch 23
 (.branch 22
 (.leaf (.matching Nonrational.OldTerminalMatches.M007.r0472))
 (.leaf (.matching Nonrational.OldTerminalMatches.M007.r0473)))
 (.branch 24
 (.leaf (.matching Nonrational.OldTerminalMatches.M007.r0474))
 (.branch 25
 (.leaf (.matching Nonrational.OldTerminalMatches.M007.r0475))
 (.leaf (.quota 2)))))
 (.branch 28
 (.leaf (.quota 2))
 (.branch 29
 (.leaf (.matching Nonrational.OldTerminalMatches.M007.r0476))
 (.branch 30
 (.leaf (.matching Nonrational.OldTerminalMatches.M007.r0477))
 (.leaf (.matching Nonrational.OldTerminalMatches.M007.r0478))))))
 (.branch 36
 (.branch 33
 (.branch 32
 (.leaf (.matching Nonrational.OldTerminalMatches.M007.r0479))
 (.leaf (.matching Nonrational.OldTerminalMatches.M007.r0480)))
 (.branch 34
 (.leaf (.matching Nonrational.OldTerminalMatches.M007.r0481))
 (.branch 35
 (.leaf (.matching Nonrational.OldTerminalMatches.M007.r0482))
 (.leaf (.matching Nonrational.OldTerminalMatches.M007.r0483)))))
 (.branch 39
 (.branch 37
 (.leaf (.matching Nonrational.OldTerminalMatches.M007.r0484))
 (.branch 38
 (.leaf (.matching Nonrational.OldTerminalMatches.M007.r0485))
 (.leaf (.quota 2))))
 (.leaf (.quota 2))))))
def disposition (j : Fin leafCount) := dispositionTable.get j.val
def dispositionTest (i : Nat) : Bool := RawLeafCertificate.check quota
  ((rawLeaves i).map Papers.RationalityTen.RootedCaches.RootedSixBase01.rawCells) (dispositionTable.get i)

end Papers.RationalityTen.RootedForests.RootedSubsumedForest0311
