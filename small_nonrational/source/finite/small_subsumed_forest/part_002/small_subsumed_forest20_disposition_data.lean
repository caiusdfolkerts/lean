module
prelude
public import SmallSubsumedForest20Data
public import RawLeafCertificate
public import OldTerminalMatches.M004
public import OldTerminalMatches.M005

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.SmallRawForests.SmallSubsumedForest20
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness

def dispositionTable : Table RawLeafCertificate.Certificate :=
(.branch 30
 (.branch 15
 (.branch 7
 (.branch 3
 (.branch 1
 (.leaf (.quota 3))
 (.leaf (.quota 2)))
 (.branch 5
 (.leaf (.quota 2))
 (.branch 6
 (.leaf (.quota 2))
 (.leaf (.matching Nonrational.OldTerminalMatches.M004.r0318)))))
 (.branch 11
 (.branch 9
 (.leaf (.quota 2))
 (.branch 10
 (.leaf (.matching Nonrational.OldTerminalMatches.M004.r0319))
 (.leaf .euler)))
 (.branch 13
 (.branch 12
 (.leaf .euler)
 (.leaf (.matching Nonrational.OldTerminalMatches.M005.r0320)))
 (.branch 14
 (.leaf (.incidence 4))
 (.leaf (.quota 2))))))
 (.branch 22
 (.branch 18
 (.branch 16
 (.leaf (.quota 3))
 (.branch 17
 (.leaf (.quota 3))
 (.leaf (.quota 2))))
 (.branch 20
 (.leaf (.quota 2))
 (.branch 21
 (.leaf (.quota 2))
 (.leaf (.matching Nonrational.OldTerminalMatches.M005.r0321)))))
 (.branch 26
 (.branch 24
 (.leaf (.quota 2))
 (.branch 25
 (.leaf .euler)
 (.leaf (.quota 2))))
 (.branch 28
 (.branch 27
 (.leaf (.matching Nonrational.OldTerminalMatches.M005.r0322))
 (.leaf (.quota 1)))
 (.branch 29
 (.leaf (.quota 2))
 (.leaf (.matching Nonrational.OldTerminalMatches.M005.r0323)))))))
 (.branch 45
 (.branch 37
 (.branch 33
 (.branch 31
 (.leaf (.quota 2))
 (.branch 32
 (.leaf (.matching Nonrational.OldTerminalMatches.M005.r0324))
 (.leaf (.quota 2))))
 (.branch 35
 (.leaf (.quota 2))
 (.branch 36
 (.leaf (.quota 1))
 (.leaf (.quota 2)))))
 (.branch 41
 (.branch 39
 (.branch 38
 (.leaf (.matching Nonrational.OldTerminalMatches.M005.r0325))
 (.leaf (.quota 1)))
 (.leaf (.quota 1)))
 (.leaf (.quota 2))))
 (.branch 53
 (.branch 49
 (.branch 47
 (.leaf (.quota 2))
 (.branch 48
 (.leaf (.quota 2))
 (.leaf (.quota 1))))
 (.branch 51
 (.branch 50
 (.leaf (.quota 1))
 (.leaf (.quota 3)))
 (.branch 52
 (.leaf (.quota 2))
 (.leaf (.quota 1)))))
 (.branch 57
 (.branch 55
 (.branch 54
 (.leaf (.quota 3))
 (.leaf (.quota 2)))
 (.branch 56
 (.leaf (.quota 1))
 (.leaf (.quota 2))))
 (.branch 59
 (.branch 58
 (.leaf .euler)
 (.leaf (.quota 1)))
 (.branch 60
 (.leaf (.quota 2))
 (.leaf (.incidence 3))))))))
def disposition (j : Fin leafCount) := dispositionTable.get j.val
def dispositionTest (i : Nat) : Bool := RawLeafCertificate.check quota
  ((rawLeaves i).map RootedSmallCache.rawCells) (dispositionTable.get i)

end Papers.RationalityTen.SmallRawForests.SmallSubsumedForest20
