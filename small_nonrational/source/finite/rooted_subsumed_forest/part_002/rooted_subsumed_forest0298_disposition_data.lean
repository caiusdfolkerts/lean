module
prelude
public import RootedSubsumedForest0298Data
public import RawLeafCertificate
public import OldTerminalMatches.M005

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0298
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness

def dispositionTable : Table RawLeafCertificate.Certificate :=
(.branch 21
 (.branch 10
 (.branch 5
 (.branch 2
 (.leaf (.quota 2))
 (.branch 3
 (.leaf (.matching Nonrational.OldTerminalMatches.M005.r0361))
 (.branch 4
 (.leaf (.matching Nonrational.OldTerminalMatches.M005.r0362))
 (.leaf (.quota 2)))))
 (.branch 7
 (.branch 6
 (.leaf (.quota 2))
 (.leaf (.quota 6)))
 (.leaf (.quota 2))))
 (.branch 15
 (.branch 12
 (.leaf (.quota 2))
 (.branch 13
 (.leaf (.matching Nonrational.OldTerminalMatches.M005.r0363))
 (.branch 14
 (.leaf (.matching Nonrational.OldTerminalMatches.M005.r0364))
 (.leaf (.matching Nonrational.OldTerminalMatches.M005.r0365)))))
 (.branch 18
 (.branch 16
 (.leaf (.quota 6))
 (.branch 17
 (.leaf (.quota 2))
 (.leaf (.quota 6))))
 (.branch 19
 (.leaf (.quota 2))
 (.branch 20
 (.leaf (.matching Nonrational.OldTerminalMatches.M005.r0366))
 (.leaf (.matching Nonrational.OldTerminalMatches.M005.r0367)))))))
 (.branch 32
 (.branch 26
 (.branch 23
 (.leaf (.quota 2))
 (.branch 24
 (.leaf (.quota 2))
 (.branch 25
 (.leaf (.quota 2))
 (.leaf (.matching Nonrational.OldTerminalMatches.M005.r0368)))))
 (.branch 29
 (.branch 27
 (.leaf (.matching Nonrational.OldTerminalMatches.M005.r0369))
 (.branch 28
 (.leaf (.matching Nonrational.OldTerminalMatches.M005.r0370))
 (.leaf (.matching Nonrational.OldTerminalMatches.M005.r0371))))
 (.branch 30
 (.leaf (.matching Nonrational.OldTerminalMatches.M005.r0372))
 (.branch 31
 (.leaf (.matching Nonrational.OldTerminalMatches.M005.r0373))
 (.leaf (.matching Nonrational.OldTerminalMatches.M005.r0374))))))
 (.branch 37
 (.branch 34
 (.branch 33
 (.leaf (.matching Nonrational.OldTerminalMatches.M005.r0375))
 (.leaf (.quota 2)))
 (.branch 35
 (.leaf (.matching Nonrational.OldTerminalMatches.M005.r0376))
 (.branch 36
 (.leaf (.matching Nonrational.OldTerminalMatches.M005.r0377))
 (.leaf (.matching Nonrational.OldTerminalMatches.M005.r0378)))))
 (.branch 40
 (.branch 38
 (.leaf (.matching Nonrational.OldTerminalMatches.M005.r0379))
 (.leaf (.quota 2)))
 (.branch 41
 (.leaf (.matching Nonrational.OldTerminalMatches.M005.r0380))
 (.branch 42
 (.leaf (.matching Nonrational.OldTerminalMatches.M005.r0381))
 (.leaf (.quota 2))))))))
def disposition (j : Fin leafCount) := dispositionTable.get j.val
def dispositionTest (i : Nat) : Bool := RawLeafCertificate.check quota
  ((rawLeaves i).map Papers.RationalityTen.RootedCaches.RootedSixBase00.rawCells) (dispositionTable.get i)

end Papers.RationalityTen.RootedForests.RootedSubsumedForest0298
