module
prelude
public import RootedSubsumedForest0348Data
public import RawLeafCertificate
public import OldTerminalMatches.M011

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0348
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness

def dispositionTable : Table RawLeafCertificate.Certificate :=
(.branch 44
 (.branch 22
 (.branch 11
 (.branch 5
 (.leaf (.quota 2))
 (.branch 8
 (.branch 6
 (.leaf (.quota 2))
 (.branch 7
 (.leaf (.incidence 5))
 (.leaf (.matching Nonrational.OldTerminalMatches.M011.r0725))))
 (.branch 9
 (.leaf (.incidence 5))
 (.branch 10
 (.leaf (.incidence 5))
 (.leaf (.quota 2))))))
 (.branch 16
 (.branch 13
 (.branch 12
 (.leaf (.quota 2))
 (.leaf (.incidence 5)))
 (.leaf (.incidence 5)))
 (.branch 19
 (.branch 17
 (.leaf (.incidence 9))
 (.branch 18
 (.leaf (.matching Nonrational.OldTerminalMatches.M011.r0726))
 (.leaf (.matching Nonrational.OldTerminalMatches.M011.r0727))))
 (.branch 20
 (.leaf (.incidence 5))
 (.branch 21
 (.leaf (.matching Nonrational.OldTerminalMatches.M011.r0728))
 (.leaf (.matching Nonrational.OldTerminalMatches.M011.r0729)))))))
 (.branch 33
 (.branch 27
 (.branch 24
 (.branch 23
 (.leaf (.quota 2))
 (.leaf (.incidence 0)))
 (.leaf (.incidence 0)))
 (.branch 30
 (.branch 28
 (.leaf (.quota 2))
 (.branch 29
 (.leaf (.quota 2))
 (.leaf (.incidence 0))))
 (.leaf (.incidence 0))))
 (.branch 38
 (.branch 35
 (.branch 34
 (.leaf (.quota 2))
 (.leaf (.matching Nonrational.OldTerminalMatches.M011.r0730)))
 (.branch 36
 (.leaf (.incidence 4))
 (.branch 37
 (.leaf (.incidence 5))
 (.leaf (.quota 2)))))
 (.branch 41
 (.branch 39
 (.leaf (.incidence 5))
 (.branch 40
 (.leaf (.incidence 9))
 (.leaf (.quota 1))))
 (.branch 42
 (.leaf (.quota 2))
 (.branch 43
 (.leaf (.matching Nonrational.OldTerminalMatches.M011.r0731))
 (.leaf (.matching Nonrational.OldTerminalMatches.M011.r0732))))))))
 (.branch 66
 (.branch 55
 (.branch 49
 (.branch 46
 (.leaf (.incidence 5))
 (.leaf (.incidence 0)))
 (.branch 52
 (.leaf (.incidence 0))
 (.branch 53
 (.leaf (.quota 2))
 (.branch 54
 (.leaf (.incidence 0))
 (.leaf (.quota 1))))))
 (.branch 60
 (.leaf (.incidence 0))
 (.branch 63
 (.branch 61
 (.leaf (.incidence 0))
 (.branch 62
 (.leaf (.incidence 9))
 (.leaf (.incidence 4))))
 (.branch 64
 (.leaf (.incidence 4))
 (.branch 65
 (.leaf (.quota 2))
 (.leaf (.incidence 5)))))))
 (.branch 77
 (.branch 71
 (.branch 68
 (.leaf (.incidence 6))
 (.branch 69
 (.leaf (.quota 2))
 (.branch 70
 (.leaf (.quota 2))
 (.leaf (.matching Nonrational.OldTerminalMatches.M011.r0733)))))
 (.branch 74
 (.branch 72
 (.leaf (.incidence 8))
 (.branch 73
 (.leaf (.incidence 7))
 (.leaf (.incidence 8))))
 (.branch 75
 (.leaf (.incidence 0))
 (.branch 76
 (.leaf (.quota 1))
 (.leaf (.quota 2))))))
 (.branch 83
 (.branch 80
 (.branch 78
 (.leaf (.quota 2))
 (.branch 79
 (.leaf (.incidence 5))
 (.leaf (.incidence 9))))
 (.branch 81
 (.leaf (.incidence 9))
 (.branch 82
 (.leaf (.incidence 9))
 (.leaf (.quota 1)))))
 (.branch 86
 (.branch 84
 (.leaf (.incidence 6))
 (.branch 85
 (.leaf (.incidence 6))
 (.leaf (.quota 2))))
 (.branch 87
 (.leaf (.incidence 5))
 (.branch 88
 (.leaf (.incidence 5))
 (.leaf (.quota 2)))))))))
def disposition (j : Fin leafCount) := dispositionTable.get j.val
def dispositionTest (i : Nat) : Bool := RawLeafCertificate.check quota
  ((rawLeaves i).map Papers.RationalityTen.RootedCaches.RootedSixBase01.rawCells) (dispositionTable.get i)

end Papers.RationalityTen.RootedForests.RootedSubsumedForest0348
