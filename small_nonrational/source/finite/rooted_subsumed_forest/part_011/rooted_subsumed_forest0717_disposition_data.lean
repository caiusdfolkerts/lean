module
prelude
public import RootedSubsumedForest0717Data
public import RawLeafCertificate
public import OldTerminalMatches.M020

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0717
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
 (.leaf (.incidence 4))
 (.branch 3
 (.leaf (.incidence 0))
 (.branch 4
 (.leaf (.incidence 4))
 (.leaf (.matching Nonrational.OldTerminalMatches.M020.r1283)))))
 (.branch 8
 (.branch 6
 (.leaf (.matching Nonrational.OldTerminalMatches.M020.r1284))
 (.branch 7
 (.leaf (.incidence 4))
 (.leaf (.incidence 0))))
 (.branch 9
 (.leaf (.matching Nonrational.OldTerminalMatches.M020.r1285))
 (.branch 10
 (.leaf (.quota 1))
 (.leaf (.incidence 9))))))
 (.branch 17
 (.branch 14
 (.branch 12
 (.leaf (.incidence 9))
 (.branch 13
 (.leaf (.incidence 4))
 (.leaf (.matching Nonrational.OldTerminalMatches.M020.r1286))))
 (.branch 15
 (.leaf (.matching Nonrational.OldTerminalMatches.M020.r1287))
 (.branch 16
 (.leaf (.matching Nonrational.OldTerminalMatches.M020.r1288))
 (.leaf (.quota 2)))))
 (.branch 20
 (.branch 18
 (.leaf (.matching Nonrational.OldTerminalMatches.M020.r1289))
 (.branch 19
 (.leaf (.matching Nonrational.OldTerminalMatches.M020.r1290))
 (.leaf (.matching Nonrational.OldTerminalMatches.M020.r1291))))
 (.branch 21
 (.leaf (.incidence 9))
 (.branch 22
 (.leaf (.matching Nonrational.OldTerminalMatches.M020.r1292))
 (.leaf (.quota 2)))))))
 (.branch 34
 (.branch 28
 (.branch 25
 (.branch 24
 (.leaf (.quota 1))
 (.leaf (.incidence 9)))
 (.branch 26
 (.leaf (.incidence 4))
 (.branch 27
 (.leaf (.matching Nonrational.OldTerminalMatches.M020.r1293))
 (.leaf (.matching Nonrational.OldTerminalMatches.M020.r1294)))))
 (.branch 31
 (.branch 29
 (.leaf (.matching Nonrational.OldTerminalMatches.M020.r1295))
 (.leaf (.incidence 4)))
 (.leaf (.incidence 4))))
 (.branch 40
 (.branch 37
 (.branch 35
 (.leaf (.matching Nonrational.OldTerminalMatches.M020.r1296))
 (.leaf (.incidence 4)))
 (.branch 38
 (.leaf (.incidence 7))
 (.leaf (.incidence 4))))
 (.branch 43
 (.leaf (.incidence 4))
 (.branch 44
 (.leaf (.incidence 4))
 (.branch 45
 (.leaf (.quota 1))
 (.leaf (.quota 2))))))))
 (.branch 69
 (.branch 57
 (.branch 51
 (.branch 48
 (.branch 47
 (.leaf (.incidence 6))
 (.leaf (.incidence 7)))
 (.branch 49
 (.leaf (.incidence 4))
 (.branch 50
 (.leaf (.quota 2))
 (.leaf (.incidence 0)))))
 (.branch 54
 (.branch 52
 (.leaf (.incidence 0))
 (.leaf (.quota 2)))
 (.leaf (.quota 2))))
 (.branch 63
 (.branch 60
 (.branch 58
 (.leaf (.quota 2))
 (.leaf (.incidence 0)))
 (.branch 61
 (.leaf (.quota 1))
 (.branch 62
 (.leaf (.matching Nonrational.OldTerminalMatches.M020.r1297))
 (.leaf (.matching Nonrational.OldTerminalMatches.M020.r1298)))))
 (.branch 66
 (.branch 64
 (.leaf (.matching Nonrational.OldTerminalMatches.M020.r1299))
 (.branch 65
 (.leaf (.quota 1))
 (.leaf (.incidence 4))))
 (.branch 67
 (.leaf (.matching Nonrational.OldTerminalMatches.M020.r1300))
 (.leaf (.incidence 4))))))
 (.branch 80
 (.branch 74
 (.branch 71
 (.branch 70
 (.leaf (.incidence 0))
 (.leaf (.incidence 4)))
 (.branch 72
 (.leaf (.incidence 4))
 (.branch 73
 (.leaf (.matching Nonrational.OldTerminalMatches.M020.r1301))
 (.leaf (.incidence 4)))))
 (.branch 77
 (.branch 75
 (.leaf (.incidence 4))
 (.leaf (.incidence 0)))
 (.leaf (.incidence 4))))
 (.branch 86
 (.branch 83
 (.branch 81
 (.leaf (.quota 2))
 (.branch 82
 (.leaf (.quota 1))
 (.leaf (.incidence 0))))
 (.branch 84
 (.leaf (.incidence 0))
 (.branch 85
 (.leaf (.quota 1))
 (.leaf (.incidence 0)))))
 (.branch 89
 (.branch 87
 (.leaf (.incidence 0))
 (.branch 88
 (.leaf (.incidence 0))
 (.leaf (.quota 2))))
 (.branch 90
 (.leaf (.quota 2))
 (.branch 91
 (.leaf (.quota 1))
 (.leaf (.quota 2)))))))))
def disposition (j : Fin leafCount) := dispositionTable.get j.val
def dispositionTest (i : Nat) : Bool := RawLeafCertificate.check quota
  ((rawLeaves i).map Papers.RationalityTen.RootedCaches.RootedSixBase03.rawCells) (dispositionTable.get i)

end Papers.RationalityTen.RootedForests.RootedSubsumedForest0717
