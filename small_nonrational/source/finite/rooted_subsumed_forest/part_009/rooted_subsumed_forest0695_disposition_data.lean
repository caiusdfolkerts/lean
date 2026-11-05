module
prelude
public import RootedSubsumedForest0695Data
public import RawLeafCertificate
public import OldTerminalMatches.M019

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0695
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness

def dispositionTable : Table RawLeafCertificate.Certificate :=
(.branch 69
 (.branch 34
 (.branch 17
 (.branch 8
 (.branch 4
 (.branch 2
 (.branch 1
 (.leaf (.quota 2))
 (.leaf (.matching Nonrational.OldTerminalMatches.M019.r1216)))
 (.branch 3
 (.leaf (.quota 2))
 (.leaf (.quota 1))))
 (.leaf (.quota 2)))
 (.branch 12
 (.leaf (.quota 2))
 (.branch 14
 (.branch 13
 (.leaf (.quota 3))
 (.leaf (.quota 2)))
 (.branch 15
 (.leaf (.quota 2))
 (.branch 16
 (.leaf (.quota 2))
 (.leaf (.quota 3)))))))
 (.branch 25
 (.branch 21
 (.branch 19
 (.leaf (.quota 2))
 (.branch 20
 (.leaf (.quota 2))
 (.leaf (.quota 1))))
 (.branch 23
 (.leaf (.quota 2))
 (.branch 24
 (.leaf (.quota 1))
 (.leaf (.quota 2)))))
 (.branch 29
 (.leaf (.quota 2))
 (.branch 31
 (.leaf (.quota 2))
 (.branch 32
 (.leaf (.quota 2))
 (.branch 33
 (.leaf (.quota 1))
 (.leaf (.quota 2))))))))
 (.branch 51
 (.branch 42
 (.branch 38
 (.leaf (.quota 2))
 (.branch 40
 (.leaf (.quota 2))
 (.branch 41
 (.leaf (.matching Nonrational.OldTerminalMatches.M019.r1217))
 (.leaf (.matching Nonrational.OldTerminalMatches.M019.r1218)))))
 (.leaf (.quota 2)))
 (.leaf (.quota 2))))
 (.branch 103
 (.branch 86
 (.branch 77
 (.leaf (.quota 2))
 (.branch 81
 (.leaf (.quota 2))
 (.branch 83
 (.leaf (.quota 2))
 (.branch 84
 (.leaf (.matching Nonrational.OldTerminalMatches.M019.r1219))
 (.branch 85
 (.leaf (.quota 1))
 (.leaf (.matching Nonrational.OldTerminalMatches.M019.r1220)))))))
 (.branch 94
 (.branch 90
 (.branch 88
 (.branch 87
 (.leaf (.quota 2))
 (.leaf (.matching Nonrational.OldTerminalMatches.M019.r1221)))
 (.branch 89
 (.leaf (.quota 2))
 (.leaf (.matching Nonrational.OldTerminalMatches.M019.r1222))))
 (.leaf (.quota 2)))
 (.branch 98
 (.branch 96
 (.branch 95
 (.leaf (.quota 2))
 (.leaf (.quota 3)))
 (.leaf (.quota 2)))
 (.branch 100
 (.leaf (.quota 2))
 (.branch 101
 (.leaf (.quota 2))
 (.branch 102
 (.leaf (.quota 2))
 (.leaf (.quota 1))))))))
 (.branch 120
 (.branch 111
 (.branch 107
 (.leaf (.quota 2))
 (.branch 109
 (.branch 108
 (.leaf (.matching Nonrational.OldTerminalMatches.M019.r1223))
 (.leaf (.quota 2)))
 (.leaf (.quota 2))))
 (.leaf (.quota 2)))
 (.branch 129
 (.leaf (.quota 2))
 (.branch 133
 (.leaf (.quota 2))
 (.branch 135
 (.branch 134
 (.leaf (.quota 2))
 (.leaf (.matching Nonrational.OldTerminalMatches.M019.r1224)))
 (.branch 136
 (.leaf (.matching Nonrational.OldTerminalMatches.M019.r1225))
 (.branch 137
 (.leaf (.matching Nonrational.OldTerminalMatches.M019.r1226))
 (.leaf (.quota 2))))))))))
def disposition (j : Fin leafCount) := dispositionTable.get j.val
def dispositionTest (i : Nat) : Bool := RawLeafCertificate.check quota
  ((rawLeaves i).map Papers.RationalityTen.RootedCaches.RootedSixBase03.rawCells) (dispositionTable.get i)

end Papers.RationalityTen.RootedForests.RootedSubsumedForest0695
