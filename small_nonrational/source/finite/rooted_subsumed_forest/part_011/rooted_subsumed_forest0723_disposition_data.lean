module
prelude
public import RootedSubsumedForest0723Data
public import RawLeafCertificate
public import OldTerminalMatches.M022

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0723
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness

def dispositionTable : Table RawLeafCertificate.Certificate :=
(.branch 73
 (.branch 36
 (.branch 18
 (.branch 9
 (.branch 4
 (.branch 2
 (.leaf (.quota 2))
 (.branch 3
 (.leaf (.matching Nonrational.OldTerminalMatches.M022.r1464))
 (.leaf (.quota 2))))
 (.branch 6
 (.branch 5
 (.leaf (.quota 1))
 (.leaf (.quota 2)))
 (.leaf (.quota 2))))
 (.leaf (.quota 2)))
 (.branch 27
 (.leaf (.quota 2))
 (.branch 31
 (.leaf (.quota 2))
 (.branch 33
 (.branch 32
 (.leaf (.quota 1))
 (.leaf (.quota 2)))
 (.leaf (.quota 2))))))
 (.branch 54
 (.branch 45
 (.branch 40
 (.branch 38
 (.branch 37
 (.leaf (.quota 2))
 (.leaf (.quota 1)))
 (.leaf (.quota 2)))
 (.leaf (.quota 2)))
 (.branch 49
 (.branch 47
 (.leaf (.quota 2))
 (.branch 48
 (.leaf (.quota 1))
 (.leaf (.matching Nonrational.OldTerminalMatches.M022.r1465))))
 (.branch 51
 (.branch 50
 (.leaf (.quota 3))
 (.leaf (.quota 2)))
 (.leaf (.quota 2)))))
 (.branch 63
 (.branch 58
 (.branch 56
 (.branch 55
 (.leaf (.quota 2))
 (.leaf (.quota 3)))
 (.leaf (.quota 2)))
 (.branch 60
 (.leaf (.quota 2))
 (.branch 61
 (.leaf (.quota 2))
 (.branch 62
 (.leaf (.quota 3))
 (.leaf (.quota 2))))))
 (.branch 68
 (.branch 65
 (.branch 64
 (.leaf (.quota 2))
 (.leaf (.quota 3)))
 (.branch 66
 (.leaf (.quota 3))
 (.leaf (.quota 2))))
 (.branch 70
 (.leaf (.quota 2))
 (.branch 71
 (.leaf (.quota 2))
 (.branch 72
 (.leaf (.quota 3))
 (.leaf (.quota 2)))))))))
 (.branch 109
 (.branch 91
 (.branch 82
 (.branch 77
 (.branch 75
 (.leaf (.quota 3))
 (.leaf (.quota 2)))
 (.leaf (.quota 2)))
 (.leaf (.quota 2)))
 (.branch 100
 (.branch 95
 (.leaf (.quota 2))
 (.branch 97
 (.leaf (.quota 2))
 (.branch 98
 (.leaf (.matching Nonrational.OldTerminalMatches.M022.r1466))
 (.branch 99
 (.leaf (.quota 1))
 (.leaf (.matching Nonrational.OldTerminalMatches.M022.r1467))))))
 (.branch 104
 (.branch 102
 (.branch 101
 (.leaf (.matching Nonrational.OldTerminalMatches.M022.r1468))
 (.leaf (.quota 2)))
 (.leaf (.quota 2)))
 (.leaf (.quota 2)))))
 (.branch 127
 (.leaf (.quota 2))
 (.branch 136
 (.branch 131
 (.leaf (.quota 2))
 (.branch 133
 (.leaf (.quota 2))
 (.branch 134
 (.leaf (.quota 2))
 (.branch 135
 (.leaf (.quota 2))
 (.leaf (.quota 1))))))
 (.branch 141
 (.branch 138
 (.leaf (.quota 2))
 (.branch 139
 (.leaf (.quota 3))
 (.branch 140
 (.leaf (.quota 2))
 (.leaf (.quota 3)))))
 (.branch 143
 (.branch 142
 (.leaf (.quota 2))
 (.leaf (.quota 1)))
 (.branch 144
 (.leaf (.quota 1))
 (.branch 145
 (.leaf (.quota 3))
 (.leaf (.quota 2))))))))))
def disposition (j : Fin leafCount) := dispositionTable.get j.val
def dispositionTest (i : Nat) : Bool := RawLeafCertificate.check quota
  ((rawLeaves i).map Papers.RationalityTen.RootedCaches.RootedSixBase03.rawCells) (dispositionTable.get i)

end Papers.RationalityTen.RootedForests.RootedSubsumedForest0723
