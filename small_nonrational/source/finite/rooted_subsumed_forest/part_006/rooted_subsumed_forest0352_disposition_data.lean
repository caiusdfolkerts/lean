module
prelude
public import RootedSubsumedForest0352Data
public import RawLeafCertificate
public import OldTerminalMatches.M011

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0352
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness

def dispositionTable : Table RawLeafCertificate.Certificate :=
(.branch 76
 (.branch 38
 (.branch 19
 (.branch 9
 (.branch 4
 (.leaf (.quota 2))
 (.branch 6
 (.branch 5
 (.leaf (.quota 2))
 (.leaf (.quota 1)))
 (.leaf (.quota 2))))
 (.leaf (.quota 2)))
 (.branch 28
 (.branch 23
 (.leaf (.quota 2))
 (.branch 25
 (.leaf (.quota 2))
 (.branch 26
 (.leaf (.incidence 5))
 (.leaf (.quota 2)))))
 (.branch 33
 (.leaf (.quota 2))
 (.branch 35
 (.leaf (.quota 2))
 (.branch 36
 (.leaf (.quota 1))
 (.branch 37
 (.leaf (.matching Nonrational.OldTerminalMatches.M011.r0740))
 (.leaf (.matching Nonrational.OldTerminalMatches.M011.r0741))))))))
 (.branch 57
 (.branch 47
 (.branch 42
 (.branch 40
 (.branch 39
 (.leaf (.matching Nonrational.OldTerminalMatches.M011.r0742))
 (.leaf (.matching Nonrational.OldTerminalMatches.M011.r0743)))
 (.leaf (.quota 1)))
 (.branch 44
 (.branch 43
 (.leaf (.quota 1))
 (.leaf (.quota 2)))
 (.leaf (.quota 2))))
 (.branch 52
 (.branch 49
 (.branch 48
 (.leaf (.quota 1))
 (.leaf (.quota 2)))
 (.branch 50
 (.leaf (.quota 2))
 (.branch 51
 (.leaf (.quota 2))
 (.leaf (.quota 1)))))
 (.leaf (.quota 2))))
 (.branch 66
 (.leaf (.quota 2))
 (.branch 71
 (.leaf (.quota 2))
 (.branch 73
 (.leaf (.quota 2))
 (.branch 74
 (.leaf (.quota 2))
 (.branch 75
 (.leaf (.quota 2))
 (.leaf (.quota 1)))))))))
 (.branch 114
 (.branch 95
 (.branch 85
 (.branch 80
 (.branch 78
 (.leaf (.quota 2))
 (.branch 79
 (.leaf (.quota 2))
 (.leaf (.quota 1))))
 (.leaf (.quota 2)))
 (.branch 90
 (.leaf (.quota 2))
 (.branch 92
 (.branch 91
 (.leaf (.matching Nonrational.OldTerminalMatches.M011.r0744))
 (.leaf (.quota 1)))
 (.leaf (.quota 2)))))
 (.branch 104
 (.branch 99
 (.leaf (.quota 2))
 (.branch 101
 (.branch 100
 (.leaf (.quota 2))
 (.leaf (.quota 1)))
 (.leaf (.quota 2))))
 (.branch 109
 (.branch 106
 (.branch 105
 (.leaf (.quota 2))
 (.leaf (.quota 1)))
 (.branch 107
 (.leaf (.quota 1))
 (.leaf (.quota 2))))
 (.branch 111
 (.branch 110
 (.leaf (.quota 1))
 (.leaf (.quota 2)))
 (.branch 112
 (.leaf (.quota 2))
 (.branch 113
 (.leaf (.incidence 5))
 (.leaf (.quota 2))))))))
 (.branch 133
 (.branch 123
 (.branch 118
 (.leaf (.quota 2))
 (.branch 120
 (.branch 119
 (.leaf (.matching Nonrational.OldTerminalMatches.M011.r0745))
 (.leaf (.quota 1)))
 (.leaf (.quota 2))))
 (.branch 128
 (.branch 125
 (.leaf (.quota 2))
 (.branch 126
 (.leaf (.incidence 4))
 (.branch 127
 (.leaf (.incidence 4))
 (.leaf (.quota 2)))))
 (.leaf (.quota 2))))
 (.branch 142
 (.branch 137
 (.branch 135
 (.leaf (.quota 2))
 (.branch 136
 (.leaf (.quota 2))
 (.leaf .euler)))
 (.branch 139
 (.branch 138
 (.leaf .euler)
 (.leaf (.quota 2)))
 (.branch 140
 (.leaf (.quota 2))
 (.branch 141
 (.leaf (.quota 2))
 (.leaf .euler)))))
 (.branch 147
 (.branch 144
 (.branch 143
 (.leaf .euler)
 (.leaf (.matching Nonrational.OldTerminalMatches.M011.r0746)))
 (.leaf .euler))
 (.branch 149
 (.branch 148
 (.leaf (.matching Nonrational.OldTerminalMatches.M011.r0747))
 (.leaf (.matching Nonrational.OldTerminalMatches.M011.r0748)))
 (.branch 150
 (.leaf (.matching Nonrational.OldTerminalMatches.M011.r0749))
 (.branch 151
 (.leaf (.quota 2))
 (.leaf (.matching Nonrational.OldTerminalMatches.M011.r0750))))))))))
def disposition (j : Fin leafCount) := dispositionTable.get j.val
def dispositionTest (i : Nat) : Bool := RawLeafCertificate.check quota
  ((rawLeaves i).map Papers.RationalityTen.RootedCaches.RootedSixBase01.rawCells) (dispositionTable.get i)

end Papers.RationalityTen.RootedForests.RootedSubsumedForest0352
