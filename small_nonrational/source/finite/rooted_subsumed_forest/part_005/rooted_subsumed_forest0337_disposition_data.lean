module
prelude
public import RootedSubsumedForest0337Data
public import RawLeafCertificate
public import OldTerminalMatches.M007
public import OldTerminalMatches.M008

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0337
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness

def dispositionTable : Table RawLeafCertificate.Certificate :=
(.branch 72
 (.branch 36
 (.branch 18
 (.branch 9
 (.branch 4
 (.branch 2
 (.leaf (.quota 2))
 (.branch 3
 (.leaf (.matching Nonrational.OldTerminalMatches.M007.r0506))
 (.leaf (.quota 2))))
 (.leaf (.quota 2)))
 (.branch 13
 (.branch 11
 (.branch 10
 (.leaf (.matching Nonrational.OldTerminalMatches.M007.r0507))
 (.leaf (.quota 2)))
 (.branch 12
 (.leaf (.matching Nonrational.OldTerminalMatches.M007.r0508))
 (.leaf (.quota 2))))
 (.leaf (.quota 2))))
 (.branch 27
 (.branch 22
 (.branch 20
 (.leaf (.quota 2))
 (.branch 21
 (.leaf (.incidence 5))
 (.leaf (.quota 2))))
 (.leaf (.quota 2)))
 (.branch 31
 (.leaf (.quota 2))
 (.branch 33
 (.branch 32
 (.leaf (.incidence 0))
 (.leaf (.quota 2)))
 (.branch 34
 (.leaf (.quota 2))
 (.branch 35
 (.leaf (.matching Nonrational.OldTerminalMatches.M007.r0509))
 (.leaf (.quota 2))))))))
 (.branch 54
 (.branch 45
 (.branch 40
 (.branch 38
 (.leaf (.quota 2))
 (.branch 39
 (.leaf (.quota 2))
 (.leaf (.quota 1))))
 (.leaf (.quota 2)))
 (.leaf (.quota 2)))
 (.branch 63
 (.branch 58
 (.branch 56
 (.branch 55
 (.leaf (.matching Nonrational.OldTerminalMatches.M007.r0510))
 (.leaf (.quota 2)))
 (.branch 57
 (.leaf (.matching Nonrational.OldTerminalMatches.M007.r0511))
 (.leaf (.quota 2))))
 (.branch 60
 (.leaf (.quota 2))
 (.branch 61
 (.leaf (.quota 2))
 (.branch 62
 (.leaf (.matching Nonrational.OldTerminalMatches.M008.r0512))
 (.leaf (.quota 2))))))
 (.branch 67
 (.branch 65
 (.branch 64
 (.leaf (.matching Nonrational.OldTerminalMatches.M008.r0513))
 (.leaf (.matching Nonrational.OldTerminalMatches.M008.r0514)))
 (.branch 66
 (.leaf (.matching Nonrational.OldTerminalMatches.M008.r0515))
 (.leaf (.matching Nonrational.OldTerminalMatches.M008.r0516))))
 (.leaf (.quota 2))))))
 (.branch 108
 (.branch 90
 (.branch 81
 (.branch 76
 (.leaf (.quota 2))
 (.branch 78
 (.leaf (.quota 2))
 (.branch 79
 (.leaf (.quota 1))
 (.leaf (.quota 2)))))
 (.branch 85
 (.leaf (.quota 2))
 (.branch 87
 (.branch 86
 (.leaf (.quota 2))
 (.leaf (.matching Nonrational.OldTerminalMatches.M008.r0517)))
 (.leaf (.quota 2)))))
 (.branch 99
 (.branch 94
 (.leaf (.quota 2))
 (.branch 96
 (.branch 95
 (.leaf (.matching Nonrational.OldTerminalMatches.M008.r0518))
 (.leaf (.matching Nonrational.OldTerminalMatches.M008.r0519)))
 (.branch 97
 (.leaf (.matching Nonrational.OldTerminalMatches.M008.r0520))
 (.branch 98
 (.leaf (.quota 2))
 (.leaf (.matching Nonrational.OldTerminalMatches.M008.r0521))))))
 (.branch 103
 (.branch 101
 (.branch 100
 (.leaf (.matching Nonrational.OldTerminalMatches.M008.r0522))
 (.leaf (.quota 2)))
 (.leaf (.quota 2)))
 (.leaf (.quota 2)))))
 (.branch 126
 (.branch 117
 (.branch 112
 (.branch 110
 (.branch 109
 (.leaf (.quota 2))
 (.leaf (.matching Nonrational.OldTerminalMatches.M008.r0523)))
 (.branch 111
 (.leaf (.matching Nonrational.OldTerminalMatches.M008.r0524))
 (.leaf (.matching Nonrational.OldTerminalMatches.M008.r0525))))
 (.branch 114
 (.leaf (.quota 2))
 (.branch 115
 (.leaf (.quota 2))
 (.branch 116
 (.leaf .euler)
 (.leaf (.quota 2))))))
 (.branch 121
 (.branch 119
 (.branch 118
 (.leaf (.quota 2))
 (.leaf (.matching Nonrational.OldTerminalMatches.M008.r0526)))
 (.branch 120
 (.leaf (.matching Nonrational.OldTerminalMatches.M008.r0527))
 (.leaf (.matching Nonrational.OldTerminalMatches.M008.r0528))))
 (.branch 123
 (.branch 122
 (.leaf (.matching Nonrational.OldTerminalMatches.M008.r0529))
 (.leaf (.matching Nonrational.OldTerminalMatches.M008.r0530)))
 (.leaf (.quota 2)))))
 (.branch 135
 (.branch 130
 (.branch 128
 (.branch 127
 (.leaf (.matching Nonrational.OldTerminalMatches.M008.r0531))
 (.leaf (.matching Nonrational.OldTerminalMatches.M008.r0532)))
 (.branch 129
 (.leaf (.matching Nonrational.OldTerminalMatches.M008.r0533))
 (.leaf (.matching Nonrational.OldTerminalMatches.M008.r0534))))
 (.branch 132
 (.leaf (.quota 2))
 (.branch 133
 (.leaf (.quota 1))
 (.branch 134
 (.leaf (.quota 1))
 (.leaf (.quota 2))))))
 (.branch 140
 (.branch 137
 (.branch 136
 (.leaf (.incidence 5))
 (.leaf (.quota 2)))
 (.branch 138
 (.leaf (.quota 2))
 (.branch 139
 (.leaf (.quota 1))
 (.leaf (.matching Nonrational.OldTerminalMatches.M008.r0535)))))
 (.branch 142
 (.branch 141
 (.leaf (.matching Nonrational.OldTerminalMatches.M008.r0536))
 (.leaf (.matching Nonrational.OldTerminalMatches.M008.r0537)))
 (.branch 143
 (.leaf (.quota 2))
 (.branch 144
 (.leaf (.matching Nonrational.OldTerminalMatches.M008.r0538))
 (.leaf (.quota 2))))))))))
def disposition (j : Fin leafCount) := dispositionTable.get j.val
def dispositionTest (i : Nat) : Bool := RawLeafCertificate.check quota
  ((rawLeaves i).map Papers.RationalityTen.RootedCaches.RootedSixBase00.rawCells) (dispositionTable.get i)

end Papers.RationalityTen.RootedForests.RootedSubsumedForest0337
