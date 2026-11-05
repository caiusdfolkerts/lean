module
prelude
public import RootedSubsumedForest0301Data
public import RawLeafCertificate
public import OldTerminalMatches.M006

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0301
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness

def dispositionTable : Table RawLeafCertificate.Certificate :=
(.branch 60
 (.branch 30
 (.branch 15
 (.branch 7
 (.branch 3
 (.leaf (.quota 2))
 (.branch 5
 (.leaf (.quota 2))
 (.branch 6
 (.leaf (.quota 2))
 (.leaf (.quota 3)))))
 (.branch 11
 (.leaf (.quota 2))
 (.branch 13
 (.branch 12
 (.leaf (.quota 2))
 (.leaf (.matching Nonrational.OldTerminalMatches.M006.r0392)))
 (.branch 14
 (.leaf (.matching Nonrational.OldTerminalMatches.M006.r0393))
 (.leaf (.quota 2))))))
 (.branch 22
 (.branch 18
 (.branch 16
 (.leaf (.quota 2))
 (.branch 17
 (.leaf (.quota 2))
 (.leaf (.quota 3))))
 (.branch 20
 (.leaf (.quota 2))
 (.branch 21
 (.leaf (.quota 1))
 (.leaf (.quota 2)))))
 (.branch 26
 (.leaf (.quota 2))
 (.branch 28
 (.leaf (.quota 2))
 (.branch 29
 (.leaf (.matching Nonrational.OldTerminalMatches.M006.r0394))
 (.leaf (.quota 2)))))))
 (.branch 45
 (.branch 37
 (.branch 33
 (.branch 31
 (.leaf (.quota 2))
 (.branch 32
 (.leaf (.quota 3))
 (.leaf (.quota 1))))
 (.leaf (.quota 2)))
 (.branch 41
 (.branch 39
 (.branch 38
 (.leaf (.quota 2))
 (.leaf .euler))
 (.branch 40
 (.leaf .euler)
 (.leaf (.matching Nonrational.OldTerminalMatches.M006.r0395))))
 (.branch 43
 (.branch 42
 (.leaf (.matching Nonrational.OldTerminalMatches.M006.r0396))
 (.leaf (.quota 2)))
 (.leaf (.quota 2)))))
 (.branch 52
 (.branch 48
 (.leaf (.quota 2))
 (.branch 50
 (.leaf (.incidence 0))
 (.leaf (.quota 2))))
 (.branch 56
 (.branch 54
 (.branch 53
 (.leaf (.quota 2))
 (.leaf (.quota 1)))
 (.branch 55
 (.leaf (.quota 1))
 (.leaf (.quota 2))))
 (.leaf (.quota 2))))))
 (.branch 90
 (.branch 75
 (.branch 67
 (.branch 63
 (.branch 61
 (.leaf (.matching Nonrational.OldTerminalMatches.M006.r0397))
 (.leaf (.quota 2)))
 (.branch 65
 (.branch 64
 (.leaf (.matching Nonrational.OldTerminalMatches.M006.r0398))
 (.leaf (.matching Nonrational.OldTerminalMatches.M006.r0399)))
 (.branch 66
 (.leaf (.matching Nonrational.OldTerminalMatches.M006.r0400))
 (.leaf (.matching Nonrational.OldTerminalMatches.M006.r0401)))))
 (.branch 71
 (.leaf (.quota 2))
 (.branch 73
 (.leaf (.quota 2))
 (.branch 74
 (.leaf (.incidence 5))
 (.leaf (.incidence 0))))))
 (.branch 82
 (.branch 78
 (.branch 76
 (.leaf (.quota 2))
 (.branch 77
 (.leaf (.quota 2))
 (.leaf (.matching Nonrational.OldTerminalMatches.M006.r0402))))
 (.branch 80
 (.branch 79
 (.leaf (.matching Nonrational.OldTerminalMatches.M006.r0403))
 (.leaf (.quota 2)))
 (.leaf (.quota 2))))
 (.branch 86
 (.leaf (.quota 2))
 (.branch 88
 (.leaf (.quota 2))
 (.branch 89
 (.leaf (.quota 2))
 (.leaf (.quota 1)))))))
 (.branch 105
 (.branch 97
 (.branch 93
 (.branch 91
 (.leaf (.incidence 5))
 (.branch 92
 (.leaf (.incidence 5))
 (.leaf (.incidence 0))))
 (.branch 95
 (.branch 94
 (.leaf (.incidence 0))
 (.leaf (.incidence 6)))
 (.leaf (.quota 2))))
 (.branch 101
 (.branch 99
 (.leaf (.quota 2))
 (.branch 100
 (.leaf (.matching Nonrational.OldTerminalMatches.M006.r0404))
 (.leaf (.matching Nonrational.OldTerminalMatches.M006.r0405))))
 (.branch 103
 (.branch 102
 (.leaf (.quota 2))
 (.leaf (.incidence 0)))
 (.branch 104
 (.leaf (.incidence 0))
 (.leaf (.matching Nonrational.OldTerminalMatches.M006.r0406))))))
 (.branch 112
 (.branch 108
 (.branch 106
 (.leaf (.matching Nonrational.OldTerminalMatches.M006.r0407))
 (.branch 107
 (.leaf (.matching Nonrational.OldTerminalMatches.M006.r0408))
 (.leaf (.matching Nonrational.OldTerminalMatches.M006.r0409))))
 (.branch 110
 (.branch 109
 (.leaf (.incidence 4))
 (.leaf (.quota 2)))
 (.leaf (.quota 2))))
 (.branch 116
 (.branch 114
 (.branch 113
 (.leaf (.quota 2))
 (.leaf (.incidence 0)))
 (.branch 115
 (.leaf .euler)
 (.leaf (.incidence 9))))
 (.branch 118
 (.branch 117
 (.leaf (.incidence 0))
 (.leaf (.quota 2)))
 (.leaf (.incidence 0))))))))
def disposition (j : Fin leafCount) := dispositionTable.get j.val
def dispositionTest (i : Nat) : Bool := RawLeafCertificate.check quota
  ((rawLeaves i).map Papers.RationalityTen.RootedCaches.RootedSixBase01.rawCells) (dispositionTable.get i)

end Papers.RationalityTen.RootedForests.RootedSubsumedForest0301
