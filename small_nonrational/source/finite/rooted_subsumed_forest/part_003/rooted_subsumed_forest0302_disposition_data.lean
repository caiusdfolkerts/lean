module
prelude
public import RootedSubsumedForest0302Data
public import RawLeafCertificate
public import OldTerminalMatches.M006

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0302
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness

def dispositionTable : Table RawLeafCertificate.Certificate :=
(.branch 66
 (.branch 33
 (.branch 16
 (.branch 8
 (.branch 4
 (.leaf (.quota 6))
 (.branch 6
 (.branch 5
 (.leaf (.quota 6))
 (.leaf (.quota 2)))
 (.leaf (.quota 6))))
 (.branch 12
 (.leaf (.quota 2))
 (.branch 14
 (.leaf (.quota 1))
 (.leaf (.quota 2)))))
 (.branch 24
 (.branch 20
 (.branch 18
 (.branch 17
 (.leaf (.quota 1))
 (.leaf (.quota 2)))
 (.leaf (.quota 2)))
 (.leaf (.quota 2)))
 (.branch 28
 (.branch 26
 (.leaf (.quota 2))
 (.leaf (.quota 6)))
 (.branch 30
 (.branch 29
 (.leaf (.quota 1))
 (.leaf (.quota 2)))
 (.branch 31
 (.leaf (.quota 2))
 (.branch 32
 (.leaf (.quota 6))
 (.leaf (.quota 2))))))))
 (.branch 49
 (.branch 41
 (.branch 37
 (.branch 35
 (.leaf (.quota 2))
 (.branch 36
 (.leaf (.quota 2))
 (.leaf (.quota 6))))
 (.branch 39
 (.branch 38
 (.leaf (.quota 6))
 (.leaf (.quota 2)))
 (.leaf (.quota 2))))
 (.branch 45
 (.branch 43
 (.branch 42
 (.leaf (.quota 1))
 (.leaf (.quota 2)))
 (.branch 44
 (.leaf (.quota 2))
 (.leaf (.quota 1))))
 (.branch 47
 (.branch 46
 (.leaf (.quota 6))
 (.leaf (.quota 2)))
 (.branch 48
 (.leaf (.quota 2))
 (.leaf (.quota 6))))))
 (.branch 57
 (.branch 53
 (.branch 51
 (.branch 50
 (.leaf (.quota 6))
 (.leaf (.quota 2)))
 (.leaf (.quota 2)))
 (.branch 55
 (.leaf (.quota 2))
 (.branch 56
 (.leaf (.matching Nonrational.OldTerminalMatches.M006.r0410))
 (.leaf (.matching Nonrational.OldTerminalMatches.M006.r0411)))))
 (.branch 61
 (.branch 59
 (.branch 58
 (.leaf (.matching Nonrational.OldTerminalMatches.M006.r0412))
 (.leaf (.quota 2)))
 (.branch 60
 (.leaf (.matching Nonrational.OldTerminalMatches.M006.r0413))
 (.leaf (.quota 2))))
 (.branch 63
 (.leaf (.quota 6))
 (.branch 64
 (.leaf (.matching Nonrational.OldTerminalMatches.M006.r0414))
 (.leaf (.quota 2))))))))
 (.branch 99
 (.branch 82
 (.branch 74
 (.branch 70
 (.branch 68
 (.branch 67
 (.leaf (.quota 1))
 (.leaf (.quota 6)))
 (.branch 69
 (.leaf (.quota 6))
 (.leaf (.quota 2))))
 (.leaf (.quota 2)))
 (.branch 78
 (.leaf (.quota 2))
 (.branch 80
 (.leaf (.quota 2))
 (.branch 81
 (.leaf (.quota 2))
 (.leaf (.matching Nonrational.OldTerminalMatches.M006.r0415))))))
 (.branch 90
 (.branch 86
 (.branch 84
 (.branch 83
 (.leaf (.matching Nonrational.OldTerminalMatches.M006.r0416))
 (.leaf (.quota 1)))
 (.leaf (.quota 2)))
 (.leaf (.quota 2)))
 (.leaf (.quota 2))))
 (.branch 116
 (.branch 107
 (.leaf (.quota 2))
 (.branch 111
 (.leaf (.quota 2))
 (.branch 113
 (.branch 112
 (.leaf (.quota 2))
 (.leaf (.matching Nonrational.OldTerminalMatches.M006.r0417)))
 (.branch 114
 (.leaf (.matching Nonrational.OldTerminalMatches.M006.r0418))
 (.branch 115
 (.leaf (.quota 2))
 (.leaf (.matching Nonrational.OldTerminalMatches.M006.r0419)))))))
 (.branch 124
 (.branch 120
 (.branch 118
 (.branch 117
 (.leaf (.matching Nonrational.OldTerminalMatches.M006.r0420))
 (.leaf (.matching Nonrational.OldTerminalMatches.M006.r0421)))
 (.leaf (.quota 2)))
 (.branch 122
 (.branch 121
 (.leaf (.quota 2))
 (.leaf (.matching Nonrational.OldTerminalMatches.M006.r0422)))
 (.branch 123
 (.leaf (.matching Nonrational.OldTerminalMatches.M006.r0423))
 (.leaf (.quota 2)))))
 (.branch 128
 (.branch 126
 (.branch 125
 (.leaf (.matching Nonrational.OldTerminalMatches.M006.r0424))
 (.leaf (.quota 2)))
 (.leaf (.quota 2)))
 (.branch 130
 (.branch 129
 (.leaf (.matching Nonrational.OldTerminalMatches.M006.r0425))
 (.leaf (.quota 2)))
 (.branch 131
 (.leaf (.quota 2))
 (.branch 132
 (.leaf (.matching Nonrational.OldTerminalMatches.M006.r0426))
 (.leaf (.matching Nonrational.OldTerminalMatches.M006.r0427))))))))))
def disposition (j : Fin leafCount) := dispositionTable.get j.val
def dispositionTest (i : Nat) : Bool := RawLeafCertificate.check quota
  ((rawLeaves i).map Papers.RationalityTen.RootedCaches.RootedSixBase01.rawCells) (dispositionTable.get i)

end Papers.RationalityTen.RootedForests.RootedSubsumedForest0302
