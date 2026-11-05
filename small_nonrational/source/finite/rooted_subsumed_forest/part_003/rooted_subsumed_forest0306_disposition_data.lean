module
prelude
public import RootedSubsumedForest0306Data
public import RawLeafCertificate
public import OldTerminalMatches.M007

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0306
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness

def dispositionTable : Table RawLeafCertificate.Certificate :=
(.branch 59
 (.branch 29
 (.branch 14
 (.branch 7
 (.branch 3
 (.branch 1
 (.leaf (.quota 2))
 (.branch 2
 (.leaf (.quota 2))
 (.leaf (.matching Nonrational.OldTerminalMatches.M007.r0448))))
 (.branch 5
 (.branch 4
 (.leaf (.matching Nonrational.OldTerminalMatches.M007.r0449))
 (.leaf (.quota 2)))
 (.leaf (.quota 2))))
 (.leaf (.quota 2)))
 (.branch 21
 (.branch 17
 (.leaf (.quota 2))
 (.branch 19
 (.leaf (.quota 2))
 (.branch 20
 (.leaf (.quota 2))
 (.leaf (.quota 1)))))
 (.branch 25
 (.branch 23
 (.branch 22
 (.leaf (.quota 1))
 (.leaf (.quota 2)))
 (.leaf (.quota 2)))
 (.leaf (.quota 2)))))
 (.branch 44
 (.branch 36
 (.leaf (.quota 2))
 (.branch 40
 (.branch 38
 (.leaf (.quota 2))
 (.branch 39
 (.leaf (.quota 2))
 (.leaf (.quota 1))))
 (.leaf (.quota 2))))
 (.branch 51
 (.branch 47
 (.branch 45
 (.leaf (.quota 2))
 (.branch 46
 (.leaf (.quota 1))
 (.leaf (.quota 2))))
 (.branch 49
 (.branch 48
 (.leaf (.quota 2))
 (.leaf (.quota 3)))
 (.leaf (.quota 2))))
 (.branch 55
 (.branch 53
 (.branch 52
 (.leaf (.quota 3))
 (.leaf (.quota 2)))
 (.branch 54
 (.leaf (.quota 2))
 (.leaf (.quota 3))))
 (.branch 57
 (.branch 56
 (.leaf (.quota 1))
 (.leaf (.quota 2)))
 (.leaf (.quota 2)))))))
 (.branch 89
 (.branch 74
 (.branch 66
 (.branch 62
 (.branch 60
 (.leaf (.quota 2))
 (.branch 61
 (.leaf (.quota 1))
 (.leaf (.quota 2))))
 (.branch 64
 (.branch 63
 (.leaf (.quota 2))
 (.leaf (.quota 1)))
 (.leaf (.quota 2))))
 (.branch 70
 (.leaf (.quota 2))
 (.branch 72
 (.branch 71
 (.leaf (.quota 1))
 (.leaf (.quota 2)))
 (.branch 73
 (.leaf (.matching Nonrational.OldTerminalMatches.M007.r0450))
 (.leaf (.quota 3))))))
 (.branch 81
 (.branch 77
 (.leaf (.quota 2))
 (.branch 79
 (.branch 78
 (.leaf (.quota 1))
 (.leaf (.quota 2)))
 (.leaf (.quota 1))))
 (.branch 85
 (.branch 83
 (.branch 82
 (.leaf (.quota 1))
 (.leaf (.matching Nonrational.OldTerminalMatches.M007.r0451)))
 (.branch 84
 (.leaf (.matching Nonrational.OldTerminalMatches.M007.r0452))
 (.leaf (.matching Nonrational.OldTerminalMatches.M007.r0453))))
 (.branch 87
 (.branch 86
 (.leaf (.matching Nonrational.OldTerminalMatches.M007.r0454))
 (.leaf (.quota 2)))
 (.leaf (.quota 2))))))
 (.branch 104
 (.branch 96
 (.branch 92
 (.leaf (.quota 2))
 (.branch 94
 (.leaf (.quota 1))
 (.leaf (.quota 2))))
 (.branch 100
 (.leaf (.quota 2))
 (.branch 102
 (.branch 101
 (.leaf (.matching Nonrational.OldTerminalMatches.M007.r0455))
 (.leaf (.quota 2)))
 (.branch 103
 (.leaf (.quota 2))
 (.leaf (.matching Nonrational.OldTerminalMatches.M007.r0456))))))
 (.branch 111
 (.branch 107
 (.branch 105
 (.leaf (.quota 2))
 (.branch 106
 (.leaf (.matching Nonrational.OldTerminalMatches.M007.r0457))
 (.leaf (.quota 2))))
 (.branch 109
 (.leaf (.quota 2))
 (.branch 110
 (.leaf (.quota 2))
 (.leaf (.quota 1)))))
 (.branch 115
 (.branch 113
 (.leaf (.quota 1))
 (.leaf (.quota 2)))
 (.leaf (.quota 2)))))))
def disposition (j : Fin leafCount) := dispositionTable.get j.val
def dispositionTest (i : Nat) : Bool := RawLeafCertificate.check quota
  ((rawLeaves i).map Papers.RationalityTen.RootedCaches.RootedSixBase02.rawCells) (dispositionTable.get i)

end Papers.RationalityTen.RootedForests.RootedSubsumedForest0306
