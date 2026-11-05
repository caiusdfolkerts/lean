module
prelude
public import RootedSubsumedForest0303Data
public import RawLeafCertificate
public import OldTerminalMatches.M006

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0303
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness

def dispositionTable : Table RawLeafCertificate.Certificate :=
(.branch 52
 (.branch 26
 (.branch 13
 (.branch 6
 (.branch 3
 (.branch 1
 (.leaf (.quota 2))
 (.branch 2
 (.leaf (.quota 2))
 (.leaf (.quota 3))))
 (.branch 4
 (.leaf (.quota 2))
 (.branch 5
 (.leaf (.matching Nonrational.OldTerminalMatches.M006.r0428))
 (.leaf (.matching Nonrational.OldTerminalMatches.M006.r0429)))))
 (.branch 9
 (.branch 7
 (.leaf (.quota 2))
 (.branch 8
 (.leaf (.quota 1))
 (.leaf (.quota 2))))
 (.leaf (.quota 2))))
 (.branch 19
 (.branch 16
 (.leaf (.quota 2))
 (.branch 17
 (.leaf (.quota 3))
 (.leaf (.quota 2))))
 (.leaf (.quota 2))))
 (.branch 39
 (.branch 32
 (.leaf (.quota 2))
 (.branch 35
 (.branch 33
 (.leaf (.quota 2))
 (.leaf (.quota 1)))
 (.branch 37
 (.leaf (.quota 2))
 (.branch 38
 (.leaf (.quota 2))
 (.leaf (.quota 3))))))
 (.branch 45
 (.branch 42
 (.leaf (.quota 2))
 (.branch 43
 (.leaf (.quota 2))
 (.branch 44
 (.leaf (.quota 1))
 (.leaf (.quota 2)))))
 (.branch 48
 (.branch 46
 (.leaf (.quota 1))
 (.leaf (.quota 2)))
 (.branch 50
 (.branch 49
 (.leaf (.quota 1))
 (.leaf (.quota 2)))
 (.leaf (.quota 2)))))))
 (.branch 78
 (.branch 65
 (.branch 58
 (.branch 55
 (.branch 53
 (.leaf (.quota 2))
 (.branch 54
 (.leaf (.quota 2))
 (.leaf (.matching Nonrational.OldTerminalMatches.M006.r0430))))
 (.branch 56
 (.leaf (.quota 1))
 (.branch 57
 (.leaf (.matching Nonrational.OldTerminalMatches.M006.r0431))
 (.leaf (.quota 2)))))
 (.leaf (.quota 2)))
 (.branch 71
 (.branch 68
 (.leaf (.quota 2))
 (.branch 69
 (.leaf (.matching Nonrational.OldTerminalMatches.M006.r0432))
 (.branch 70
 (.leaf (.matching Nonrational.OldTerminalMatches.M006.r0433))
 (.leaf (.quota 2)))))
 (.branch 74
 (.branch 72
 (.leaf (.matching Nonrational.OldTerminalMatches.M006.r0434))
 (.branch 73
 (.leaf (.matching Nonrational.OldTerminalMatches.M006.r0435))
 (.leaf (.quota 1))))
 (.branch 76
 (.branch 75
 (.leaf (.quota 1))
 (.leaf (.quota 2)))
 (.leaf (.quota 2))))))
 (.branch 91
 (.branch 84
 (.branch 81
 (.branch 79
 (.leaf (.quota 3))
 (.leaf (.quota 2)))
 (.branch 82
 (.leaf (.quota 1))
 (.branch 83
 (.leaf (.matching Nonrational.OldTerminalMatches.M006.r0436))
 (.leaf (.quota 2)))))
 (.branch 87
 (.branch 85
 (.leaf (.quota 2))
 (.branch 86
 (.leaf (.matching Nonrational.OldTerminalMatches.M006.r0437))
 (.leaf (.quota 2))))
 (.leaf (.quota 2))))
 (.branch 98
 (.branch 94
 (.leaf (.quota 2))
 (.branch 96
 (.leaf (.quota 2))
 (.branch 97
 (.leaf (.matching Nonrational.OldTerminalMatches.M006.r0438))
 (.leaf (.matching Nonrational.OldTerminalMatches.M006.r0439)))))
 (.branch 101
 (.branch 99
 (.leaf (.matching Nonrational.OldTerminalMatches.M006.r0440))
 (.branch 100
 (.leaf (.matching Nonrational.OldTerminalMatches.M006.r0441))
 (.leaf (.matching Nonrational.OldTerminalMatches.M006.r0442))))
 (.leaf (.quota 2)))))))
def disposition (j : Fin leafCount) := dispositionTable.get j.val
def dispositionTest (i : Nat) : Bool := RawLeafCertificate.check quota
  ((rawLeaves i).map Papers.RationalityTen.RootedCaches.RootedSixBase01.rawCells) (dispositionTable.get i)

end Papers.RationalityTen.RootedForests.RootedSubsumedForest0303
