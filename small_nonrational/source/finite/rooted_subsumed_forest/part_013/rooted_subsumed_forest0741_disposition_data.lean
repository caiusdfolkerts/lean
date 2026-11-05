module
prelude
public import RootedSubsumedForest0741Data
public import RawLeafCertificate
public import OldTerminalMatches.M024
public import OldTerminalMatches.M025

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0741
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness

def dispositionTable : Table RawLeafCertificate.Certificate :=
(.branch 23
 (.branch 11
 (.branch 5
 (.branch 2
 (.branch 1
 (.leaf (.matching Nonrational.OldTerminalMatches.M024.r1599))
 (.leaf (.matching Nonrational.OldTerminalMatches.M025.r1600)))
 (.branch 3
 (.leaf (.quota 2))
 (.branch 4
 (.leaf (.matching Nonrational.OldTerminalMatches.M025.r1601))
 (.leaf (.quota 2)))))
 (.branch 8
 (.branch 6
 (.leaf (.matching Nonrational.OldTerminalMatches.M025.r1602))
 (.branch 7
 (.leaf (.quota 1))
 (.leaf (.matching Nonrational.OldTerminalMatches.M025.r1603))))
 (.branch 9
 (.leaf (.matching Nonrational.OldTerminalMatches.M025.r1604))
 (.branch 10
 (.leaf (.matching Nonrational.OldTerminalMatches.M025.r1605))
 (.leaf (.matching Nonrational.OldTerminalMatches.M025.r1606))))))
 (.branch 17
 (.leaf (.quota 2))
 (.branch 20
 (.branch 18
 (.leaf (.matching Nonrational.OldTerminalMatches.M025.r1607))
 (.leaf (.quota 2)))
 (.leaf (.quota 2)))))
 (.branch 35
 (.branch 29
 (.branch 26
 (.branch 24
 (.leaf (.matching Nonrational.OldTerminalMatches.M025.r1608))
 (.branch 25
 (.leaf (.matching Nonrational.OldTerminalMatches.M025.r1609))
 (.leaf (.matching Nonrational.OldTerminalMatches.M025.r1610))))
 (.branch 27
 (.leaf (.matching Nonrational.OldTerminalMatches.M025.r1611))
 (.branch 28
 (.leaf (.quota 2))
 (.leaf (.quota 3)))))
 (.branch 32
 (.branch 30
 (.leaf (.matching Nonrational.OldTerminalMatches.M025.r1612))
 (.branch 31
 (.leaf (.quota 1))
 (.leaf (.matching Nonrational.OldTerminalMatches.M025.r1613))))
 (.branch 33
 (.leaf (.matching Nonrational.OldTerminalMatches.M025.r1614))
 (.branch 34
 (.leaf (.matching Nonrational.OldTerminalMatches.M025.r1615))
 (.leaf (.matching Nonrational.OldTerminalMatches.M025.r1616))))))
 (.branch 41
 (.branch 38
 (.branch 36
 (.leaf (.matching Nonrational.OldTerminalMatches.M025.r1617))
 (.branch 37
 (.leaf (.matching Nonrational.OldTerminalMatches.M025.r1618))
 (.leaf (.quota 2))))
 (.branch 39
 (.leaf (.quota 1))
 (.leaf (.quota 2))))
 (.branch 44
 (.branch 42
 (.leaf (.quota 1))
 (.branch 43
 (.leaf (.matching Nonrational.OldTerminalMatches.M025.r1619))
 (.leaf (.matching Nonrational.OldTerminalMatches.M025.r1620))))
 (.branch 45
 (.leaf (.quota 2))
 (.branch 46
 (.leaf (.quota 1))
 (.leaf (.quota 2))))))))
def disposition (j : Fin leafCount) := dispositionTable.get j.val
def dispositionTest (i : Nat) : Bool := RawLeafCertificate.check quota
  ((rawLeaves i).map Papers.RationalityTen.RootedCaches.RootedSixBase04.rawCells) (dispositionTable.get i)

end Papers.RationalityTen.RootedForests.RootedSubsumedForest0741
