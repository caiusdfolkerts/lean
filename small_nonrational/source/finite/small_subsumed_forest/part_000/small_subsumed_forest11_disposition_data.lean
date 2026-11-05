module
prelude
public import SmallSubsumedForest11Data
public import RawLeafCertificate

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.SmallRawForests.SmallSubsumedForest11
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness

def dispositionTable : Table RawLeafCertificate.Certificate :=
(.branch 19
 (.branch 9
 (.branch 4
 (.leaf (.incidence 3))
 (.branch 6
 (.leaf (.incidence 8))
 (.branch 7
 (.leaf (.incidence 8))
 (.branch 8
 (.leaf (.incidence 4))
 (.leaf (.incidence 3))))))
 (.branch 14
 (.branch 11
 (.branch 10
 (.leaf (.incidence 3))
 (.leaf (.incidence 8)))
 (.branch 12
 (.leaf (.incidence 8))
 (.leaf (.incidence 4))))
 (.branch 16
 (.branch 15
 (.leaf (.incidence 7))
 (.leaf (.incidence 9)))
 (.branch 17
 (.leaf (.incidence 5))
 (.branch 18
 (.leaf (.incidence 5))
 (.leaf (.incidence 8)))))))
 (.branch 29
 (.branch 24
 (.branch 21
 (.branch 20
 (.leaf (.incidence 5))
 (.leaf (.quota 1)))
 (.branch 22
 (.leaf (.incidence 5))
 (.branch 23
 (.leaf (.quota 1))
 (.leaf (.incidence 5)))))
 (.branch 26
 (.branch 25
 (.leaf (.incidence 9))
 (.leaf (.incidence 5)))
 (.branch 27
 (.leaf (.incidence 9))
 (.branch 28
 (.leaf (.incidence 5))
 (.leaf (.incidence 9))))))
 (.branch 34
 (.branch 31
 (.branch 30
 (.leaf (.incidence 5))
 (.leaf (.quota 1)))
 (.branch 32
 (.leaf (.quota 1))
 (.branch 33
 (.leaf (.incidence 3))
 (.leaf (.quota 1)))))
 (.branch 36
 (.branch 35
 (.leaf (.incidence 4))
 (.leaf (.quota 1)))
 (.branch 37
 (.leaf (.incidence 9))
 (.branch 38
 (.leaf (.quota 1))
 (.leaf (.incidence 4))))))))
def disposition (j : Fin leafCount) := dispositionTable.get j.val
def dispositionTest (i : Nat) : Bool := RawLeafCertificate.check quota
  ((rawLeaves i).map RootedSmallCache.rawCells) (dispositionTable.get i)

end Papers.RationalityTen.SmallRawForests.SmallSubsumedForest11
