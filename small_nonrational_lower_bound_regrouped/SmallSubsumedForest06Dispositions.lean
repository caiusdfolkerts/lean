module
prelude
public meta import LowerSchemas.FiniteSmallSubsumedForest
public import SmallSubsumedForest06Data
public import RawLeafCertificate

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.SmallRawForests.SmallSubsumedForest06
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness

def dispositionTable : Table RawLeafCertificate.Certificate :=
(.branch 3
 (.branch 1
 (.leaf (.incidence 7))
 (.branch 2
 (.leaf (.incidence 6))
 (.leaf (.incidence 7))))
 (.branch 5
 (.branch 4
 (.leaf (.incidence 8))
 (.leaf (.incidence 4)))
 (.leaf (.incidence 4))))
cert_disposition_4
def dispositionTest (i : Nat) : Bool := RawLeafCertificate.check quota
  ((rawLeaves i).map RootedSmallCache.rawCells) (dispositionTable.get i)
cert_disposition_at_12 0
cert_disposition_at_12 1
cert_disposition_at_12 2
cert_disposition_at_12 3
cert_disposition_at_12 4
cert_disposition_at_12 5
cert_disposition_at_12 6
cert_disposition_interval_6 0 1
cert_disposition_interval_6 1 2
cert_disposition_interval_6 2 3
cert_disposition_interval_6 3 4
cert_disposition_interval_6 4 5
cert_disposition_interval_6 5 6
cert_disposition_interval_6 6 7
theorem dispositionTest_complete : Interval dispositionTest 0 leafCount := (interval_append dispositionTest 0 3 7 (interval_append dispositionTest 0 1 3 disposition_interval_0 (interval_append dispositionTest 1 2 3 disposition_interval_1 disposition_interval_2)) (interval_append dispositionTest 3 5 7 (interval_append dispositionTest 3 4 5 disposition_interval_3 disposition_interval_4) (interval_append dispositionTest 5 6 7 disposition_interval_5 disposition_interval_6)))
cert_disposition_checked_6
end Papers.RationalityTen.SmallRawForests.SmallSubsumedForest06
