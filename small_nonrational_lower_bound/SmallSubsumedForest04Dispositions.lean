module
prelude
public meta import LowerSchemas.FiniteSmallSubsumedForest
public import SmallSubsumedForest04Data
public import RawLeafCertificate

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.SmallRawForests.SmallSubsumedForest04
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness

def dispositionTable : Table RawLeafCertificate.Certificate :=
(.branch 2
 (.branch 1
 (.leaf (.incidence 5))
 (.leaf (.incidence 3)))
 (.branch 3
 (.leaf (.incidence 3))
 (.leaf (.quota 2))))
cert_disposition_4
def dispositionTest (i : Nat) : Bool := RawLeafCertificate.check quota
  ((rawLeaves i).map RootedSmallCache.rawCells) (dispositionTable.get i)
cert_disposition_at_12 0
cert_disposition_at_12 1
cert_disposition_at_12 2
cert_disposition_at_12 3
cert_disposition_interval_6 0 1
cert_disposition_interval_6 1 2
cert_disposition_interval_6 2 3
cert_disposition_interval_6 3 4
theorem dispositionTest_complete : Interval dispositionTest 0 leafCount := (interval_append dispositionTest 0 2 4 (interval_append dispositionTest 0 1 2 disposition_interval_0 disposition_interval_1) (interval_append dispositionTest 2 3 4 disposition_interval_2 disposition_interval_3))
cert_disposition_checked_6
end Papers.RationalityTen.SmallRawForests.SmallSubsumedForest04
