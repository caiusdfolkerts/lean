module
prelude
public meta import LowerSchemas.FiniteRootedSubsumedForest.Part0
public import RootedSubsumedForest0357Data
public import RawLeafCertificate

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0357
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness

def dispositionTable : Table RawLeafCertificate.Certificate :=
(.branch 3
 (.leaf (.incidence 5))
 (.branch 5
 (.branch 4
 (.leaf (.incidence 5))
 (.leaf (.incidence 0)))
 (.leaf (.incidence 5))))
cert_disposition_3
cert_dispositionTest_5 02
cert_disposition_at_5 0
cert_disposition_at_5 1
cert_disposition_at_5 2
cert_disposition_at_5 3
cert_disposition_at_5 4
cert_disposition_at_5 5
cert_disposition_at_5 6
cert_disposition_interval_4 0 1
cert_disposition_interval_4 1 2
cert_disposition_interval_4 2 3
cert_disposition_interval_4 3 4
cert_disposition_interval_4 4 5
cert_disposition_interval_4 5 6
cert_disposition_interval_4 6 7
theorem dispositionTest_complete : Interval dispositionTest 0 leafCount := (interval_append dispositionTest 0 3 7 (interval_append dispositionTest 0 1 3 disposition_interval_0 (interval_append dispositionTest 1 2 3 disposition_interval_1 disposition_interval_2)) (interval_append dispositionTest 3 5 7 (interval_append dispositionTest 3 4 5 disposition_interval_3 disposition_interval_4) (interval_append dispositionTest 5 6 7 disposition_interval_5 disposition_interval_6)))
cert_disposition_checked_5 02
end Papers.RationalityTen.RootedForests.RootedSubsumedForest0357
