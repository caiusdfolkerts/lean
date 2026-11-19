module
prelude
public meta import LowerSchemas.FiniteRootedRawForest
public import RootedRawForest0091Data
public import RawLeafCertificate

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedRawForest0091
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness

def dispositionTable : Table RawLeafCertificate.Certificate :=
(.branch 6
 (.branch 3
 (.branch 1
 (.leaf (.incidence 0))
 (.branch 2
 (.leaf (.incidence 3))
 (.leaf (.incidence 0))))
 (.branch 4
 (.leaf (.incidence 3))
 (.branch 5
 (.leaf (.incidence 0))
 (.leaf (.incidence 3)))))
 (.branch 9
 (.branch 7
 (.leaf (.incidence 3))
 (.branch 8
 (.leaf (.incidence 0))
 (.leaf (.incidence 3))))
 (.branch 10
 (.leaf (.incidence 0))
 (.branch 11
 (.leaf (.incidence 3))
 (.leaf (.incidence 0))))))
cert_disposition_2
cert_dispositionTest_2 057
cert_disposition_at_2 0
cert_disposition_at_2 1
cert_disposition_at_2 2
cert_disposition_at_2 3
cert_disposition_at_2 4
cert_disposition_at_2 5
cert_disposition_at_2 6
cert_disposition_at_2 7
cert_disposition_at_2 8
cert_disposition_at_2 9
cert_disposition_at_2 10
cert_disposition_at_2 11
cert_disposition_interval_2 0 1
cert_disposition_interval_2 1 2
cert_disposition_interval_2 2 3
cert_disposition_interval_2 3 4
cert_disposition_interval_2 4 5
cert_disposition_interval_2 5 6
cert_disposition_interval_2 6 7
cert_disposition_interval_2 7 8
cert_disposition_interval_2 8 9
cert_disposition_interval_2 9 10
cert_disposition_interval_2 10 11
cert_disposition_interval_2 11 12
theorem dispositionTest_complete : Interval dispositionTest 0 leafCount := (interval_append dispositionTest 0 6 12 (interval_append dispositionTest 0 3 6 (interval_append dispositionTest 0 1 3 disposition_interval_0 (interval_append dispositionTest 1 2 3 disposition_interval_1 disposition_interval_2)) (interval_append dispositionTest 3 4 6 disposition_interval_3 (interval_append dispositionTest 4 5 6 disposition_interval_4 disposition_interval_5))) (interval_append dispositionTest 6 9 12 (interval_append dispositionTest 6 7 9 disposition_interval_6 (interval_append dispositionTest 7 8 9 disposition_interval_7 disposition_interval_8)) (interval_append dispositionTest 9 10 12 disposition_interval_9 (interval_append dispositionTest 10 11 12 disposition_interval_10 disposition_interval_11))))
cert_disposition_checked_2 057
end Papers.RationalityTen.RootedForests.RootedRawForest0091
