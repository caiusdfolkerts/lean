module
prelude
public meta import LowerSchemas.FiniteRootedRawForest
public import RootedRawForest0063Data
public import RawLeafCertificate

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedRawForest0063
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness

def dispositionTable : Table RawLeafCertificate.Certificate :=
(.branch 9
 (.branch 4
 (.branch 2
 (.leaf (.incidence 1))
 (.branch 3
 (.leaf (.incidence 0))
 (.leaf (.incidence 2))))
 (.branch 6
 (.branch 5
 (.leaf (.incidence 0))
 (.leaf (.incidence 2)))
 (.branch 7
 (.leaf (.incidence 2))
 (.branch 8
 (.leaf (.incidence 0))
 (.leaf (.incidence 1))))))
 (.branch 13
 (.branch 11
 (.branch 10
 (.leaf (.incidence 1))
 (.leaf (.incidence 0)))
 (.leaf (.incidence 2)))
 (.branch 15
 (.branch 14
 (.leaf (.incidence 0))
 (.leaf (.incidence 2)))
 (.branch 16
 (.leaf (.incidence 0))
 (.leaf (.incidence 1))))))
cert_disposition_2
cert_dispositionTest_2 029
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
cert_disposition_at_2 12
cert_disposition_at_2 13
cert_disposition_at_2 14
cert_disposition_at_2 15
cert_disposition_at_2 16
cert_disposition_at_2 17
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
cert_disposition_interval_2 12 13
cert_disposition_interval_2 13 14
cert_disposition_interval_2 14 15
cert_disposition_interval_2 15 16
cert_disposition_interval_2 16 17
cert_disposition_interval_2 17 18
theorem dispositionTest_complete : Interval dispositionTest 0 leafCount := (interval_append dispositionTest 0 9 18 (interval_append dispositionTest 0 4 9 (interval_append dispositionTest 0 2 4 (interval_append dispositionTest 0 1 2 disposition_interval_0 disposition_interval_1) (interval_append dispositionTest 2 3 4 disposition_interval_2 disposition_interval_3)) (interval_append dispositionTest 4 6 9 (interval_append dispositionTest 4 5 6 disposition_interval_4 disposition_interval_5) (interval_append dispositionTest 6 7 9 disposition_interval_6 (interval_append dispositionTest 7 8 9 disposition_interval_7 disposition_interval_8)))) (interval_append dispositionTest 9 13 18 (interval_append dispositionTest 9 11 13 (interval_append dispositionTest 9 10 11 disposition_interval_9 disposition_interval_10) (interval_append dispositionTest 11 12 13 disposition_interval_11 disposition_interval_12)) (interval_append dispositionTest 13 15 18 (interval_append dispositionTest 13 14 15 disposition_interval_13 disposition_interval_14) (interval_append dispositionTest 15 16 18 disposition_interval_15 (interval_append dispositionTest 16 17 18 disposition_interval_16 disposition_interval_17)))))
cert_disposition_checked_2 029
end Papers.RationalityTen.RootedForests.RootedRawForest0063
