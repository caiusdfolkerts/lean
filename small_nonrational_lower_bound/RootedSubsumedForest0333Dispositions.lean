module
prelude
public meta import LowerSchemas.FiniteRootedSubsumedForest
public import RootedSubsumedForest0333Data
public import RawLeafCertificate

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0333
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness

def dispositionTable : Table RawLeafCertificate.Certificate :=
(.branch 5
 (.branch 2
 (.leaf (.quota 2))
 (.branch 3
 (.leaf (.incidence 0))
 (.branch 4
 (.leaf (.incidence 5))
 (.leaf (.quota 2)))))
 (.branch 8
 (.branch 6
 (.leaf (.quota 2))
 (.branch 7
 (.leaf (.incidence 0))
 (.leaf (.incidence 5))))
 (.branch 9
 (.leaf (.incidence 0))
 (.branch 10
 (.leaf (.incidence 0))
 (.leaf (.incidence 5))))))
cert_disposition_3
cert_dispositionTest_5 00
cert_disposition_at_5 0
cert_disposition_at_5 1
cert_disposition_at_5 2
cert_disposition_at_5 3
cert_disposition_at_5 4
cert_disposition_at_5 5
cert_disposition_at_5 6
cert_disposition_at_5 7
cert_disposition_at_5 8
cert_disposition_at_5 9
cert_disposition_at_5 10
cert_disposition_interval_4 0 1
cert_disposition_interval_4 1 2
cert_disposition_interval_4 2 3
cert_disposition_interval_4 3 4
cert_disposition_interval_4 4 5
cert_disposition_interval_4 5 6
cert_disposition_interval_4 6 7
cert_disposition_interval_4 7 8
cert_disposition_interval_4 8 9
cert_disposition_interval_4 9 10
cert_disposition_interval_4 10 11
theorem dispositionTest_complete : Interval dispositionTest 0 leafCount := (interval_append dispositionTest 0 5 11 (interval_append dispositionTest 0 2 5 (interval_append dispositionTest 0 1 2 disposition_interval_0 disposition_interval_1) (interval_append dispositionTest 2 3 5 disposition_interval_2 (interval_append dispositionTest 3 4 5 disposition_interval_3 disposition_interval_4))) (interval_append dispositionTest 5 8 11 (interval_append dispositionTest 5 6 8 disposition_interval_5 (interval_append dispositionTest 6 7 8 disposition_interval_6 disposition_interval_7)) (interval_append dispositionTest 8 9 11 disposition_interval_8 (interval_append dispositionTest 9 10 11 disposition_interval_9 disposition_interval_10))))
cert_disposition_checked_5 00
end Papers.RationalityTen.RootedForests.RootedSubsumedForest0333
