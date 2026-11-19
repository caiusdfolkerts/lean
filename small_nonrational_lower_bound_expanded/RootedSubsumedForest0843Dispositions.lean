module
prelude
public meta import LowerSchemas.FiniteRootedSubsumedForest.Part0
public import RootedSubsumedForest0843Data
public import RawLeafCertificate

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0843
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness

def dispositionTable : Table RawLeafCertificate.Certificate :=
(.branch 9
 (.branch 4
 (.branch 2
 (.branch 1
 (.leaf (.quota 2))
 (.leaf (.quota 3)))
 (.branch 3
 (.leaf (.quota 1))
 (.leaf (.quota 2))))
 (.branch 6
 (.leaf (.quota 2))
 (.branch 7
 (.leaf (.incidence 9))
 (.branch 8
 (.leaf (.quota 1))
 (.leaf (.quota 2))))))
 (.branch 13
 (.branch 11
 (.leaf (.quota 2))
 (.branch 12
 (.leaf (.quota 2))
 (.leaf (.quota 1))))
 (.branch 15
 (.branch 14
 (.leaf (.incidence 3))
 (.leaf (.quota 2)))
 (.branch 16
 (.leaf (.quota 2))
 (.branch 17
 (.leaf (.quota 1))
 (.leaf (.quota 2)))))))
cert_disposition_3
cert_dispositionTest_4 05
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
cert_disposition_at_5 11
cert_disposition_at_5 12
cert_disposition_at_5 13
cert_disposition_at_5 14
cert_disposition_at_5 15
cert_disposition_at_5 16
cert_disposition_at_5 17
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
cert_disposition_interval_4 11 12
cert_disposition_interval_4 12 13
cert_disposition_interval_4 13 14
cert_disposition_interval_4 14 15
cert_disposition_interval_4 15 16
cert_disposition_interval_4 16 17
cert_disposition_interval_4 17 18
theorem dispositionTest_complete : Interval dispositionTest 0 leafCount := (interval_append dispositionTest 0 9 18 (interval_append dispositionTest 0 4 9 (interval_append dispositionTest 0 2 4 (interval_append dispositionTest 0 1 2 disposition_interval_0 disposition_interval_1) (interval_append dispositionTest 2 3 4 disposition_interval_2 disposition_interval_3)) (interval_append dispositionTest 4 6 9 (interval_append dispositionTest 4 5 6 disposition_interval_4 disposition_interval_5) (interval_append dispositionTest 6 7 9 disposition_interval_6 (interval_append dispositionTest 7 8 9 disposition_interval_7 disposition_interval_8)))) (interval_append dispositionTest 9 13 18 (interval_append dispositionTest 9 11 13 (interval_append dispositionTest 9 10 11 disposition_interval_9 disposition_interval_10) (interval_append dispositionTest 11 12 13 disposition_interval_11 disposition_interval_12)) (interval_append dispositionTest 13 15 18 (interval_append dispositionTest 13 14 15 disposition_interval_13 disposition_interval_14) (interval_append dispositionTest 15 16 18 disposition_interval_15 (interval_append dispositionTest 16 17 18 disposition_interval_16 disposition_interval_17)))))
cert_disposition_checked_4 05
end Papers.RationalityTen.RootedForests.RootedSubsumedForest0843
