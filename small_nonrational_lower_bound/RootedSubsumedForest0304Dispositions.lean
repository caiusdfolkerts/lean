module
prelude
public meta import LowerSchemas.FiniteRootedSubsumedForest
public import RootedSubsumedForest0304Data
public import RawLeafCertificate
public import OldTerminalMatches.M006

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0304
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness

def dispositionTable : Table RawLeafCertificate.Certificate :=
(.branch 10
 (.branch 5
 (.branch 2
 (.leaf (.quota 8))
 (.branch 3
 (.leaf (.quota 8))
 (.branch 4
 (.leaf (.quota 3))
 (.leaf (.quota 8)))))
 (.leaf (.quota 8)))
 (.branch 15
 (.branch 12
 (.branch 11
 (.leaf (.quota 2))
 (.leaf (.quota 8)))
 (.branch 13
 (.leaf (.quota 2))
 (.branch 14
 (.leaf (.quota 8))
 (.leaf (.quota 2)))))
 (.branch 17
 (.leaf (.quota 8))
 (.branch 18
 (.leaf (.quota 8))
 (.branch 19
 (.leaf (.quota 2))
 (.leaf (.matching Nonrational.OldTerminalMatches.M006.r0443)))))))
cert_disposition_3
cert_dispositionTest_5 01
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
cert_disposition_at_8 18
cert_disposition_at_6 19 01 006 0443
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
cert_disposition_interval_4 18 19
cert_disposition_interval_4 19 20
theorem dispositionTest_complete : Interval dispositionTest 0 leafCount := (interval_append dispositionTest 0 10 20 (interval_append dispositionTest 0 5 10 (interval_append dispositionTest 0 2 5 (interval_append dispositionTest 0 1 2 disposition_interval_0 disposition_interval_1) (interval_append dispositionTest 2 3 5 disposition_interval_2 (interval_append dispositionTest 3 4 5 disposition_interval_3 disposition_interval_4))) (interval_append dispositionTest 5 7 10 (interval_append dispositionTest 5 6 7 disposition_interval_5 disposition_interval_6) (interval_append dispositionTest 7 8 10 disposition_interval_7 (interval_append dispositionTest 8 9 10 disposition_interval_8 disposition_interval_9)))) (interval_append dispositionTest 10 15 20 (interval_append dispositionTest 10 12 15 (interval_append dispositionTest 10 11 12 disposition_interval_10 disposition_interval_11) (interval_append dispositionTest 12 13 15 disposition_interval_12 (interval_append dispositionTest 13 14 15 disposition_interval_13 disposition_interval_14))) (interval_append dispositionTest 15 17 20 (interval_append dispositionTest 15 16 17 disposition_interval_15 disposition_interval_16) (interval_append dispositionTest 17 18 20 disposition_interval_17 (interval_append dispositionTest 18 19 20 disposition_interval_18 disposition_interval_19)))))
cert_disposition_checked_5 01
end Papers.RationalityTen.RootedForests.RootedSubsumedForest0304
