module
prelude
public meta import LowerSchemas.FiniteRootedSubsumedForest.Part0
public import RootedSubsumedForest0700Data
public import RawLeafCertificate
public import OldTerminalMatches.M019

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0700
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness

def dispositionTable : Table RawLeafCertificate.Certificate :=
(.branch 7
 (.branch 3
 (.branch 1
 (.leaf (.quota 2))
 (.leaf (.quota 3)))
 (.branch 5
 (.leaf (.quota 2))
 (.branch 6
 (.leaf (.quota 3))
 (.leaf (.quota 2)))))
 (.branch 10
 (.branch 8
 (.leaf (.quota 2))
 (.branch 9
 (.leaf (.incidence 4))
 (.leaf (.quota 2))))
 (.branch 12
 (.leaf (.quota 1))
 (.branch 13
 (.leaf (.matching Nonrational.OldTerminalMatches.M019.r1227))
 (.leaf (.quota 2))))))
cert_disposition_3
cert_dispositionTest_5 03
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
cert_disposition_at_8 11
cert_disposition_at_6 12 03 019 1227
cert_disposition_at_5 13
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
theorem dispositionTest_complete : Interval dispositionTest 0 leafCount := (interval_append dispositionTest 0 7 14 (interval_append dispositionTest 0 3 7 (interval_append dispositionTest 0 1 3 disposition_interval_0 (interval_append dispositionTest 1 2 3 disposition_interval_1 disposition_interval_2)) (interval_append dispositionTest 3 5 7 (interval_append dispositionTest 3 4 5 disposition_interval_3 disposition_interval_4) (interval_append dispositionTest 5 6 7 disposition_interval_5 disposition_interval_6))) (interval_append dispositionTest 7 10 14 (interval_append dispositionTest 7 8 10 disposition_interval_7 (interval_append dispositionTest 8 9 10 disposition_interval_8 disposition_interval_9)) (interval_append dispositionTest 10 12 14 (interval_append dispositionTest 10 11 12 disposition_interval_10 disposition_interval_11) (interval_append dispositionTest 12 13 14 disposition_interval_12 disposition_interval_13))))
cert_disposition_checked_5 03
end Papers.RationalityTen.RootedForests.RootedSubsumedForest0700
