module
prelude
public meta import LowerSchemas.FiniteRootedSubsumedForest.Part0
public import RootedSubsumedForest0347Data
public import RawLeafCertificate
public import OldTerminalMatches.M011

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0347
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness

def dispositionTable : Table RawLeafCertificate.Certificate :=
(.branch 7
 (.branch 3
 (.branch 1
 (.leaf (.quota 2))
 (.branch 2
 (.leaf (.matching Nonrational.OldTerminalMatches.M011.r0720))
 (.leaf (.matching Nonrational.OldTerminalMatches.M011.r0721))))
 (.branch 5
 (.branch 4
 (.leaf (.matching Nonrational.OldTerminalMatches.M011.r0722))
 (.leaf (.incidence 5)))
 (.branch 6
 (.leaf (.matching Nonrational.OldTerminalMatches.M011.r0723))
 (.leaf (.quota 1)))))
 (.branch 11
 (.branch 9
 (.leaf (.quota 2))
 (.branch 10
 (.leaf (.matching Nonrational.OldTerminalMatches.M011.r0724))
 (.leaf (.incidence 0))))
 (.branch 13
 (.branch 12
 (.leaf (.incidence 0))
 (.leaf (.quota 2)))
 (.branch 14
 (.leaf (.incidence 0))
 (.leaf (.incidence 8))))))
cert_disposition_3
cert_dispositionTest_5 01
cert_disposition_at_8 0
cert_disposition_at_9 1 01 011 0720
cert_disposition_at_9 2 01 011 0721
cert_disposition_at_6 3 01 011 0722
cert_disposition_at_8 4
cert_disposition_at_6 5 01 011 0723
cert_disposition_at_5 6
cert_disposition_at_5 7
cert_disposition_at_8 8
cert_disposition_at_6 9 01 011 0724
cert_disposition_at_5 10
cert_disposition_at_5 11
cert_disposition_at_5 12
cert_disposition_at_5 13
cert_disposition_at_5 14
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
theorem dispositionTest_complete : Interval dispositionTest 0 leafCount := (interval_append dispositionTest 0 7 15 (interval_append dispositionTest 0 3 7 (interval_append dispositionTest 0 1 3 disposition_interval_0 (interval_append dispositionTest 1 2 3 disposition_interval_1 disposition_interval_2)) (interval_append dispositionTest 3 5 7 (interval_append dispositionTest 3 4 5 disposition_interval_3 disposition_interval_4) (interval_append dispositionTest 5 6 7 disposition_interval_5 disposition_interval_6))) (interval_append dispositionTest 7 11 15 (interval_append dispositionTest 7 9 11 (interval_append dispositionTest 7 8 9 disposition_interval_7 disposition_interval_8) (interval_append dispositionTest 9 10 11 disposition_interval_9 disposition_interval_10)) (interval_append dispositionTest 11 13 15 (interval_append dispositionTest 11 12 13 disposition_interval_11 disposition_interval_12) (interval_append dispositionTest 13 14 15 disposition_interval_13 disposition_interval_14))))
cert_disposition_checked_5 01
end Papers.RationalityTen.RootedForests.RootedSubsumedForest0347
