module
prelude
public meta import LowerSchemas.FiniteRootedSubsumedForest
public import RootedSubsumedForest0310Data
public import RawLeafCertificate
public import OldTerminalMatches.M007

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0310
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness

def dispositionTable : Table RawLeafCertificate.Certificate :=
(.branch 9
 (.branch 4
 (.branch 2
 (.leaf (.quota 2))
 (.branch 3
 (.leaf (.quota 2))
 (.leaf (.matching Nonrational.OldTerminalMatches.M007.r0462))))
 (.branch 6
 (.leaf (.quota 2))
 (.branch 7
 (.leaf (.matching Nonrational.OldTerminalMatches.M007.r0463))
 (.branch 8
 (.leaf (.matching Nonrational.OldTerminalMatches.M007.r0464))
 (.leaf (.matching Nonrational.OldTerminalMatches.M007.r0465))))))
 (.branch 13
 (.branch 11
 (.branch 10
 (.leaf (.quota 2))
 (.leaf (.matching Nonrational.OldTerminalMatches.M007.r0466)))
 (.branch 12
 (.leaf (.matching Nonrational.OldTerminalMatches.M007.r0467))
 (.leaf (.matching Nonrational.OldTerminalMatches.M007.r0468))))
 (.branch 15
 (.branch 14
 (.leaf (.matching Nonrational.OldTerminalMatches.M007.r0469))
 (.leaf (.incidence 5)))
 (.branch 16
 (.leaf (.incidence 5))
 (.leaf (.quota 2))))))
cert_disposition_3
cert_dispositionTest_5 00
cert_disposition_at_5 0
cert_disposition_at_5 1
cert_disposition_at_8 2
cert_disposition_at_6 3 00 007 0462
cert_disposition_at_5 4
cert_disposition_at_8 5
cert_disposition_at_9 6 00 007 0463
cert_disposition_at_9 7 00 007 0464
cert_disposition_at_6 8 00 007 0465
cert_disposition_at_8 9
cert_disposition_at_9 10 00 007 0466
cert_disposition_at_9 11 00 007 0467
cert_disposition_at_9 12 00 007 0468
cert_disposition_at_6 13 00 007 0469
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
cert_disposition_checked_5 00
end Papers.RationalityTen.RootedForests.RootedSubsumedForest0310
