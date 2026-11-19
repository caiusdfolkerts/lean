module
prelude
public meta import LowerSchemas.FiniteRootedSubsumedForest
public import RootedSubsumedForest0279Data
public import RawLeafCertificate
public import OldTerminalMatches.M005

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0279
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness

def dispositionTable : Table RawLeafCertificate.Certificate :=
(.branch 8
 (.branch 4
 (.branch 2
 (.branch 1
 (.leaf (.quota 6))
 (.leaf (.quota 2)))
 (.branch 3
 (.leaf (.quota 6))
 (.leaf (.quota 2))))
 (.branch 6
 (.branch 5
 (.leaf (.quota 2))
 (.leaf (.matching Nonrational.OldTerminalMatches.M005.r0346)))
 (.leaf (.quota 2))))
 (.branch 12
 (.branch 10
 (.branch 9
 (.leaf (.quota 2))
 (.leaf (.matching Nonrational.OldTerminalMatches.M005.r0347)))
 (.leaf (.quota 2)))
 (.branch 14
 (.branch 13
 (.leaf (.matching Nonrational.OldTerminalMatches.M005.r0348))
 (.leaf (.matching Nonrational.OldTerminalMatches.M005.r0349)))
 (.branch 15
 (.leaf (.matching Nonrational.OldTerminalMatches.M005.r0350))
 (.leaf (.matching Nonrational.OldTerminalMatches.M005.r0351))))))
cert_disposition_3
cert_dispositionTest_5 01
cert_disposition_at_5 0
cert_disposition_at_5 1
cert_disposition_at_5 2
cert_disposition_at_5 3
cert_disposition_at_8 4
cert_disposition_at_6 5 01 005 0346
cert_disposition_at_5 6
cert_disposition_at_5 7
cert_disposition_at_8 8
cert_disposition_at_6 9 01 005 0347
cert_disposition_at_5 10
cert_disposition_at_8 11
cert_disposition_at_9 12 01 005 0348
cert_disposition_at_9 13 01 005 0349
cert_disposition_at_9 14 01 005 0350
cert_disposition_at_6 15 01 005 0351
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
theorem dispositionTest_complete : Interval dispositionTest 0 leafCount := (interval_append dispositionTest 0 8 16 (interval_append dispositionTest 0 4 8 (interval_append dispositionTest 0 2 4 (interval_append dispositionTest 0 1 2 disposition_interval_0 disposition_interval_1) (interval_append dispositionTest 2 3 4 disposition_interval_2 disposition_interval_3)) (interval_append dispositionTest 4 6 8 (interval_append dispositionTest 4 5 6 disposition_interval_4 disposition_interval_5) (interval_append dispositionTest 6 7 8 disposition_interval_6 disposition_interval_7))) (interval_append dispositionTest 8 12 16 (interval_append dispositionTest 8 10 12 (interval_append dispositionTest 8 9 10 disposition_interval_8 disposition_interval_9) (interval_append dispositionTest 10 11 12 disposition_interval_10 disposition_interval_11)) (interval_append dispositionTest 12 14 16 (interval_append dispositionTest 12 13 14 disposition_interval_12 disposition_interval_13) (interval_append dispositionTest 14 15 16 disposition_interval_14 disposition_interval_15))))
cert_disposition_checked_5 01
end Papers.RationalityTen.RootedForests.RootedSubsumedForest0279
