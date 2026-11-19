module
prelude
public meta import LowerSchemas.FiniteRootedSubsumedForest.Part0
public import RootedSubsumedForest0247Data
public import RawLeafCertificate
public import OldTerminalMatches.M005

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0247
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness

def dispositionTable : Table RawLeafCertificate.Certificate :=
(.branch 6
 (.branch 3
 (.branch 1
 (.leaf (.incidence 5))
 (.branch 2
 (.leaf (.incidence 5))
 (.leaf (.quota 2))))
 (.branch 4
 (.leaf (.quota 2))
 (.branch 5
 (.leaf (.matching Nonrational.OldTerminalMatches.M005.r0337))
 (.leaf (.matching Nonrational.OldTerminalMatches.M005.r0338)))))
 (.branch 9
 (.branch 7
 (.leaf (.incidence 8))
 (.branch 8
 (.leaf (.quota 1))
 (.leaf (.matching Nonrational.OldTerminalMatches.M005.r0339))))
 (.branch 11
 (.branch 10
 (.leaf (.matching Nonrational.OldTerminalMatches.M005.r0340))
 (.leaf (.incidence 0)))
 (.leaf (.quota 2)))))
cert_disposition_3
cert_dispositionTest_5 02
cert_disposition_at_5 0
cert_disposition_at_5 1
cert_disposition_at_5 2
cert_disposition_at_8 3
cert_disposition_at_9 4 02 005 0337
cert_disposition_at_6 5 02 005 0338
cert_disposition_at_5 6
cert_disposition_at_8 7
cert_disposition_at_9 8 02 005 0339
cert_disposition_at_6 9 02 005 0340
cert_disposition_at_5 10
cert_disposition_at_5 11
cert_disposition_at_5 12
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
theorem dispositionTest_complete : Interval dispositionTest 0 leafCount := (interval_append dispositionTest 0 6 13 (interval_append dispositionTest 0 3 6 (interval_append dispositionTest 0 1 3 disposition_interval_0 (interval_append dispositionTest 1 2 3 disposition_interval_1 disposition_interval_2)) (interval_append dispositionTest 3 4 6 disposition_interval_3 (interval_append dispositionTest 4 5 6 disposition_interval_4 disposition_interval_5))) (interval_append dispositionTest 6 9 13 (interval_append dispositionTest 6 7 9 disposition_interval_6 (interval_append dispositionTest 7 8 9 disposition_interval_7 disposition_interval_8)) (interval_append dispositionTest 9 11 13 (interval_append dispositionTest 9 10 11 disposition_interval_9 disposition_interval_10) (interval_append dispositionTest 11 12 13 disposition_interval_11 disposition_interval_12))))
cert_disposition_checked_5 02
end Papers.RationalityTen.RootedForests.RootedSubsumedForest0247
