module
prelude
public meta import LowerSchemas.FiniteRootedSubsumedForest.Part0
public import RootedSubsumedForest0312Data
public import RawLeafCertificate
public import OldTerminalMatches.M007

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0312
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness

def dispositionTable : Table RawLeafCertificate.Certificate :=
(.branch 12
 (.branch 6
 (.branch 3
 (.leaf (.quota 3))
 (.branch 4
 (.leaf (.quota 3))
 (.branch 5
 (.leaf (.quota 1))
 (.leaf (.quota 2)))))
 (.branch 9
 (.leaf (.quota 2))
 (.branch 10
 (.leaf (.quota 2))
 (.branch 11
 (.leaf (.quota 2))
 (.leaf (.matching Nonrational.OldTerminalMatches.M007.r0486))))))
 (.branch 18
 (.branch 15
 (.branch 13
 (.leaf (.matching Nonrational.OldTerminalMatches.M007.r0487))
 (.branch 14
 (.leaf (.matching Nonrational.OldTerminalMatches.M007.r0488))
 (.leaf (.matching Nonrational.OldTerminalMatches.M007.r0489))))
 (.leaf (.quota 2)))
 (.branch 21
 (.branch 19
 (.leaf (.quota 2))
 (.branch 20
 (.leaf (.quota 2))
 (.leaf (.quota 1))))
 (.leaf (.quota 2)))))
cert_disposition_3
cert_dispositionTest_5 02
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
cert_disposition_at_8 10
cert_disposition_at_9 11 02 007 0486
cert_disposition_at_9 12 02 007 0487
cert_disposition_at_9 13 02 007 0488
cert_disposition_at_6 14 02 007 0489
cert_disposition_at_5 15
cert_disposition_at_5 16
cert_disposition_at_5 17
cert_disposition_at_5 18
cert_disposition_at_5 19
cert_disposition_at_5 20
cert_disposition_at_5 21
cert_disposition_at_5 22
cert_disposition_at_5 23
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
cert_disposition_interval_4 20 21
cert_disposition_interval_4 21 22
cert_disposition_interval_4 22 23
cert_disposition_interval_4 23 24
theorem dispositionTest_complete : Interval dispositionTest 0 leafCount := (interval_append dispositionTest 0 12 24 (interval_append dispositionTest 0 6 12 (interval_append dispositionTest 0 3 6 (interval_append dispositionTest 0 1 3 disposition_interval_0 (interval_append dispositionTest 1 2 3 disposition_interval_1 disposition_interval_2)) (interval_append dispositionTest 3 4 6 disposition_interval_3 (interval_append dispositionTest 4 5 6 disposition_interval_4 disposition_interval_5))) (interval_append dispositionTest 6 9 12 (interval_append dispositionTest 6 7 9 disposition_interval_6 (interval_append dispositionTest 7 8 9 disposition_interval_7 disposition_interval_8)) (interval_append dispositionTest 9 10 12 disposition_interval_9 (interval_append dispositionTest 10 11 12 disposition_interval_10 disposition_interval_11)))) (interval_append dispositionTest 12 18 24 (interval_append dispositionTest 12 15 18 (interval_append dispositionTest 12 13 15 disposition_interval_12 (interval_append dispositionTest 13 14 15 disposition_interval_13 disposition_interval_14)) (interval_append dispositionTest 15 16 18 disposition_interval_15 (interval_append dispositionTest 16 17 18 disposition_interval_16 disposition_interval_17))) (interval_append dispositionTest 18 21 24 (interval_append dispositionTest 18 19 21 disposition_interval_18 (interval_append dispositionTest 19 20 21 disposition_interval_19 disposition_interval_20)) (interval_append dispositionTest 21 22 24 disposition_interval_21 (interval_append dispositionTest 22 23 24 disposition_interval_22 disposition_interval_23)))))
cert_disposition_checked_5 02
end Papers.RationalityTen.RootedForests.RootedSubsumedForest0312
