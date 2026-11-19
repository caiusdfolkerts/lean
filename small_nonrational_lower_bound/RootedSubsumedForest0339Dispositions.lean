module
prelude
public meta import LowerSchemas.FiniteRootedSubsumedForest
public import RootedSubsumedForest0339Data
public import RawLeafCertificate
public import OldTerminalMatches.M011

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0339
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness

def dispositionTable : Table RawLeafCertificate.Certificate :=
(.branch 14
 (.branch 7
 (.branch 3
 (.leaf (.quota 2))
 (.branch 5
 (.branch 4
 (.leaf (.quota 2))
 (.leaf (.quota 3)))
 (.branch 6
 (.leaf (.quota 2))
 (.leaf (.quota 3)))))
 (.branch 10
 (.branch 8
 (.leaf (.matching Nonrational.OldTerminalMatches.M011.r0712))
 (.branch 9
 (.leaf (.quota 3))
 (.leaf (.quota 2))))
 (.branch 12
 (.leaf (.quota 2))
 (.branch 13
 (.leaf (.matching Nonrational.OldTerminalMatches.M011.r0713))
 (.leaf (.matching Nonrational.OldTerminalMatches.M011.r0714))))))
 (.branch 21
 (.branch 17
 (.branch 15
 (.leaf (.quota 2))
 (.branch 16
 (.leaf (.quota 2))
 (.leaf (.matching Nonrational.OldTerminalMatches.M011.r0715))))
 (.leaf (.quota 2)))
 (.branch 25
 (.branch 23
 (.branch 22
 (.leaf (.quota 2))
 (.leaf (.matching Nonrational.OldTerminalMatches.M011.r0716)))
 (.branch 24
 (.leaf (.matching Nonrational.OldTerminalMatches.M011.r0717))
 (.leaf (.matching Nonrational.OldTerminalMatches.M011.r0718))))
 (.branch 27
 (.branch 26
 (.leaf (.matching Nonrational.OldTerminalMatches.M011.r0719))
 (.leaf (.quota 2)))
 (.leaf (.quota 2))))))
cert_disposition_3
cert_dispositionTest_5 00
cert_disposition_at_5 0
cert_disposition_at_5 1
cert_disposition_at_5 2
cert_disposition_at_5 3
cert_disposition_at_5 4
cert_disposition_at_5 5
cert_disposition_at_8 6
cert_disposition_at_6 7 00 011 0712
cert_disposition_at_5 8
cert_disposition_at_5 9
cert_disposition_at_5 10
cert_disposition_at_8 11
cert_disposition_at_9 12 00 011 0713
cert_disposition_at_6 13 00 011 0714
cert_disposition_at_5 14
cert_disposition_at_8 15
cert_disposition_at_6 16 00 011 0715
cert_disposition_at_5 17
cert_disposition_at_5 18
cert_disposition_at_5 19
cert_disposition_at_5 20
cert_disposition_at_8 21
cert_disposition_at_9 22 00 011 0716
cert_disposition_at_9 23 00 011 0717
cert_disposition_at_9 24 00 011 0718
cert_disposition_at_6 25 00 011 0719
cert_disposition_at_5 26
cert_disposition_at_5 27
cert_disposition_at_5 28
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
cert_disposition_interval_4 24 25
cert_disposition_interval_4 25 26
cert_disposition_interval_4 26 27
cert_disposition_interval_4 27 28
cert_disposition_interval_4 28 29
theorem dispositionTest_complete : Interval dispositionTest 0 leafCount := (interval_append dispositionTest 0 14 29 (interval_append dispositionTest 0 7 14 (interval_append dispositionTest 0 3 7 (interval_append dispositionTest 0 1 3 disposition_interval_0 (interval_append dispositionTest 1 2 3 disposition_interval_1 disposition_interval_2)) (interval_append dispositionTest 3 5 7 (interval_append dispositionTest 3 4 5 disposition_interval_3 disposition_interval_4) (interval_append dispositionTest 5 6 7 disposition_interval_5 disposition_interval_6))) (interval_append dispositionTest 7 10 14 (interval_append dispositionTest 7 8 10 disposition_interval_7 (interval_append dispositionTest 8 9 10 disposition_interval_8 disposition_interval_9)) (interval_append dispositionTest 10 12 14 (interval_append dispositionTest 10 11 12 disposition_interval_10 disposition_interval_11) (interval_append dispositionTest 12 13 14 disposition_interval_12 disposition_interval_13)))) (interval_append dispositionTest 14 21 29 (interval_append dispositionTest 14 17 21 (interval_append dispositionTest 14 15 17 disposition_interval_14 (interval_append dispositionTest 15 16 17 disposition_interval_15 disposition_interval_16)) (interval_append dispositionTest 17 19 21 (interval_append dispositionTest 17 18 19 disposition_interval_17 disposition_interval_18) (interval_append dispositionTest 19 20 21 disposition_interval_19 disposition_interval_20))) (interval_append dispositionTest 21 25 29 (interval_append dispositionTest 21 23 25 (interval_append dispositionTest 21 22 23 disposition_interval_21 disposition_interval_22) (interval_append dispositionTest 23 24 25 disposition_interval_23 disposition_interval_24)) (interval_append dispositionTest 25 27 29 (interval_append dispositionTest 25 26 27 disposition_interval_25 disposition_interval_26) (interval_append dispositionTest 27 28 29 disposition_interval_27 disposition_interval_28)))))
cert_disposition_checked_5 00
end Papers.RationalityTen.RootedForests.RootedSubsumedForest0339
