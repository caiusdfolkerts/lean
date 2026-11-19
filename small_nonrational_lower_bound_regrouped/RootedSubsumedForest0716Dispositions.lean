module
prelude
public meta import LowerSchemas.FiniteRootedSubsumedForest.Part0
public import RootedSubsumedForest0716Data
public import RawLeafCertificate
public import OldTerminalMatches.M019
public import OldTerminalMatches.M020

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0716
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness

def dispositionTable : Table RawLeafCertificate.Certificate :=
(.branch 15
 (.branch 7
 (.branch 3
 (.branch 1
 (.leaf (.quota 2))
 (.branch 2
 (.leaf (.quota 2))
 (.leaf (.matching Nonrational.OldTerminalMatches.M019.r1274))))
 (.branch 5
 (.branch 4
 (.leaf (.matching Nonrational.OldTerminalMatches.M019.r1275))
 (.leaf (.incidence 4)))
 (.branch 6
 (.leaf (.quota 1))
 (.leaf (.incidence 8)))))
 (.branch 11
 (.branch 9
 (.branch 8
 (.leaf (.incidence 4))
 (.leaf (.matching Nonrational.OldTerminalMatches.M019.r1276)))
 (.branch 10
 (.leaf (.matching Nonrational.OldTerminalMatches.M019.r1277))
 (.leaf (.quota 2))))
 (.leaf (.quota 2))))
 (.branch 22
 (.branch 18
 (.branch 16
 (.leaf (.quota 2))
 (.branch 17
 (.leaf (.quota 2))
 (.leaf (.matching Nonrational.OldTerminalMatches.M019.r1278))))
 (.branch 20
 (.branch 19
 (.leaf (.matching Nonrational.OldTerminalMatches.M019.r1279))
 (.leaf (.quota 2)))
 (.branch 21
 (.leaf (.matching Nonrational.OldTerminalMatches.M020.r1280))
 (.leaf (.quota 1)))))
 (.branch 26
 (.branch 24
 (.branch 23
 (.leaf (.incidence 4))
 (.leaf (.matching Nonrational.OldTerminalMatches.M020.r1281)))
 (.branch 25
 (.leaf (.quota 1))
 (.leaf (.matching Nonrational.OldTerminalMatches.M020.r1282))))
 (.leaf (.quota 2)))))
cert_disposition_3
cert_dispositionTest_5 03
cert_disposition_at_5 0
cert_disposition_at_8 1
cert_disposition_at_9 2 03 019 1274
cert_disposition_at_6 3 03 019 1275
cert_disposition_at_5 4
cert_disposition_at_5 5
cert_disposition_at_5 6
cert_disposition_at_8 7
cert_disposition_at_9 8 03 019 1276
cert_disposition_at_6 9 03 019 1277
cert_disposition_at_5 10
cert_disposition_at_5 11
cert_disposition_at_5 12
cert_disposition_at_5 13
cert_disposition_at_5 14
cert_disposition_at_5 15
cert_disposition_at_8 16
cert_disposition_at_9 17 03 019 1278
cert_disposition_at_6 18 03 019 1279
cert_disposition_at_8 19
cert_disposition_at_6 20 03 020 1280
cert_disposition_at_5 21
cert_disposition_at_8 22
cert_disposition_at_6 23 03 020 1281
cert_disposition_at_8 24
cert_disposition_at_6 25 03 020 1282
cert_disposition_at_5 26
cert_disposition_at_5 27
cert_disposition_at_5 28
cert_disposition_at_5 29
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
cert_disposition_interval_4 29 30
theorem dispositionTest_complete : Interval dispositionTest 0 leafCount := (interval_append dispositionTest 0 15 30 (interval_append dispositionTest 0 7 15 (interval_append dispositionTest 0 3 7 (interval_append dispositionTest 0 1 3 disposition_interval_0 (interval_append dispositionTest 1 2 3 disposition_interval_1 disposition_interval_2)) (interval_append dispositionTest 3 5 7 (interval_append dispositionTest 3 4 5 disposition_interval_3 disposition_interval_4) (interval_append dispositionTest 5 6 7 disposition_interval_5 disposition_interval_6))) (interval_append dispositionTest 7 11 15 (interval_append dispositionTest 7 9 11 (interval_append dispositionTest 7 8 9 disposition_interval_7 disposition_interval_8) (interval_append dispositionTest 9 10 11 disposition_interval_9 disposition_interval_10)) (interval_append dispositionTest 11 13 15 (interval_append dispositionTest 11 12 13 disposition_interval_11 disposition_interval_12) (interval_append dispositionTest 13 14 15 disposition_interval_13 disposition_interval_14)))) (interval_append dispositionTest 15 22 30 (interval_append dispositionTest 15 18 22 (interval_append dispositionTest 15 16 18 disposition_interval_15 (interval_append dispositionTest 16 17 18 disposition_interval_16 disposition_interval_17)) (interval_append dispositionTest 18 20 22 (interval_append dispositionTest 18 19 20 disposition_interval_18 disposition_interval_19) (interval_append dispositionTest 20 21 22 disposition_interval_20 disposition_interval_21))) (interval_append dispositionTest 22 26 30 (interval_append dispositionTest 22 24 26 (interval_append dispositionTest 22 23 24 disposition_interval_22 disposition_interval_23) (interval_append dispositionTest 24 25 26 disposition_interval_24 disposition_interval_25)) (interval_append dispositionTest 26 28 30 (interval_append dispositionTest 26 27 28 disposition_interval_26 disposition_interval_27) (interval_append dispositionTest 28 29 30 disposition_interval_28 disposition_interval_29)))))
cert_disposition_checked_5 03
end Papers.RationalityTen.RootedForests.RootedSubsumedForest0716
